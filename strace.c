/*
 * Copyright (c) 1991, 1992 Paul Kranenburg <pk@cs.few.eur.nl>
 * Copyright (c) 1993 Branko Lankester <branko@hacktic.nl>
 * Copyright (c) 1993, 1994, 1995, 1996 Rick Sladkey <jrs@world.std.com>
 * Copyright (c) 1996-1999 Wichert Akkerman <wichert@cistron.nl>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "defs.h"
#include <stdarg.h>
#include <sys/param.h>
#include <fcntl.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <pwd.h>
#include <grp.h>
#include <dirent.h>
#include <sys/utsname.h>
#ifdef HAVE_PRCTL
# include <sys/prctl.h>
#endif
#if defined(IA64)
# include <asm/ptrace_offsets.h>
#endif
/* In some libc, these aren't declared. Do it ourself: */
extern char **environ;
extern int optind;
extern char *optarg;

#ifdef USE_LIBUNWIND
/* if this is true do the stack trace for every system call */
bool stack_trace_enabled = false;
#endif

#if defined __NR_tkill
# define my_tkill(tid, sig) syscall(__NR_tkill, (tid), (sig))
#else
   /* kill() may choose arbitrarily the target task of the process group
      while we later wait on a that specific TID.  PID process waits become
      TID task specific waits for a process under ptrace(2).  */
# warning "tkill(2) not available, risk of strace hangs!"
# define my_tkill(tid, sig) kill((tid), (sig))
#endif

/* Glue for systems without a MMU that cannot provide fork() */
#if !defined(HAVE_FORK)
# undef NOMMU_SYSTEM
# define NOMMU_SYSTEM 1
#endif
#if NOMMU_SYSTEM
# define fork() vfork()
#endif

cflag_t cflag = CFLAG_NONE;//Флаг того, какие дополнительные логи нужно собирать
unsigned int followfork = 0;
unsigned int ptrace_setoptions = 0; //Опции, с которыми будет вызываться ptrace
unsigned int xflag = 0;
bool need_fork_exec_workarounds = 0;//Требуются обходные пути из-за того что ядро не поддерживает какие-то из нужных нам опций ptrace
bool debug_flag = 0;
bool Tflag = 0;
bool iflag = 0;//Нужно печатать pc
bool count_wallclock = 0;
unsigned int qflag = 0;//Флаг того, что не нужно выводить сообщения о присоединении/отсоединении процессов
/* Which WSTOPSIG(status) value marks syscall traps? */
static unsigned int syscall_trap_sig = SIGTRAP;
static unsigned int tflag = 0;//Флаг формата таймстампов
static bool rflag = 0;
static bool print_pid_pfx = 0;

/* -I n */
//Используется для opt_intr
enum {
    INTR_NOT_SET        = 0,
    INTR_ANYWHERE       = 1, /* don't block/ignore any signals */
    INTR_WHILE_WAIT     = 2, /* block fatal signals while decoding syscall. default */
    INTR_NEVER          = 3, /* block fatal signals. default if '-o FILE PROG' */
    INTR_BLOCK_TSTP_TOO = 4, /* block fatal signals and SIGTSTP (^Z) */
    NUM_INTR_OPTS
};
static int opt_intr; //Значение опции -I -- она отвечает за блокироваку сигналов
/* We play with signal mask only if this mode is active: */
#define interactive (opt_intr == INTR_WHILE_WAIT)

/*
 * daemonized_tracer supports -D option.
 * With this option, strace forks twice.
 * Unlike normal case, with -D *grandparent* process exec's,
 * becoming a traced process. Child exits (this prevents traced process
 * from having children it doesn't expect to have), and grandchild
 * attaches to grandparent similarly to strace -p PID.
 * This allows for more transparent interaction in cases
 * when process and its parent are communicating via signals,
 * wait() etc. Without -D, strace process gets lodged in between,
 * disrupting parent<->child link.
 */
static bool daemonized_tracer = 0;

#if USE_SEIZE
static int post_attach_sigstop = TCB_IGNORE_ONE_SIGSTOP;
# define use_seize (post_attach_sigstop == 0)
#else
# define post_attach_sigstop TCB_IGNORE_ONE_SIGSTOP
# define use_seize 0
#endif

/* Sometimes we want to print only succeeding syscalls. */
bool not_failing_only = 0;

/* Show path associated with fd arguments */
unsigned int show_fd_path = 0;

static bool detach_on_execve = 0;
/* Are we "strace PROG" and need to skip detach on first execve? */
static bool skip_one_b_execve = 0; //Флаг того, что strace вызван как strace PROG  и мы должны скрыть отсоединение при первом вызове execve
/* Are we "strace PROG" and need to hide everything until execve? */
bool hide_log_until_execve = 0;

static int exit_code = 0;
static int strace_child = 0;
//Pid процесса strace
static int strace_tracer_pid = 0;

static char *username = NULL;
static uid_t run_uid;
static gid_t run_gid;

unsigned int max_strlen = DEFAULT_STRLEN;
static int acolumn = DEFAULT_ACOLUMN;
static char *acolumn_spaces;

static char *outfname = NULL;
/* If -ff, points to stderr. Else, it's our common output log */
static FILE *shared_log;

struct tcb *printing_tcp = NULL;
static struct tcb *current_tcp;

static struct tcb **tcbtab;
static unsigned int nprocs, tcbtabsize;
static const char *progname;

unsigned os_release; /* Версия операционной системы*/

static void detach(struct tcb *tcp);
static void cleanup(void);
static void interrupt(int sig);
static sigset_t empty_set, blocked_set;

#ifdef HAVE_SIG_ATOMIC_T
static volatile sig_atomic_t interrupted;
#else
static volatile int interrupted;
#endif

#ifndef HAVE_STRERROR

#if !HAVE_DECL_SYS_ERRLIST
extern int sys_nerr;
extern char *sys_errlist[];
#endif

const char *
strerror(int err_no)
{
	static char buf[sizeof("Unknown error %d") + sizeof(int)*3];

	if (err_no < 1 || err_no >= sys_nerr) {
		sprintf(buf, "Unknown error %d", err_no);
		return buf;
	}
	return sys_errlist[err_no];
}

#endif /* HAVE_STERRROR */

static void
usage(FILE *ofp, int exitval)
{
	fprintf(ofp, "\
usage: strace [-CdffhiqrtttTvVxxy] [-I n] [-e expr]...\n\
              [-a column] [-o file] [-s strsize] [-P path]...\n\
              -p pid... / [-D] [-E var=val]... [-u username] PROG [ARGS]\n\
   or: strace -c[df] [-I n] [-e expr]... [-O overhead] [-S sortby]\n\
              -p pid... / [-D] [-E var=val]... [-u username] PROG [ARGS]\n\
-c -- count time, calls, and errors for each syscall and report summary\n\
-C -- like -c but also print regular output\n\
-w -- summarise syscall latency (default is system time)\n\
-d -- enable debug output to stderr\n\
-D -- run tracer process as a detached grandchild, not as parent\n\
-f -- follow forks, -ff -- with output into separate files\n\
-i -- print instruction pointer at time of syscall\n\
-q -- suppress messages about attaching, detaching, etc.\n\
-r -- print relative timestamp, -t -- absolute timestamp, -tt -- with usecs\n\
-T -- print time spent in each syscall\n\
-v -- verbose mode: print unabbreviated argv, stat, termios, etc. args\n\
-x -- print non-ascii strings in hex, -xx -- print all strings in hex\n\
-y -- print paths associated with file descriptor arguments\n\
-h -- print help message, -V -- print version\n\
-a column -- alignment COLUMN for printing syscall results (default %d)\n\
-b execve -- detach on this syscall\n\
-e expr -- a qualifying expression: option=[!]all or option=[!]val1[,val2]...\n\
   options: trace, abbrev, verbose, raw, signal, read, write\n\
-I interruptible --\n\
   1: no signals are blocked\n\
   2: fatal signals are blocked while decoding syscall (default)\n\
   3: fatal signals are always blocked (default if '-o FILE PROG')\n\
   4: fatal signals and SIGTSTP (^Z) are always blocked\n\
      (useful to make 'strace -o FILE PROG' not stop on ^Z)\n\
-o file -- send trace output to FILE instead of stderr\n\
-O overhead -- set overhead for tracing syscalls to OVERHEAD usecs\n\
-p pid -- trace process with process id PID, may be repeated\n\
-s strsize -- limit length of print strings to STRSIZE chars (default %d)\n\
-S sortby -- sort syscall counts by: time, calls, name, nothing (default %s)\n\
-u username -- run command as username handling setuid and/or setgid\n\
-E var=val -- put var=val in the environment for command\n\
-E var -- remove var from the environment for command\n\
-P path -- trace accesses to path\n\
"
#ifdef USE_LIBUNWIND
"-k obtain stack trace between each syscall (experimental)\n\
"
#endif
/* ancient, no one should use it
-F -- attempt to follow vforks (deprecated, use -f)\n\
 */
/* this is broken, so don't document it
-z -- print only succeeding syscalls\n\
 */
, DEFAULT_ACOLUMN, DEFAULT_STRLEN, DEFAULT_SORTBY);
	exit(exitval);
}
//Завершение работы
static void die(void) __attribute__ ((noreturn));
static void die(void)
{
	if (strace_tracer_pid == getpid()) {
		cflag = 0;
		cleanup();
	}
	exit(1);
}
//Вывод сообщения об ошибке
static void verror_msg(int err_no, const char *fmt, va_list p)
{
	char *msg;

	fflush(NULL);//Завершение всех операций записи на диск

	/* We want to print entire message with single fprintf to ensure
	 * message integrity if stderr is shared with other programs.
	 * Thus we use vasprintf + single fprintf.
	 */
	/* Для того, чтобы сообщение об ощибке не было перемешано с сообщениями об ошибках
	 * других потоков, если они разделяют с нами stderr, используется  vasprintf и единственный
	 * fprintf
	 */
	msg = NULL;
	if (vasprintf(&msg, fmt, p) >= 0) {
		if (err_no)//Печатаем либо просто сообщение об ошибке, либо еще и номер, если err_no!=0
			fprintf(stderr, "%s: %s: %s\n", progname, msg, strerror(err_no));
		else
			fprintf(stderr, "%s: %s\n", progname, msg);
		free(msg);//Освобождение памяти
	} else {
		/*Если в vasprintf возникли проблемы с malloc, пытаемся произвести
		 * вывод без malloc. В данном случае сообщение об ощибке может быть
		 * перемешано с другими сообщениями об ошибках
		 * */
		fprintf(stderr, "%s: ", progname);
		vfprintf(stderr, fmt, p);
		if (err_no)
			fprintf(stderr, ": %s\n", strerror(err_no));
		else
			putc('\n', stderr);
	}
}

//Функция для вывода сообщения об ошибке без завершения работы
void error_msg(const char *fmt, ...)
{
	va_list p;//Записываем сюда все аргументы
	va_start(p, fmt);
	verror_msg(0, fmt, p);//Выводим форматированное сообщение в stderr
	va_end(p);//Освобождаем память от va_list
}
//Функция для вывода сообщения об ошибке и завершения процесса
void error_msg_and_die(const char *fmt, ...)
{
	va_list p;//Записываем сюда все аргументы
	va_start(p, fmt);
	verror_msg(0, fmt, p);//Выводим форматированное сообщение в stderr
	die();//Завершение процесса с ошибкой
}

//То же самое, что error_msg, но выводим сообщение об ошбике с номером ошибки errno
void perror_msg(const char *fmt, ...)
{
	va_list p;//Записываем сюда все аргументы
	va_start(p, fmt);
	verror_msg(errno, fmt, p);///Выводим форматированное сообщение в stderr
	va_end(p);//Освобождаем память от va_list
}
//То же самое, что error_msg_and_die, но выводим сообщение об ошбике с номером ошибки errno
void perror_msg_and_die(const char *fmt, ...)
{
	va_list p;//Записываем сюда все аргументы
	va_start(p, fmt);
	verror_msg(errno, fmt, p);//Выводим форматированное сообщение в stderr
	die();//Завершаем процесс
}
//Вызывается в случае out_of_memory
void die_out_of_memory(void)
{
	static bool recursed = 0;//Статический флажок на случай, если эта функция уже вызывалась в других потоках
	if (recursed)
		exit(1);
	recursed = 1;
	error_msg_and_die("Out of memory");//Вывод сообщения об ошибке и выход
}
/*Ошибка при парсинге опций. Выводит сообщение об ошибке и завершает работу программы*/
static void
error_opt_arg(int opt, const char *arg)
{
	error_msg_and_die("Invalid -%c argument: '%s'", opt, arg);//Вывод сообщения об ошибке и выход
}

#if USE_SEIZE
/*Присоединить ptrace к pid */
static int
ptrace_attach_or_seize(int pid)
{
	int r;
	if (!use_seize)
		return ptrace(PTRACE_ATTACH, pid, 0L, 0L);//Присоедениться к процессу, сделав его tracee и остановить его
	r = ptrace(PTRACE_SEIZE, pid, 0L, (unsigned long)ptrace_setoptions);//Присоединиться к процессу, но не останавливать его
	if (r)
		return r;
	r = ptrace(PTRACE_INTERRUPT, pid, 0L, 0L);//Остановить отслеживаемый процесс, в случае, если не удалось к нему присоединиться
	return r;
}
#else
# define ptrace_attach_or_seize(pid) ptrace(PTRACE_ATTACH, (pid), 0, 0)
#endif

/*
 * Используется, когда нужно разблокировать остановленный наблюдаемый процесс
 * Должна вызываться только с sig==PTRACE_CONT, PTRACE_DETACH and PTRACE_SYSCALL.
 * Возвращает 0 при успешном завершении работы или если возникла ошибка ESRCH (no such process)
 * (возможно, процесс был убит, пока мы обращались к функции)
 * в противном случае выведет сообщение об ошибке и вернет -1
 */
static int
ptrace_restart(int op, struct tcb *tcp, int sig)
{
	int err;
	const char *msg;

	errno = 0;
	ptrace(op, tcp->pid, (void *) 0, (long) sig); //Пробуем присоединиться к процессу, который указан в параметрах
	err = errno;
	if (!err)
		return 0;//Ошибок не возникло -- возвращаем 0

	msg = "SYSCALL";//Для вывода сообщения об ошибке, выясняем, какая была вызвана операция
	if (op == PTRACE_CONT)
		msg = "CONT";
	if (op == PTRACE_DETACH)
		msg = "DETACH";
#ifdef PTRACE_LISTEN
	if (op == PTRACE_LISTEN)
		msg = "LISTEN";
#endif
	/*
	 * Why curcol != 0? Otherwise sometimes we get this:
	 *
	 * 10252 kill(10253, SIGKILL)              = 0
	 *  <ptrace(SYSCALL,10252):No such process>10253 ...next decode...
	 *
	 * 10252 died after we retrieved syscall exit data,
	 * but before we tried to restart it. Log looks ugly.
	 */
	if (current_tcp && current_tcp->curcol != 0) {
		tprintf(" <ptrace(%s):%s>\n", msg, strerror(err));
		line_ended();
	}
	if (err == ESRCH)//Возвращаем 0,если не найден процесс
		return 0;
	errno = err;//Иначе--выводит сообщение об ощибке
	perror_msg("ptrace(PTRACE_%s,pid:%d,sig:%d)", msg, tcp->pid, sig);
	return -1;
}
//Устанавливает флаг FD_CLOEXEC к файлу, связанному с дескриптором fd
static void
set_cloexec_flag(int fd)
{
	int flags, newflags;

	flags = fcntl(fd, F_GETFD);//Прочитать флаги файлового дескриптора
	if (flags < 0) {//Произошла ошибка при чтении флагов
		perror_msg_and_die("fcntl(%d, F_GETFD)", fd);
	}

	newflags = flags | FD_CLOEXEC;//Добавляем нужный флаг
	if (flags == newflags)
		return;
	//Применяем новые флаги к дескриптору
	fcntl(fd, F_SETFD, newflags); /* never fails */
}
/*Убить процесс с сохранение номера ошибки*/
static void kill_save_errno(pid_t pid, int sig)
{
	int saved_errno = errno;//Сохраняем номер ошибки

	(void) kill(pid, sig);//Убиваем процесс
	errno = saved_errno;//Возвращаем сохраненную ошибку на место
}

/*
 * Если strace запущен с опцией -u, нужно поменять местами uid и euid
 * перед тем и после того, как, как будут произведены операции с файловой системой
 * и операции, связанные с управлением процессами
 */
static void
swap_uid(void)
{
	int euid = geteuid(), uid = getuid();

	if (euid != uid && setreuid(euid, uid) < 0) {//Устанавливаем real and effective user IDs
		perror_msg_and_die("setreuid");//Ошибка
	}
}

#ifdef _LARGEFILE64_SOURCE
# ifdef HAVE_FOPEN64
#  define fopen_for_output fopen64
# else
#  define fopen_for_output fopen
# endif
# define struct_stat struct stat64
# define stat_file stat64
# define struct_dirent struct dirent64
# define read_dir readdir64
# define struct_rlimit struct rlimit64
# define set_rlimit setrlimit64
#else
# define fopen_for_output fopen
# define struct_stat struct stat
# define stat_file stat
# define struct_dirent struct dirent
# define read_dir readdir
# define struct_rlimit struct rlimit
# define set_rlimit setrlimit
#endif
/*Функция для открытия файла path для вывода*/
static FILE *
strace_fopen(const char *path)
{
	FILE *fp;//Струтура для хранения файла

	swap_uid(); // меняем uid и euid
	fp = fopen_for_output(path, "w");//
	if (!fp)//Не получилось открыть файл
		perror_msg_and_die("Can't fopen '%s'", path);
	swap_uid();//меняем id обратно
	set_cloexec_flag(fileno(fp));
	return fp;//Возвращаем файл
}

static int popen_pid = 0;//Специальный пид. Это процесс, в который будет писаться лог, если передан параметр -о [!|]

#ifndef _PATH_BSHELL
# define _PATH_BSHELL "/bin/sh"
#endif

/*
 * We cannot use standard popen(3) here because we have to distinguish
 * popen child process from other processes we trace, and standard popen(3)
 * does not export its child's pid.
 */
//Открываем процесс для записи в него информации, если передана опция -о [!|]*
static FILE *
strace_popen(const char *command)
{
	FILE *fp;
	int pid;
	int fds[2];

	swap_uid();//Ставим нужные uid и gid
	if (pipe(fds) < 0)/*Открываем поток*/
		perror_msg_and_die("pipe");

	set_cloexec_flag(fds[1]); /* never fails */

	pid = vfork();//Клонирует процесс. Родитель замирает, пока ребенок не закончит работу
	if (pid < 0)
		perror_msg_and_die("vfork");

	if (pid == 0) {//В ребенке
		/* child */
		close(fds[1]);//Закрываем записывающую сторону канала
		if (fds[0] != 0) {
			if (dup2(fds[0], 0))//Перенаправляем stdin
				perror_msg_and_die("dup2");
			close(fds[0]);
		}
		execl(_PATH_BSHELL, "sh", "-c", command, NULL);//Запускаем команду command на исполнение
		perror_msg_and_die("Can't execute '%s'", _PATH_BSHELL);
	}

	/* В родителе  */
	popen_pid = pid;
	close(fds[0]);//Закрываем читающую сторону канала
	swap_uid();//Возвращаем uid и gid
	fp = fdopen(fds[1], "w");//Открываем pipe на запись
	if (!fp)
		die_out_of_memory();
	return fp;//Возвращаем открытый канал.
}
//Печатает колонку в лог файл
void
tprintf(const char *fmt, ...)
{
	va_list args;

	va_start(args, fmt);
	if (current_tcp) {//Если текущий дескриптор правильный
		int n = strace_vfprintf(current_tcp->outf, fmt, args);//Выводим в файл
		if (n < 0) {//Возникла ошибка при печати
			if (current_tcp->outf != stderr)
				perror_msg("%s", outfname);
		} else
			current_tcp->curcol += n;//увеличиваем номер колонки
	}
	va_end(args);
}

#ifndef HAVE_FPUTS_UNLOCKED
# define fputs_unlocked fputs
#endif
//Печатаем строку в файл
void
tprints(const char *str)
{
	if (current_tcp) {
		int n = fputs_unlocked(str, current_tcp->outf);//Печатаем переданную строку в лог
		if (n >= 0) {
			current_tcp->curcol += strlen(str);//Увеличиваем номер столбца
			return;
		}
		if (current_tcp->outf != stderr)//Ошибка, если вывод производился не в stderr
			perror_msg("%s", outfname);
	}
}
//Переход к следующей линии
void
line_ended(void)
{
	if (current_tcp) {//Обнуляем колонку в дескрипторе процесса (с которым идет работа)
		current_tcp->curcol = 0;
		fflush(current_tcp->outf);
	}
	if (printing_tcp) {//Обнуляем колонку в дескрипторе процесса, который является текущим по отношению к печати
		printing_tcp->curcol = 0;
		printing_tcp = NULL;
	}
}
//Печать начала записи в лог
void
printleader(struct tcb *tcp)
{
	/* If -ff, "previous tcb we printed" is always the same as current,
	 * because we have per-tcb output files.
	 */
	if (followfork >= 2)//Если каждый тред имеет свой файл -- печатаем в этот файл (опция -ff)
		printing_tcp = tcp;

	if (printing_tcp) {//Указан печатающий тред?
		current_tcp = printing_tcp;
		if (printing_tcp->curcol != 0 && (followfork < 2 || printing_tcp == tcp)) {
			/*
			 * case 1: we have a shared log (i.e. not -ff), and last line
			 * wasn't finished (same or different tcb, doesn't matter).
			 * case 2: split log, we are the same tcb, but our last line
			 * didn't finish ("SIGKILL nuked us after syscall entry" etc).

			 * Попадем сюда в следующих случаях:
			 * 1) Есть разделяемый лог (не указана опция -ff) и последняя печатаемая строка
			 * не закончена (не имеет значение, в текущем или в другом tcb)
			 * 2) мы в том же самом tcb, но последняя линия не была закончена
			 *
			 */
			tprints(" <unfinished ...>\n");//Сообщаем о незаконченности последней строки и переходим на нулевой столбец
			printing_tcp->curcol = 0;
		}
	}

	printing_tcp = tcp;
	current_tcp = tcp;
	current_tcp->curcol = 0;

	if (print_pid_pfx)//Как печатать номер пида?
		tprintf("%-5d ", tcp->pid);
	else if (nprocs > 1 && !outfname)
		tprintf("[pid %5u] ", tcp->pid);

	if (tflag) {//Нужны таймстампы? (опция -t)
		char str[sizeof("HH:MM:SS")];
		struct timeval tv, dtv;
		static struct timeval otv;

		gettimeofday(&tv, NULL);//Берем текущее время
		if (rflag) {//Относительные таймстампы? Bug??
			if (otv.tv_sec == 0)
				otv = tv;
			tv_sub(&dtv, &tv, &otv);
			tprintf("%6ld.%06ld ", //Печатаем таймстамп в файл
				(long) dtv.tv_sec, (long) dtv.tv_usec);
			otv = tv;
		}
		else if (tflag > 2) {//Указано 3t
			tprintf("%ld.%06ld ",
				(long) tv.tv_sec, (long) tv.tv_usec);
		}
		else {//Не относительный таймстампы и не 3t
			time_t local = tv.tv_sec;
			strftime(str, sizeof(str), "%T", localtime(&local));
			if (tflag > 1)// 2t? -- пичатаем микросекунды
				tprintf("%s.%06ld ", str, (long) tv.tv_usec);
			else
				tprintf("%s ", str);
		}
	}
	if (iflag)//Нужно печатать pc?
		print_pc(tcp);
}
//Печатаем заполнители
void
tabto(void)
{
	if (current_tcp->curcol < acolumn)//Если текущий столбец меньше, чем количество столбцов
		tprints(acolumn_spaces + current_tcp->curcol);//Печатаем в лог соответствющее число заполнителей
}

/*
 * Дожна вызываться сразу после успешного присоединения к отслеживаемому процессу
 * в противном случае, "strace -oFILE -ff -p<nonexistant_pid>"
 * может создать ненужный пустой файл FILE.<nonexistant_pid> и завершиться
 */
static void
newoutf(struct tcb *tcp)
{
	tcp->outf = shared_log; /* если не было опции -ff у всех процессов будет один лог*/
	if (followfork >= 2) {//Если была указана опция ff генерируем имя файла в соответствии с pid-ом процесса и открываем файл на запись
		char name[520 + sizeof(int) * 3];
		sprintf(name, "%.512s.%u", outfname, tcp->pid);
		tcp->outf = strace_fopen(name);//
	}
}
/*Расширяет таблицу отслеживаемых процессов*/
static void
expand_tcbtab(void)
{
	/* Allocate some more TCBs and expand the table.
	   We don't want to relocate the TCBs because our
	   callers have pointers and it would be a pain.
	   So tcbtab is a table of pointers.  Since we never
	   free the TCBs, we allocate a single chunk of many.  */
	int i = tcbtabsize;
	struct tcb *newtcbs = calloc(tcbtabsize, sizeof(newtcbs[0]));//Память для новой записи
	struct tcb **newtab = realloc(tcbtab, tcbtabsize * 2 * sizeof(tcbtab[0]));//Перевыделяем память
	if (!newtab || !newtcbs)///Ошибка при выделении памяти
		die_out_of_memory();
	tcbtabsize *= 2;//Увеличиваем таблицу в два раза
	tcbtab = newtab;
	while (i < tcbtabsize)//Инициализируем записи новой таблицы
		tcbtab[i++] = newtcbs++;
}
//Добавляет заданный пид в отслеживаемые
static struct tcb *
alloctcb(int pid)
{
	int i;
	struct tcb *tcp;//Структура для процесса

	if (nprocs == tcbtabsize)//Расширяем таблицу записей, если нужно
		expand_tcbtab();

	for (i = 0; i < tcbtabsize; i++) {//Ищем первую свободную запись в таблице процессов
		tcp = tcbtab[i];
		if (!tcp->pid) {//Если запись свободна
			memset(tcp, 0, sizeof(*tcp));//Обнуляем поля в ней
			tcp->pid = pid;//Ставим пид
#if SUPPORTED_PERSONALITIES > 1
			tcp->currpers = current_personality;//Ставим архитектуру
#endif

#ifdef USE_LIBUNWIND
			if (stack_trace_enabled)
				unwind_tcb_init(tcp);
#endif

			nprocs++;//Увеличиваем количество отслеживаемых процессов
			if (debug_flag)//Вывод отладочной информации, если нужно
				fprintf(stderr, "new tcb for pid %d, active tcbs:%d\n", tcp->pid, nprocs);
			return tcp;//Возвращаем новую струтуру
		}
	}
	error_msg_and_die("bug in alloctcb");//Ошибка. Сюда мы попадат не должны
}
/*Убирает запись о процессе из таблицы pidов*/
static void
droptcb(struct tcb *tcp)
{
	if (tcp->pid == 0) //Случай, когда запись и так не активна
		return;

#ifdef USE_LIBUNWIND
	if (stack_trace_enabled) {
		unwind_tcb_fin(tcp);
	}
#endif

	nprocs--;//Уменьшаем счетчик активных потоков
	if (debug_flag)
		fprintf(stderr, "dropped tcb for pid %d, %d remain\n", tcp->pid, nprocs);

	if (tcp->outf) {//Закрываем лог-файл, если нужно, либо завершаем операции записи в этот файл и пишем туда информацию об отсоединении указанного процесса, если нужно
		if (followfork >= 2) {
			if (tcp->curcol != 0)
				fprintf(tcp->outf, " <detached ...>\n");
			fclose(tcp->outf);
		} else {
			if (printing_tcp == tcp && tcp->curcol != 0)
				fprintf(tcp->outf, " <detached ...>\n");
			fflush(tcp->outf);
		}
	}

	if (current_tcp == tcp)//Если шла работа с pid-ом, который нужно завешить
		current_tcp = NULL;
	if (printing_tcp == tcp)//Если шла операция вывода для pid-а, который нужно завершить
		printing_tcp = NULL;

	memset(tcp, 0, sizeof(*tcp));//Обнуляем память, связанную с pid-ом
}

/* Detach traced process.
 * Never call DETACH twice on the same process as both unattached and
 * attached-unstopped processes give the same ESRCH.  For unattached process we
 * would SIGSTOP it and wait for its SIGSTOP notification forever.
 *
 * Отделить отслеживаемый процесс.
 * Нельзя вызывать дваждый для одного процесса
 */
static void
detach(struct tcb *tcp)
{
	int error;
	int status;

	if (tcp->flags & TCB_BPTSET)//Флаг TCB_BPTSET установлен для текущего потока
		clearbpt(tcp);//Убрать флаг

	/*
	 * Linux wrongly insists the child be stopped
	 * before detaching.  Arghh.  We go through hoops
	 * to make a clean break of things.
	 */
#if defined(SPARC)
# undef PTRACE_DETACH
# define PTRACE_DETACH PTRACE_SUNDETACH
#endif

	if (!(tcp->flags & TCB_ATTACHED))//Если процесс итак не присоединен -- просто сбрасываем запись о нем из таблицы
		goto drop;

	/* We attached but possibly didn't see the expected SIGSTOP.
	 * We must catch exactly one as otherwise the detached process
	 * would be left stopped (process state T).
	 *
	 * Мы присоединены, но, возможно, не знаем о том, что в процессе
	 * был вызван SIGSTOP
	 * Нужно, чтобы SIGSTOP был только один, инче отцепленный процесс
	 * останется в остановленном состоянии
	 */
	if (tcp->flags & TCB_IGNORE_ONE_SIGSTOP) //
		goto wait_loop;

	error = ptrace(PTRACE_DETACH, tcp->pid, 0, 0);//Отцепляем процесс
	if (!error) {//Не возникло ошибок?
		/* On a clear day, you can see forever. */
		goto drop;
	}
	if (errno != ESRCH) {
		/* Shouldn't happen. */
		perror_msg("detach: ptrace(PTRACE_DETACH,%u)", tcp->pid);
		goto drop;
	}
	/* ESRCH: process is either not stopped or doesn't exist. */
	if (my_tkill(tcp->pid, 0) < 0) {//Пытаемся убить процесс
		if (errno != ESRCH)//ESRCH: Процесс не остановлен или не существует
			/* Shouldn't happen. */
			perror_msg("detach: tkill(%u,0)", tcp->pid);//Ошибка
		/* else: process doesn't exist. */
		goto drop;
	}
	/* Process is not stopped, need to stop it. */
	//Процесс не остановлен. Мы должны его остановить
	if (use_seize) {
		/*
		 * With SEIZE, tracee can be in group-stop already.
		 * In this state sending it another SIGSTOP does nothing.
		 * Need to use INTERRUPT.
		 * Testcase: trying to ^C a "strace -p <stopped_process>".
		 */
		error = ptrace(PTRACE_INTERRUPT, tcp->pid, 0, 0);//В состоянии SEIZE может быть в групповой остановке -- если мы пошел еще один SIGSTOP -- это ни к чему не приведет
		if (!error)//Не возникло ошибок?
			goto wait_loop;
		if (errno != ESRCH)//Возникла ошибка и она не связана с тем, что процесс не существует
			perror_msg("detach: ptrace(PTRACE_INTERRUPT,%u)", tcp->pid);
	}
	else {
		error = my_tkill(tcp->pid, SIGSTOP);//Отправляем процессу сигнал SIGSTOP
		if (!error)//Ошибок нет -- идем ожидать завершения
			goto wait_loop;
		if (errno != ESRCH)//Возникла ошибка при попытки остановить процесс
			perror_msg("detach: tkill(%u,SIGSTOP)", tcp->pid);
	}
	/* Either process doesn't exist, or some weird error. */
	goto drop;

 wait_loop:
	/* We end up here in three cases:
	 * 1. We sent PTRACE_INTERRUPT (use_seize case)
	 * 2. We sent SIGSTOP (!use_seize)
	 * 3. Attach SIGSTOP was already pending (TCB_IGNORE_ONE_SIGSTOP set)
	 *
	 * Здесь мы можем оказаться в 3-х случаях:
	 * 1. Мы послали процессу PTRACE_INTERRUPT (use_seize case)
	 * 2. Мы послали процессу SIGSTOP
	 * 3. SIGSTOP был уже отправлен
	 */
	for (;;) {
		int sig;
		if (waitpid(tcp->pid, &status, __WALL) < 0) {//Ждем завершения процесса
			if (errno == EINTR)//Вызов был прерван -- нужно снова подождать
				continue;
			/*
			 * if (errno == ECHILD) break;
			 * ^^^  WRONG! We expect this PID to exist,
			 * and want to emit a message otherwise:
			 */
			perror_msg("detach: waitpid(%u)", tcp->pid);//Ошибка
			break;
		}
		if (!WIFSTOPPED(status)) {//Процесс не был остановлен -- он вышел из-за какого-то сигнала, сюда мы не должны попадать в нормальных случаях
			/*
			 * Tracee exited or was killed by signal.
			 * We shouldn't normally reach this place:
			 * we don't want to consume exit status.
			 * Consider "strace -p PID" being ^C-ed:
			 * we want merely to detach from PID.
			 *
			 * However, we _can_ end up here if tracee
			 * was SIGKILLed.
			 */
			break;
		}
		sig = WSTOPSIG(status);//Запоминаем сигнал, который остановил процесс
		if (debug_flag)
			fprintf(stderr, "detach wait: event:%d sig:%d\n",//Вывод для отладки strace
					(unsigned)status >> 16, sig);
		if (use_seize) {//use_seize-case
			unsigned event = (unsigned)status >> 16;
			if (event == PTRACE_EVENT_STOP /*&& sig == SIGTRAP*/) {
				/*
				 * sig == SIGTRAP: PTRACE_INTERRUPT stop.
				 * sig == other: process was already stopped
				 * with this stopping sig (see tests/detach-stopped).
				 * Looks like re-injecting this sig is not necessary
				 * in DETACH for the tracee to remain stopped.
				 */
				sig = 0;
			}
			/*
			 * PTRACE_INTERRUPT is not guaranteed to produce
			 * the above event if other ptrace-stop is pending.
			 * See tests/detach-sleeping testcase:
			 * strace got SIGINT while tracee is sleeping.
			 * We sent PTRACE_INTERRUPT.
			 * We see syscall exit, not PTRACE_INTERRUPT stop.
			 * We won't get PTRACE_INTERRUPT stop
			 * if we would CONT now. Need to DETACH.
			 */
			if (sig == syscall_trap_sig)
				sig = 0;
			/* else: not sure in which case we can be here.
			 * Signal stop? Inject it while detaching.
			 */
			ptrace_restart(PTRACE_DETACH, tcp, sig);
			break;
		}
		/* Note: this check has to be after use_seize check */
		/* (else, in use_seize case SIGSTOP will be mistreated) */
		if (sig == SIGSTOP) {
			/* Detach, suppressing SIGSTOP */
			ptrace_restart(PTRACE_DETACH, tcp, 0);
			break;
		}
		if (sig == syscall_trap_sig)
			sig = 0;
		/* Can't detach just yet, may need to wait for SIGSTOP */
		error = ptrace_restart(PTRACE_CONT, tcp, sig);
		if (error < 0) {
			/* Should not happen.
			 * Note: ptrace_restart returns 0 on ESRCH, so it's not it.
			 * ptrace_restart already emitted error message.
			 */
			break;
		}
	}

 drop://Удаляем запись из таблицы процессов
	if (!qflag && (tcp->flags & TCB_ATTACHED))
		fprintf(stderr, "Process %u detached\n", tcp->pid);

	droptcb(tcp);
}

//Парсит значение параметра -p. Пиды могут записываться группой и иметь различные разделители..
//Добавляет заданные значения в
static void
process_opt_p_list(char *opt)
{
	while (*opt) {
		/*
		 * We accept -p PID,PID; -p "`pidof PROG`"; -p "`pgrep PROG`".
		 * pidof uses space as delim, pgrep uses newline. :(
		 */
		int pid;
		char *delim = opt + strcspn(opt, ", \n\t");//Поскольку пид может поступить из различных источинков, они могут иметь различные разделитли
		char c = *delim;//c -- разделитель

		*delim = '\0';//устанавливаем значение, лежащее в разделителе в 0
		pid = string_to_uint(opt);//Берем первый пид
		if (pid <= 0) {//Ошибка
			error_msg_and_die("Invalid process id: '%s'", opt);
		}
		if (pid == strace_tracer_pid) {//Сказали следить за самим собой
			error_msg_and_die("I'm sorry, I can't let you do that, Dave.");//Кто такой Дейв? 38: David S. Miller <davem@caip.rutgers.edu> или Dr. David Alan Gilbert <dave@treblig.org>
		}
		*delim = c;
		alloctcb(pid);//Добавляем процесс с этим пидом в таблицу процессов
		if (c == '\0')//Строка завершена
			break;
		opt = delim + 1;//Следующая запись
	}
}
//
static void
startup_attach(void)
{
	int tcbi;
	struct tcb *tcp;

	/*
	 * Block user interruptions as we would leave the traced
	 * process stopped (process state T) if we would terminate in
	 * between PTRACE_ATTACH and wait4() on SIGSTOP.
	 * We rely on cleanup() from this point on.
	 */
	if (interactive)//Добавляем в  blocked_set в набор блокируемых сигналов, если происходит работа в интерактивном режиме
		sigprocmask(SIG_BLOCK, &blocked_set, NULL);

	if (daemonized_tracer) {//Если была указана опция -
		pid_t pid = fork();
		if (pid < 0) {
			perror_msg_and_die("fork");
		}
		if (pid) { /* Родитель */
			/*
			 * Ожидаем, пока процесс-внук присоединится к процессу, который отслеживается
			 * внук остановит работу текущего процесса после того, как присоединится
			 * После смерти текущего процесса, процесс-дедушка выйдет из своего wait
			 * Далее он запустит программу, которая должна будет остлеживаться
			 */
			pause();
			_exit(0); /* paranoia */
		}
		/*Этот процесс будет трейсером -- запоминаем наш новый pid*/
		strace_tracer_pid = getpid();
	}

	for (tcbi = 0; tcbi < tcbtabsize; tcbi++) {
		tcp = tcbtab[tcbi];

		if (!tcp->pid)//Если эта запись не имеет указанного пида -- переход к следующей итерации
			continue;

		/* Мы должны присоединиться к процессу tcp, но до сих пор не присоединены?*/
		if (tcp->flags & TCB_ATTACHED)
			continue; /* Нет, мы уже присоединены*/

		/*Если не была указана опция -D и были указаны -f или -ff*/
		/*Т.е. трэйсер не демон, и нужно следить за всемы тредами, порожденными
		 * наблюдаемым процессом
		 * Мы примоединяемся к каждому треду процесса*/
		if (followfork && !daemonized_tracer) {
			char procdir[sizeof("/proc/%d/task") + sizeof(int) * 3];
			DIR *dir;
			/*Открываем директорию указанного процесса*/
			sprintf(procdir, "/proc/%d/task", tcp->pid);
			dir = opendir(procdir);
			if (dir != NULL) {//Если директория открылась
				unsigned int ntid = 0, nerr = 0;//Счетчики потоков и тредов
				struct_dirent *de;

				while ((de = read_dir(dir)) != NULL) {//Читаем все записи в директории
					struct tcb *cur_tcp;
					int tid;

					if (de->d_fileno == 0)//Если текущая запись -- символическая ссылка -- переходим к следующей
						continue;
					/* we trust /proc filesystem */
					tid = atoi(de->d_name);//tid -- имя записи в директории
					if (tid <= 0)
						continue;
					++ntid;//
					if (ptrace_attach_or_seize(tid) < 0) {//Присоединяемся к потоку
						++nerr;//Если не удалось -- увеличиваем счетчик ошибок, выводим сообщение и переходим к следующей итерации
						if (debug_flag)
							fprintf(stderr, "attach to pid %d failed\n", tid);
						continue;
					}
					if (debug_flag)
						fprintf(stderr, "attach to pid %d succeeded\n", tid);
					cur_tcp = tcp;
					if (tid != tcp->pid)//Если в процессе живет тред, номер которого не равен пиду, создаем новую запись в таблице отслеживаемых pidов
						cur_tcp = alloctcb(tid);
					cur_tcp->flags |= TCB_ATTACHED | TCB_STARTUP | post_attach_sigstop;//Мы присоединились к текущему треду
					newoutf(cur_tcp);//Создаем новый лог-файл, если требуется
				}
				closedir(dir);//Закрываем директорию /proc/<PID>/task
				if (interactive) {//Если идет работа в интерактивном режиме, проверяем, прервана ли работа. Если да -- прекращаем работу текущего цикла
					sigprocmask(SIG_SETMASK, &empty_set, NULL);//Запрещаем блокируемые сигналы
					if (interrupted)
						goto ret;
					sigprocmask(SIG_BLOCK, &blocked_set, NULL);//Возвращаем все как было
				}
				ntid -= nerr;
				if (ntid == 0) {//Если не удалось подсоединиться ни к одному из потоков
					perror_msg("attach: ptrace(PTRACE_ATTACH, ...)");
					droptcb(tcp);//Убираем запись о текущем пиде из таблицы
					continue;
				}
				if (!qflag) {//Если нужно, пишем сообщение об присоединении
					fprintf(stderr, ntid > 1 ? "Process %u attached with %u threads\n" : "Process %u attached\n", tcp->pid, ntid);
				}
				if (!(tcp->flags & TCB_ATTACHED)) {
					/* -p PID,мы не смогли подключиться к самому PID-у,
					 * но смогли к одному из его тредов.
					 * Убираем запись о пиде из таблицы (там сохранятся записи об его тредах, к которым удалось подсоединиться)
					 */
					droptcb(tcp);
				}
				continue;
			} /* if (opendir worked) */
		} /* if (-f) */
		//Присоединяемся к pid-у
		if (ptrace_attach_or_seize(tcp->pid) < 0) {
			perror_msg("attach: ptrace(PTRACE_ATTACH, ...)");
			droptcb(tcp);//Ошибка. Убираем запись о треде из таблцы
			continue;
		}
		tcp->flags |= TCB_ATTACHED | TCB_STARTUP | post_attach_sigstop;//Устанавливаем нужные флаги
		newoutf(tcp);//Создаем выходной файл, если нужно
		if (debug_flag)
			fprintf(stderr, "attach to pid %d (main) succeeded\n", tcp->pid);

		if (daemonized_tracer) {
			/*
			 * Убиваем родителя, если указана опция -D
			 * Make parent go away.
			 * Also makes grandparent's wait() unblock.
			 */
			kill(getppid(), SIGKILL);
		}

		if (!qflag)
			fprintf(stderr,
				"Process %u attached\n",
				tcp->pid);
	} /* for each tcbtab[] */

 ret:
	if (interactive)//Если интерактивный режим, ставим empty_set вместо списка сигналов, которые могут блокировать
		sigprocmask(SIG_SETMASK, &empty_set, NULL);
}

/* Stack-o-phobic exec helper, in the hope to work around
 * NOMMU + "daemonized tracer" difficulty.
 */
struct exec_params {
	int fd_to_close;
	uid_t run_euid;
	gid_t run_egid;
	char **argv;
	char *pathname;
};
static struct exec_params params_for_tracee; //Параметры отслеживаемого процесса
exec_or_die(void)
{
	struct exec_params *params = &params_for_tracee;

	if (params->fd_to_close >= 0)//Если пишем не в stderr, файловый дескриптор fd_to_close нужно закрыть, чтобы в него писал трэйсер
		close(params->fd_to_close);
	if (!daemonized_tracer && !use_seize) {//Если не была указана опция -D,
		if (ptrace(PTRACE_TRACEME, 0L, 0L, 0L) < 0) {//Говорим ptrace, что мы -- процесс, который будет отслежваться своим родителем
			perror_msg_and_die("ptrace(PTRACE_TRACEME, ...)");
		}
	}

	if (username != NULL) {//Случай, когда указано имя пользователя, от имени которого нужно будет запустить процесс
		/*
		 * It is important to set groups before we
		 * lose privileges on setuid.
		 */
		if (initgroups(username, run_gid) < 0) {//Получаем gid пользователя
			perror_msg_and_die("initgroups");
		}
		if (setregid(run_gid, params->run_egid) < 0) {//Устанавливаем rgid текущего процесса в run_gid и effective gid в params->run_egid
			perror_msg_and_die("setregid");
		}
		if (setreuid(run_uid, params->run_euid) < 0) {//Устанавливаем ruid текущего процесса в run_uid и effective uid в params->run_euid
			perror_msg_and_die("setreuid");
		}
	}
	else if (geteuid() != 0)//Если имя не указано
		if (setreuid(run_uid, run_uid) < 0) {//Просто устанавливаем ruid и effective uid
			perror_msg_and_die("setreuid");
		}

	if (!daemonized_tracer) {//Если не была указана опция -D
		/*
		 * Induce a ptrace stop. Tracer (our parent)
		 * will resume us with PTRACE_SYSCALL and display
		 * the immediately following execve syscall.
		 * Can't do this on NOMMU systems, we are after
		 * vfork: parent is blocked, stopping would deadlock.
		 */
		if (!NOMMU_SYSTEM)
			kill(getpid(), SIGSTOP);//Останавливаем выполнение текущего процесса до того, как получим сигнал продолжения от родителя
	} else {
		alarm(3);//Планируем SIGALRM через 3 секунды
		/* we depend on SIGCHLD set to SIG_DFL by init code */
		/* if it happens to be SIG_IGN'ed, wait won't block */
		wait(NULL);//Ждем, пока ребенок закончит работу
		alarm(0);//Отменяем запланированный SIGALRM
	}

	execv(params->pathname, params->argv);//Запуск указанной программы на исполнение
	perror_msg_and_die("exec");//Ошибка. Мы не должны были попасть сюда
}
/*Функция для старта дочернего процесса, если strace вызван путем strace FILE*/
static void
startup_child(char **argv)
{
	struct_stat statbuf;//Структура для храниния информации о файлу
	const char *filename;//Имя файла
	char pathname[MAXPATHLEN];//Путь
	int pid;//Пид дочернего процесса
	struct tcb *tcp;

	filename = argv[0];//
	if (strchr(filename, '/')) {//Если имя файла содержит резделители
		if (strlen(filename) > sizeof pathname - 1) {//Ошибка: слишком длинное имя файла
			errno = ENAMETOOLONG;
			perror_msg_and_die("exec");
		}
		strcpy(pathname, filename);//Копируем имя в pathname
	}
#ifdef USE_DEBUGGING_EXEC
	/*
	 * Debuggers customarily check the current directory
	 * first regardless of the path but doing that gives
	 * security geeks a panic attack.
	 */
	else if (stat_file(filename, &statbuf) == 0)
		strcpy(pathname, filename);
#endif /* USE_DEBUGGING_EXEC */
	else {//Если имя файла не содержит резделители
		const char *path;
		int m, n, len;
		//Производится поиск filename в PATH
		for (path = getenv("PATH"); path && *path; path += m) {
			const char *colon = strchr(path, ':');//Берем очередную запись из PATH
			if (colon) {
				n = colon - path;
				m = n + 1;
			}
			else
				m = n = strlen(path);
			if (n == 0) {//Проверяем, был ли получено правильный путь
				if (!getcwd(pathname, MAXPATHLEN))
					continue;
				len = strlen(pathname);
			}
			else if (n > sizeof pathname - 1)
				continue;
			else {
				strncpy(pathname, path, n);//Копируем текущую запись в pathname
				len = n;
			}
			if (len && pathname[len - 1] != '/') //Добавляем /, если требуется
				pathname[len++] = '/';
			strcpy(pathname + len, filename);//конкатенируем pathname и filename
			if (stat_file(pathname, &statbuf) == 0 && //Проверяем существует ли файл
			    /* Accept only regular files
			       with some execute bits set.
			       XXX not perfect, might still fail */
			    S_ISREG(statbuf.st_mode) && //Если файл существует, и он не является ссылкой
			    (statbuf.st_mode & 0111))//И к нему есть доступ, заканчиваем цикл
				break;
		}
	}
	if (stat_file(pathname, &statbuf) < 0) {
		perror_msg_and_die("Can't stat '%s'", filename);//Ошибка. Файл не найден
	}

	//Модифицируем параметры процесса, который будет отслеживаться
	params_for_tracee.fd_to_close = (shared_log != stderr) ? fileno(shared_log) : -1; //Запоминаем файловый дескриптор, если не сказано писать лог в stderr
	params_for_tracee.run_euid = (statbuf.st_mode & S_ISUID) ? statbuf.st_uid : run_uid; //Запоминаем нужный uid
	params_for_tracee.run_egid = (statbuf.st_mode & S_ISGID) ? statbuf.st_gid : run_gid;//Запоминаем нужный gid
	params_for_tracee.argv = argv; //Запоминаем argv
	/*
	 * On NOMMU, can be safely freed only after execve in tracee.
	 * It's hard to know when that happens, so we just leak it.
	 */
	params_for_tracee.pathname = NOMMU_SYSTEM ? strdup(pathname) : pathname;

#if defined HAVE_PRCTL && defined PR_SET_PTRACER && defined PR_SET_PTRACER_ANY
	if (daemonized_tracer)//Если была указана опция -D (трейсер--демон), необходимо установить нужные разрешения безопасности, чтобы ptrace могла получить доступ к текущему процессу
		 //prctl - operations on a process
		prctl(PR_SET_PTRACER, PR_SET_PTRACER_ANY);

#endif

	pid = fork();//Создаем процесс-копию
	if (pid < 0) {//Произошла ошибка
		perror_msg_and_die("fork");
	}
	if ((pid != 0 && daemonized_tracer)//Если мы находимся в процессе родителе и указана опция -D
	 || (pid == 0 && !daemonized_tracer)//или если мы находимся в процесс-ребенке и опция -D не указана
	) {
		/* We are to become the tracee. Two cases:
		 * -D: we are parent
		 * not -D: we are child
		 */
		//Текущий процесс будет отслеживаемым
		exec_or_die(); //Запускаем программу, которая будет отслеживаться
	}

	/* Этот процесс является трейсером*/

	if (!daemonized_tracer) {//В процессе-трейсере
		strace_child = pid; //Запоминаем pid strace-ребенка
		if (!use_seize) {
			/* child did PTRACE_TRACEME, nothing to do in parent */
		} else {
			if (!NOMMU_SYSTEM) {
				/* Ожидаем, пока ребенок закончит работу */
				int status;
				while (waitpid(pid, &status, WSTOPPED) < 0) {
					if (errno == EINTR)
						continue;//Продолжаем ждать, если возникла ошибка EINTR
					perror_msg_and_die("waitpid"); //Ошибка
				}
				if (!WIFSTOPPED(status) || WSTOPSIG(status) != SIGSTOP) {//Проверка корректности завершения дочернего процесса
					kill_save_errno(pid, SIGKILL);//Если процесс не завершился корректно, убиваем его с сохранением ошибки
					perror_msg_and_die("Unexpected wait status %x", status);
				}
			}
			/* Else: NOMMU case, we have no way to sync.
			 * Just attach to it as soon as possible.
			 * This means that we may miss a few first syscalls...
			 */

			if (ptrace_attach_or_seize(pid)) {//Присоединиться к процессу ребенку ptrace-ом и остановить его
				kill_save_errno(pid, SIGKILL);//убиваем ребенка с сохранением ошибки, если он не был остановлен командой из условия
				perror_msg_and_die("Can't attach to %d", pid);
			}
			if (!NOMMU_SYSTEM)
				kill(pid, SIGCONT);//Убиваем процесс-ребенок
		}
		tcp = alloctcb(pid);//Добавляем созданный пид в список отслеживаемых
		if (!NOMMU_SYSTEM)//Записываем нужные флаги в информацию о процессе
			tcp->flags |= TCB_ATTACHED | TCB_STARTUP | post_attach_sigstop;//
		else
			tcp->flags |= TCB_ATTACHED | TCB_STARTUP;
		newoutf(tcp);//Открываем лог для вновь созданного процесса
	}
	else {
		/* C опцией -D, сюда попадает процесс -- *ребенок*, IOW: имеем другой пид pid. */
		strace_tracer_pid = getpid();//запоминаем свой пид
		/* Отслеживаемый процесс -- наш родитель: */
		pid = getppid();
		alloctcb(pid);//Присоединение будет осуществлено позже. Выделяем для отслеживаемого процесса запись в таблице
		/* attaching will be done later, by startup_attach */
		/* note: we don't do newoutf(tcp) here either! */

		/* NOMMU BUG! -D mode is active, we (child) return,
		 * and we will scribble over parent's stack!
		 * When parent later unpauses, it segfaults.
		 *
		 * We work around it
		 * (1) by declaring exec_or_die() NORETURN,
		 * hopefully compiler will just jump to it
		 * instead of call (won't push anything to stack),
		 * (2) by trying very hard in exec_or_die()
		 * to not use any stack,
		 * (3) having a really big (MAXPATHLEN) stack object
		 * in this function, which creates a "buffer" between
		 * child's and parent's stack pointers.
		 * This may save us if (1) and (2) failed
		 * and compiler decided to use stack in exec_or_die() anyway
		 * (happens on i386 because of stack parameter passing).
		 *
		 * A cleaner solution is to use makecontext + setcontext
		 * to create a genuine separate stack and execute on it.
		 */
	}
}

/*
 * Проверяет, поддерживает ли ядро опцию PTRACE_O_TRACECLONE и др.
 * Сначала создает новый дочерний процесс, вызывает ptrace c опцией PTRACE_SETOPTIONS
 * далее проверяет какие опции поддерживаются ядром
 */
static int
test_ptrace_setoptions_followfork(void)
{
	int pid, expected_grandchild = 0, found_grandchild = 0;
	const unsigned int test_options = PTRACE_O_TRACECLONE | //Опции для проверки
					  PTRACE_O_TRACEFORK |
					  PTRACE_O_TRACEVFORK;

	/* Need fork for test. NOMMU has no forks */
	if (NOMMU_SYSTEM)
		goto worked; /* be bold, and pretend that test succeeded */

	pid = fork();
	if (pid < 0)//Ошибка при вызове fork
		perror_msg_and_die("fork");
	if (pid == 0) { //Процесс-ребенок
		pid = getpid(); //Запоминаем пид
		if (ptrace(PTRACE_TRACEME, 0L, 0L, 0L) < 0) //Вызываем ptrace для теста
			perror_msg_and_die("%s: PTRACE_TRACEME doesn't work", //Ошибка
					   __func__);
		kill_save_errno(pid, SIGSTOP);
		if (fork() < 0)//Создаем еще одну копию
			perror_msg_and_die("fork");//Ошибка при создании копии
		_exit(0);//Выход дочернего процесса и процесса, который он породил
	}

	while (1) {
		int status, tracee_pid;

		errno = 0;
		tracee_pid = wait(&status);//Ждет смерти потомка
		if (tracee_pid <= 0) {
			if (errno == EINTR)//Ошибка: потомок не может быть прерван
				continue;
			if (errno == ECHILD)//Нет дочерних процессов
				break;
			kill_save_errno(pid, SIGKILL);//Убиваем дочерний процесс -- ошибка
			perror_msg_and_die("%s: unexpected wait result %d",
					   __func__, tracee_pid);
		}
		if (WIFEXITED(status)) {//Если дочерний процесс закончился нормально
			if (WEXITSTATUS(status)) {//Проверяем return value
				if (tracee_pid != pid)//Убиваем процесс-потомок, если это не потомок главного процесса
					kill_save_errno(pid, SIGKILL);
				error_msg_and_die("%s: unexpected exit status %u",
						  __func__, WEXITSTATUS(status));
			}
			continue;
		}
		if (WIFSIGNALED(status)) {//Проверяем, был ли потомок остановлен из-за сигнала
			if (tracee_pid != pid)//Убиваем процесс-потомок, если это не потомок главного процесса
				kill_save_errno(pid, SIGKILL);
			error_msg_and_die("%s: unexpected signal %u",
					  __func__, WTERMSIG(status));
		}
		if (!WIFSTOPPED(status)) {//Проверяет, был ли потомок остановлен
			if (tracee_pid != pid)//Убиваем процесс-потомок, если это не потомок главного процесса
				kill_save_errno(tracee_pid, SIGKILL);
			kill_save_errno(pid, SIGKILL);//Убиваем так же процесс--потомок
			error_msg_and_die("%s: unexpected wait status %x",
					  __func__, status);
		}
		if (tracee_pid != pid) {//Проверяем, находимся ли мы в процессе-внуке
			found_grandchild = tracee_pid;
			if (ptrace(PTRACE_CONT, tracee_pid, 0, 0) < 0) {//Проверяем, работает ли опция PTRACE_CONT
				kill_save_errno(tracee_pid, SIGKILL);
				kill_save_errno(pid, SIGKILL);
				perror_msg_and_die("PTRACE_CONT doesn't work");
			}
			continue;
		}
		switch (WSTOPSIG(status)) {
		case SIGSTOP://Если процесс получил SIGSTOP
			if (ptrace(PTRACE_SETOPTIONS, pid, 0, test_options) < 0//Проверяем работу опции PTRACE_SETOPTIONS
			    && errno != EINVAL && errno != EIO)
				perror_msg("PTRACE_SETOPTIONS");
			break;
		case SIGTRAP: //Если процесс получил SIGSTOP
			if (status >> 16 == PTRACE_EVENT_FORK) {
				long msg = 0;

				if (ptrace(PTRACE_GETEVENTMSG, pid,
					   NULL, (long) &msg) == 0)//Проверяем работу опции PTRACE_GETEVENTMSG
					expected_grandchild = msg;
			}
			break;
		}
		if (ptrace(PTRACE_SYSCALL, pid, 0, 0) < 0) {//Проверяем работу опции PTRACE_SYSCALL
			kill_save_errno(pid, SIGKILL);
			perror_msg_and_die("PTRACE_SYSCALL doesn't work");
		}
	}
	if (expected_grandchild && expected_grandchild == found_grandchild) {//Попадем внутрь, если все опции работают
 worked:
		ptrace_setoptions |= test_options;//Добавляем проверенные опции
		if (debug_flag)
			fprintf(stderr, "ptrace_setoptions = %#x\n",
				ptrace_setoptions);
		return 0;//Отработали успешно
	}
	error_msg("Test for PTRACE_O_TRACECLONE failed, "
		  "giving up using this feature.");
	return 1;
}

/*
 * Test whether the kernel support PTRACE_O_TRACESYSGOOD.
 * First fork a new child, call ptrace(PTRACE_SETOPTIONS) on it,
 * and then see whether it will stop with (SIGTRAP | 0x80).
 *
 * Use of this option enables correct handling of user-generated SIGTRAPs,
 * and SIGTRAPs generated by special instructions such as int3 on x86:

# compile with: gcc -nostartfiles -nostdlib -o int3 int3.S
_start:		.globl	_start
		int3
		movl	$42, %ebx
		movl	$1, %eax
		int	$0x80
*//*
 * Проверяет поддержку ядром PTRACE_O_TRACESYSGOOD
 * сначала пораждает ребенка, затем вызвает в нем ptrace(PTRACE_SETOPTIONS)
 * и смотрит, остановится ли он со статусом SIGTRAP | 0x80
 *
 * Использование опции PTRACE_O_TRACESYSGOOD позволяет корректно обрабатывать
 * SIGTRAP-ы, сгенерированные пользователем и SIGTRAP-ы, сгенерированные специальными инструкциями
 * такимми, как int3 в x86
 */
static int
test_ptrace_setoptions_for_all(void)
{
	const unsigned int test_options = PTRACE_O_TRACESYSGOOD |
					  PTRACE_O_TRACEEXEC;
	int pid;
	int it_worked = 0;

	/* Need fork for test. NOMMU has no forks */
	/*Невозможно протестировать в no-MMU-системах*/
	if (NOMMU_SYSTEM)
		goto worked; /* be bold, and pretend that test succeeded */

	pid = fork();//Создаем копию процесса
	if (pid < 0)
		perror_msg_and_die("fork");//Ошибка при fork

	if (pid == 0) {//В ребенке
		pid = getpid();//Запоминаеам свой пид
		if (ptrace(PTRACE_TRACEME, 0L, 0L, 0L) < 0)//Вызываем ptrace(PTRACE_TRACEME
			/* Note: exits with exitcode 1 */
			perror_msg_and_die("%s: PTRACE_TRACEME doesn't work",
					   __func__);
		kill(pid, SIGSTOP);//Останавливаем себя
		_exit(0); /* parent should see entry into this syscall */
	}

	while (1) {//Основной цикл родителя
		int status, tracee_pid;

		errno = 0;
		tracee_pid = wait(&status);//Ждем остановки процесса
		if (tracee_pid <= 0) {
			if (errno == EINTR)
				continue;//Вызов был прерван-- повторяем цикл
			kill_save_errno(pid, SIGKILL);//Убиваем потомка, в случае другой ошибки
			perror_msg_and_die("%s: unexpected wait result %d",
					   __func__, tracee_pid);
		}
		if (WIFEXITED(status)) {//Вышел ли потомок?
			if (WEXITSTATUS(status) == 0)
				break;//Потомок нормально завершил работу
			error_msg_and_die("%s: unexpected exit status %u", //Потомок завершил работу не нормально -- ошибка
					  __func__, WEXITSTATUS(status));
		}
		if (WIFSIGNALED(status)) {//Если потомок завершил работу из-за возникнованеия сигнала- -- ошибка
			error_msg_and_die("%s: unexpected signal %u",
					  __func__, WTERMSIG(status));
		}
		if (!WIFSTOPPED(status)) {//Если потомок не остановлен
			kill(pid, SIGKILL);//Убиваем потомка -- это ошибка
			error_msg_and_die("%s: unexpected wait status %x",
					  __func__, status);
		}
		if (WSTOPSIG(status) == SIGSTOP) {//Потомок остановлен сигналом SIGSTOP -- то, чего мы ожидаем
			/*
			 * We don't check "options aren't accepted" error.
			 * If it happens, we'll never get (SIGTRAP | 0x80),
			 * and thus will decide to not use the option.
			 * IOW: the outcome of the test will be correct.
			 */
			if (ptrace(PTRACE_SETOPTIONS, pid, 0L, test_options) < 0//Пробуем прицепиться установить опции для ptrace
			    && errno != EINVAL && errno != EIO)
				perror_msg("PTRACE_SETOPTIONS");
		}
		if (WSTOPSIG(status) == (SIGTRAP | 0x80)) {//Снова проверяем статус
			it_worked = 1;
		}
		if (ptrace(PTRACE_SYSCALL, pid, 0L, 0L) < 0) {//Пробуем отслеживать системные вызовы потомка
			kill_save_errno(pid, SIGKILL);
			perror_msg_and_die("PTRACE_SYSCALL doesn't work");
		}
	}

	if (it_worked) {//Прошли ли проверки успешно?
 worked:
		syscall_trap_sig = (SIGTRAP | 0x80); //Если да -- устанавливаем значение сигнала
		ptrace_setoptions |= test_options; //Добавляем наши опции к ptrace_setoptions
		if (debug_flag)
			fprintf(stderr, "ptrace_setoptions = %#x\n",
				ptrace_setoptions);
		return 0;
	}

	error_msg("Test for PTRACE_O_TRACESYSGOOD failed, "
		  "giving up using this feature.");
	return 1;
}

#if USE_SEIZE
//Проверяет работу PTRACE_SEIZE
static void
test_ptrace_seize(void)
{
	int pid;

	/* Need fork for test. NOMMU has no forks */
	if (NOMMU_SYSTEM) {
		post_attach_sigstop = 0; /* Это приведет к установке use_seize в 1 */
		return;
	}

	pid = fork();//Создаем копию процесса
	if (pid < 0)
		perror_msg_and_die("fork");//Ошибка

	//Останавливаем потомка и выходим после получения сигнала
	if (pid == 0) {
		pause();
		_exit(0);
	}

	/* PTRACE_SEIZE, unlike ATTACH, doesn't force tracee to trap.  After
	 * attaching tracee continues to run unless a trap condition occurs.
	 * PTRACE_SEIZE doesn't affect signal or group stop state.
	 * PTRACE_SEIZE в отличии от ATTACH не приводит отслеживаемый процесс к попаданию в trap
	 * После присоединения, отслеживаемый процесс продолжит работу, если не возникнет trap-conditions
	 * PTRACE_SEIZE не оказывает влияения на сигналльное состоянии или групповую остановку.
	 */
	if (ptrace(PTRACE_SEIZE, pid, 0, 0) == 0) {
		post_attach_sigstop = 0; /* Это приведет к установке use_seize в 1 */
	} else if (debug_flag) {
		fprintf(stderr, "PTRACE_SEIZE doesn't work\n"); //Проверка провалилась
	}

	kill(pid, SIGKILL); //Убиваем потомка

	while (1) {
		int status, tracee_pid;

		errno = 0;
		tracee_pid = waitpid(pid, &status, 0); //Ожидаем потомка
		if (tracee_pid <= 0) {//Ошибка
			if (errno == EINTR)
				continue;//В случае, если вызов был прерван, производим еще одну итерацию
			perror_msg_and_die("%s: unexpected wait result %d",//Иначе -- возникла ошибка
					 __func__, tracee_pid);
		}
		if (WIFSIGNALED(status)) { //Выходим, если потомок был остановлен из-за возникновения сигнала
			return;
		}
		error_msg_and_die("%s: unexpected wait status %x",
				__func__, status);
	}
}
#else /* !USE_SEIZE */
# define test_ptrace_seize() ((void)0)
#endif

/*Возвращает номер релиза системы*/
static unsigned
get_os_release(void)
{
	unsigned rel;
	const char *p;
	struct utsname u;
	if (uname(&u) < 0)//Пишем релиз в струтуру u
		perror_msg_and_die("uname");
	/* u.release имеет следующую форму: "3.2.9[-some-garbage]" */
	rel = 0;
	p = u.release;
	for (;;) {
		if (!(*p >= '0' && *p <= '9'))//Ошибка в случае неправильного номера релиза
			error_msg_and_die("Bad OS release string: '%s'", u.release);
		/* Note: this open-codes KERNEL_VERSION(): */
		rel = (rel << 8) | atoi(p);//добавляем очередные разряды в rel
		if (rel >= KERNEL_VERSION(1,0,0))
			break;
		while (*p >= '0' && *p <= '9')//Пропускаем нечисловые символы
			p++;
		if (*p != '.') {
			if (rel >= KERNEL_VERSION(0,1,0)) {
				/* "X.Y-something" means "X.Y.0" */
				rel <<= 8;
				break;
			}
			error_msg_and_die("Bad OS release string: '%s'", u.release);
		}
		p++;//Переходим к следующему символу
	}
	return rel;
}

/*
 * Оригинальный комментарий:
 * Initialization part of main() was eating much stack (~0.5k),
 * which was unused after init.
 * We can reuse it if we move init code into a separate function.
 *
 * Don't want main() to inline us and defeat the reason
 * we have a separate function.
 *
 * Инициализация съедает большой размер стека  (~0.5k),
 * который останется неиспользованным после инициализации
 * Для того, чтобы ресурсы не пропадали, инициализация производится
 * в отдельной функции, которая помечается, как noinline
 */
static void __attribute__ ((noinline))
init(int argc, char *argv[])
{
	struct tcb *tcp;
	int c, i;
	int optF = 0;
	struct sigaction sa;

	progname = argv[0] ? argv[0] : "strace"; //Эта переменная используется только в случае, если нужно вывести ошибку

	/* Make sure SIGCHLD has the default action so that waitpid
	   definitely works without losing track of children.  The user
	   should not have given us a bogus state to inherit, but he might
	   have.  Arguably we should detect SIG_IGN here and pass it on
	   to children, but probably noone really needs that.  */
	/* Установка стандартного обработчика на SIGCHLD
	 * Делается с целью правильного отслеживания дочерних процессов.
	 * Отслеживание может нарушиться в случае, если пользователь
	 * каким-то образом даст неправельное состояние наследования
	 * */
	signal(SIGCHLD, SIG_DFL);

	strace_tracer_pid = getpid(); //Запоминаем pid текущего процесса

	os_release = get_os_release(); //Запоминаем версию операционной системы

	/*  Выделение памяти для tcbtab.  */
	tcbtabsize = argc;	/* Для всех возможных -p аргументов*/
	tcbtab = calloc(tcbtabsize, sizeof(tcbtab[0]));
	if (!tcbtab)//Если память не была выделена -- вывод сообщения об ощибке и выход
		die_out_of_memory();
	/*Выделение памяти для tcbtab[i]*/
	tcp = calloc(tcbtabsize, sizeof(*tcp));
	if (!tcp)//Если память не была выделена -- вывод сообщения об ощибке и выход
		die_out_of_memory();
	for (c = 0; c < tcbtabsize; c++)
		tcbtab[c] = tcp++;

	shared_log = stderr;//shared_log инициализируется stderr
	set_sortby(DEFAULT_SORTBY);//установка сортировки в значение по умолчанию (время)
	set_personality(DEFAULT_PERSONALITY);//установка архитектуры в значение по умолчанию
	qualify("trace=all");//Осуществлять отслеживание всего
	qualify("abbrev=all");//Выводить аргументы в виде аббревиатур
	qualify("verbose=all");//Выводить все
#if DEFAULT_QUAL_FLAGS != (QUAL_TRACE | QUAL_ABBREV | QUAL_VERBOSE)
# error Bug in DEFAULT_QUAL_FLAGS
#endif
	qualify("signal=all");//Отслеживание всех сигналов
	//Парсинг опций
	while ((c = getopt(argc, argv,
		"+b:cCdfFhiqrtTvVwxyz"
#ifdef USE_LIBUNWIND
		"k"
#endif
		"D"
		"a:e:o:O:p:s:S:u:E:P:I:")) != EOF) {
		switch (c) {
		case 'b': //Опция -b -- отсоединиться при указанном системном вызове
			if (strcmp(optarg, "execve") != 0)
				error_msg_and_die("Syscall '%s' for -b isn't supported",
					optarg);
			detach_on_execve = 1;
			break;
		case 'c': //Только подсчет параметров всех вызовов и вывод общей информации
			if (cflag == CFLAG_BOTH) {
				error_msg_and_die("-c and -C are mutually exclusive");
			}
			cflag = CFLAG_ONLY_STATS;
			break;
		case 'C': //то же, что и c+постоянный вывод текущей информации
			if (cflag == CFLAG_ONLY_STATS) {
				error_msg_and_die("-c and -C are mutually exclusive");
			}
			cflag = CFLAG_BOTH;
			break;
		case 'd'://Выводить отладочную информацию в stderr
			debug_flag = 1;
			break;
		case 'D'://Флаг того, что процесс strace должен работать, как отсоединенные ребенок, а не как родитель
			daemonized_tracer = 1;
			break;
		case 'F'://То же самое, что и f
			optF = 1;
			break;
		case 'f'://отслеживать потоки, которые появились после вызова fork
			followfork++;
			break;
		case 'h': // вывод справки
			usage(stdout, 0);
			break;
		case 'i'://Вывод значения instruction pointer в момент обращения к системному вызову
			iflag = 1;
			break;
		case 'q': //Не выводить сообщения о присоединении/отсоединении процессов
			qflag++;
			break;
		case 'r'://Печатать относительные таймстампы
			rflag = 1;
			/* fall through to tflag++ */
		case 't'://Абсолютные таймстампы
			tflag++;
			break;
		case 'T'://Выводить время, проведенное в каждом вызове
			Tflag = 1;
			break;
		case 'w'://Вывести суммарную задержку  системного вызова (summarise syscall latency)
			count_wallclock = 1;
			break;
		case 'x'://печатать non-ascii строки в 16-ричном формате
			xflag++;
			break;
		case 'y'://Выводить пути, ассоциированные с аргументами--файловыми дескрипторами
			show_fd_path++;
			break;
		case 'v'://подробный вывод
			qualify("abbrev=none");
			break;
		case 'V'://Вывести версию и выйти
			printf("%s -- version %s\n", PACKAGE_NAME, VERSION);
			exit(0);
			break;
		case 'z'://Опция не описана в Хэлпе
			not_failing_only = 1;
			break;
		case 'a'://Установить ширину выравнивания столбцов при выводе
			acolumn = string_to_uint(optarg);
			if (acolumn < 0)
				error_opt_arg(c, optarg);
			break;
		case 'e'://Строка для модификации флагов в массиве qual_vec option=[!]all or option=[!]val1[,val2]
			qualify(optarg);//Модификация флаго в соответствии со строкой
			break;
		case 'o': //Вывод в файл
			outfname = strdup(optarg);
			break;
		case 'O': //установка оверхеда при отслеживании вызовов в микросекундах
			i = string_to_uint(optarg);
			if (i < 0)
				error_opt_arg(c, optarg);
			set_overhead(i);
			break;
		case 'p'://Производить отслеживание для указанного пида
			process_opt_p_list(optarg);//Парсит значение параметра. Пиды могут записываться группой и иметь различные разделители...
			break;
		case 'P'://Отслеживать доступы к указанному пути
			pathtrace_select(optarg);
			break;
		case 's'://Установка максимальной длины печатаемой строки
			i = string_to_uint(optarg);
			if (i < 0)//Ошибка
				error_opt_arg(c, optarg);
			max_strlen = i;
			break;
		case 'S'://Установить поле, по которому будет производиться сортировка вызовов: time, calls, name, nothing (default time)
			set_sortby(optarg);
			break;
		case 'u'://Запускать команду от имени пользователя
			username = strdup(optarg);
			break;
#ifdef USE_LIBUNWIND
		case 'k':
			stack_trace_enabled = true;
			break;
#endif
		case 'E'://Добавить переменную среды с указанным значением или удалить
			if (putenv(optarg) < 0)
				die_out_of_memory();
			break;
		case 'I': /*  Блокировать указанные сигналы при работе в указанных случаях
					   1: no signals are blocked
					   2: fatal signals are blocked while decoding syscall (default)
					   3: fatal signals are always blocked (default if '-o FILE PROG')
					   4: fatal signals and SIGTSTP (^Z) are always blocked
		 	 	 	 */
			opt_intr = string_to_uint(optarg);
			if (opt_intr <= 0 || opt_intr >= NUM_INTR_OPTS)//Ошибка
				error_opt_arg(c, optarg);
			break;
		default:
			usage(stderr, 1);//Если опция не найдена -- вывести справку
			break;
		}
	}
	argv += optind;//Добавить optind--индекс следующей опции в argv
	/* argc -= optind; - no need, argc is not used below */

	acolumn_spaces = malloc(acolumn + 1);//Выделения памяти для массива с пробелами, который используется для выравнивания колонок
	if (!acolumn_spaces)
		die_out_of_memory();
	memset(acolumn_spaces, ' ', acolumn);//Инициализация массива с пробелами, который используется для выравнивания колонок
	acolumn_spaces[acolumn] = '\0';

	/* Must have PROG [ARGS], or -p PID. Not both. */
	if (!argv[0] == !nprocs)//Ошибка при указании несовместимых аргументов
		usage(stderr, 1);

	if (nprocs != 0 && daemonized_tracer) {//Ошибка при указании несовместимых аргументов
		error_msg_and_die("-D and -p are mutually exclusive");
	}

	//Если опция -f была не указана, а было указано F
	if (!followfork)
		followfork = optF;

	//Ошибка при указании несовместимых аргументов
	if (followfork >= 2 && cflag) {
		error_msg_and_die("(-c or -C) and -ff are mutually exclusive");
	}

	//Ошибка: не указан с, хотя указан w
	if (count_wallclock && !cflag) {
		error_msg_and_die("-w must be given with (-c or -C)");
	}
	//Вывод сообщений о том, что какие-то опции не оказывают ни какого влияния
	if (cflag == CFLAG_ONLY_STATS) {
		if (iflag)
			error_msg("-%c has no effect with -c", 'i');
#ifdef USE_LIBUNWIND
		if (stack_trace_enabled)
			error_msg("-%c has no effect with -c", 'k');
#endif
		if (rflag)
			error_msg("-%c has no effect with -c", 'r');
		if (tflag)
			error_msg("-%c has no effect with -c", 't');
		if (Tflag)
			error_msg("-%c has no effect with -c", 'T');
		if (show_fd_path)
			error_msg("-%c has no effect with -c", 'y');
	}

#ifdef USE_LIBUNWIND
	if (stack_trace_enabled)
		unwind_init();
#endif

	/* Требуется ли запуск от имени другого пользователя?. */
	if (username != NULL) {
		struct passwd *pent;

		if (getuid() != 0 || geteuid() != 0) { //Если требуется и программа запущена не от имени рута--ошибка
			error_msg_and_die("You must be root to use the -u option");
		}
		pent = getpwnam(username);//Ищем указанного пользователя
		if (pent == NULL) {//Если не нашли -- ошибка
			error_msg_and_die("Cannot find user '%s'", username);
		}
		run_uid = pent->pw_uid; //Запуск от имени uid
		run_gid = pent->pw_gid;	//Запуск от имени guid
	}
	else {
		run_uid = getuid(); //Если username не указан -- запускаем от того пользователя, который запустил strace
		run_gid = getgid(); //и от его группы
	}

	/*
	 * On any reasonably recent Linux kernel (circa about 2.5.46)
	 * need_fork_exec_workarounds should stay 0 after these tests:
	 */
	/*need_fork_exec_workarounds = 0; - already is */
	if (followfork)
		need_fork_exec_workarounds = test_ptrace_setoptions_followfork();//Проверяем работу некоторых опций ptrace. В случае успеха вернет 0
	need_fork_exec_workarounds |= test_ptrace_setoptions_for_all(); //Проверяем работу некоторых опций ptrace. В случае успеха вернет 0
	test_ptrace_seize();//Проверяем работу PTRACE_SEIZE

	/* Нужно ли перенаправлять вывод в файл?*/
	if (outfname) {
		/* Если указан pipe */
		if (outfname[0] == '|' || outfname[0] == '!') {//Если параметра начинается с '|' или '!' -- он трактуется, как имя команды, которая будет запущена и stdin которой будет связан с strace, через пайп
			/*
			 * Мы не сможем выводить в файл <outfname>.PID,
			 * если нужно выводить в пайп
			 */
			if (followfork >= 2)//Ошибка
				error_msg_and_die("Piping the output and -ff are mutually exclusive");
			shared_log = strace_popen(outfname + 1);//Открываем лог в случае, если имя выходного файла начинается с '|' или '!'
		}
		else if (followfork < 2)//Открываем лог
			shared_log = strace_fopen(outfname);
	} else {
		/* -ff без -o FILE -- то же самое, что -f */
		if (followfork >= 2)
			followfork = 1;
	}
	//Если не указано имя для файла, если открыт пайп
	if (!outfname || outfname[0] == '|' || outfname[0] == '!') {
		char *buf = malloc(BUFSIZ);//Выделяем память под буфер
		if (!buf)//Ошибка
			die_out_of_memory();
		setvbuf(shared_log, buf, _IOLBF, BUFSIZ);
	}
	//Если указано, что лог нужно сохранять в файл и указано имя программы для запуска
	if (outfname && argv[0]) {
		if (!opt_intr)//Устанавливаем флаг реакции на сигналы -- никода не прерываться, если до этого он не установлен в !0
			opt_intr = INTR_NEVER;
		qflag = 1;//Ставим флаг того, что не нужно выводить сообщения о присоединении/отсоединении процессов
	}
	if (!opt_intr) //Если если до этого opt_intr не установлен в !0
		opt_intr = INTR_WHILE_WAIT;//Ставим значение по умолчанию

	//В целом, opt_intr выбирается по следующему правилу
	/* argv[0]	-pPID	-oFILE	Default interactive setting
	 * yes		  0			0	INTR_WHILE_WAIT
	 * no		  1			0	INTR_WHILE_WAIT
	 * yes		  0			1	INTR_NEVER
	 * no		  1			1	INTR_WHILE_WAIT
	 */

	sigemptyset(&empty_set);//инициализирует набор сигналов empty_set, и "очищает" его от всех сигналов
	sigemptyset(&blocked_set);//инициализирует набор сигналов blocked_set, и "очищает" его от всех сигналов

	/*
	 * startup_child() должна быть вызвана до того, как обработчики сигналов
	 * получат какие-то значения, чтобы эти обработчики не унаследовались порожденным
	 * процессом
	 * Кроме того, какие-то особенные оброботчики нам не требуются, поскольку в процессе работы
	 * startup_child() мы убьем порожденные процессы, если это потребуется в любом случае
	 */
	if (argv[0]) {
		if (!NOMMU_SYSTEM || daemonized_tracer)//Если указана опция -D (NOMMU_SYSTEM в моей системе всегда 0)
			hide_log_until_execve = 1;
		skip_one_b_execve = 1; //Флаг того, что strace вызван как strace PROG  и мы должны скрыть отсоединение при первом вызове execve
		startup_child(argv); //Запуск дочернего процессора
	}
	//Ставим обработчик на SIG_IGN
	sa.sa_handler = SIG_IGN;
	sigemptyset(&sa.sa_mask);//инициализирует набор сигналов, которые должны быть заблокированы в ходе обработке данного и удаляет из них все записи
	sa.sa_flags = 0;
	sigaction(SIGTTOU, &sa, NULL); /* SIG_IGN на SIGTTOU */
	sigaction(SIGTTIN, &sa, NULL); /* SIG_IGN на SIGTTOU*/
	if (opt_intr != INTR_ANYWHERE) {//Если нужно блокировать какие-то сигналы
		if (opt_intr == INTR_BLOCK_TSTP_TOO)//Если нужно блокировать fatal signals и SIGTSTP
			sigaction(SIGTSTP, &sa, NULL); /* SIG_IGN */
		/*
		 * В интерактивном режиме (не использваны опции -o OUTFILE, или -p PID)
		 * Фатальные сигналы блокируются до того, как будет обработано очередное завершение системного вызова
		 * И не блокируются между его обработкой, когда происходит ожидание окончания какого-либо системного вызова
		 * В неинтерактивном режиме сигналы игнорируются
		 */
		if (opt_intr == INTR_WHILE_WAIT) {//Добавляем указанные сигналы в blocked_set, если указана соответсвтующая опция
			sigaddset(&blocked_set, SIGHUP);
			sigaddset(&blocked_set, SIGINT);
			sigaddset(&blocked_set, SIGQUIT);
			sigaddset(&blocked_set, SIGPIPE);
			sigaddset(&blocked_set, SIGTERM);
			sa.sa_handler = interrupt;//Ставим обработчик, который прерывает работу
		}
		/* Ставим обработчики сигналов*/
		sigaction(SIGHUP, &sa, NULL);
		sigaction(SIGINT, &sa, NULL);
		sigaction(SIGQUIT, &sa, NULL);
		sigaction(SIGPIPE, &sa, NULL);
		sigaction(SIGTERM, &sa, NULL);
	}
	if (nprocs != 0 || daemonized_tracer)
		startup_attach();

	/* Нужно ли писать пиды в -o OUTFILE?
	 * -ff: нет (каждый  pid пишет в свой файл);
	 * -f: да (возможно, в будущем появятся новые пиды)
	 * -p PID1,PID2: да (уже сейчас идет работа с несколькими пидами
	 */
	print_pid_pfx = (outfname && followfork < 2 && (followfork == 1 || nprocs > 1));
}
/* Возвращает запись из таблицы пидов, соответствующую указанному pid
 * если запись не найдена -- вернет NULL
*/
static struct tcb *
pid2tcb(int pid)
{
	int i;

	if (pid <= 0)//Неправильный пид
		return NULL;

	for (i = 0; i < tcbtabsize; i++) {//Перебираем записи в таблице
		struct tcb *tcp = tcbtab[i];
		if (tcp->pid == pid)
			return tcp;//Запись найдена
	}

	return NULL;//Запись не найдена
}

//Освобождение ресурсов
static void
cleanup(void)
{
	int i;
	struct tcb *tcp;
	int fatal_sig;

	/* 'interrupted' is a volatile object, fetch it only once */
	fatal_sig = interrupted;
	if (!fatal_sig)//Проверяем, был ли выход вызван установкой interrupted
		fatal_sig = SIGTERM;

	for (i = 0; i < tcbtabsize; i++) {//Убиваем процессы или вызываем для них detach
		tcp = tcbtab[i];
		if (!tcp->pid)//Пид уже обнулен
			continue;
		if (debug_flag)
			fprintf(stderr,
				"cleanup: looking at pid %u\n", tcp->pid);
		if (tcp->pid == strace_child) {//
			kill(tcp->pid, SIGCONT);
			kill(tcp->pid, fatal_sig);
		}
		detach(tcp);
	}
	if (cflag)
		call_summary(shared_log);//Вывод итоговой информации в лог
}
//Установить interrupted
static void
interrupt(int sig)
{
	interrupted = sig;
}


/*Главная функция сбора информации*/
static void
trace(void)
{
	struct rusage ru;

	/* Used to be "while (nprocs != 0)", but in this testcase:
	 *  int main() { _exit(!!fork()); }
	 * under strace -f, parent sometimes (rarely) manages
	 * to exit before we see the first stop of the child,
	 * and we are losing track of it:
	 *  19923 clone(...) = 19924
	 *  19923 exit_group(1)     = ?
	 *  19923 +++ exited with 1 +++
	 * Waiting for ECHILD works better.
	 * (However, if -o|logger is in use, we can't do that.
	 * Can work around that by double-forking the logger,
	 * but that loses the ability to wait for its completion on exit.
	 * Oh well...)
	 */
	while (1) {
		int pid;
		int wait_errno;
		int status, sig;//Для запоминания статуса прерванного процесса и сигнала, который вызвал прерывание
		int stopped;
		struct tcb *tcp;
		unsigned event;

		if (interrupted)//Выход, если был послан сигнал прекращения работы
			return;

		if (popen_pid != 0 && nprocs == 0)//Нет открытых процессов
			return;

		if (interactive)//Установка сигналов, которые могут вызывать остановку процессов на empty_set
			sigprocmask(SIG_SETMASK, &empty_set, NULL);
		pid = wait4(-1, &status, __WALL, (cflag ? &ru : NULL));//-1 -- ожидать любой пид __WALL -- ожидать всех потомков вне зависимости от типа
																//в зависимости о cflags, либо будет запомнена структура ru, либо нет. в ней
																//могут храниться ограничения на ресурсы

		wait_errno = errno;
		if (interactive)//Возвращаем обратно  сигналы
			sigprocmask(SIG_BLOCK, &blocked_set, NULL);

		if (pid < 0) {//Был ли wait завершен без ошибки?
			if (wait_errno == EINTR)//Вызов был прерван -- перходим к следующей итерации
				continue;
			if (nprocs == 0 && wait_errno == ECHILD)//Пид не был возвращен, тк. нет детей
				return;
			/* If nprocs > 0, ECHILD is not expected,
			 * treat it as any other error here:
			 */
			errno = wait_errno;//Ошибка
			perror_msg_and_die("wait4(__WALL)");
		}

		if (pid == popen_pid) {//вызвано прерывание в логгере
			if (!WIFSTOPPED(status))
				popen_pid = 0;//Логгера больше нет. Продолжаем без него
			continue;
		}

		event = ((unsigned)status >> 16);
		if (debug_flag) {//Если ведется дебаг strace
			char buf[sizeof("WIFEXITED,exitcode=%u") + sizeof(int)*3 /*paranoia:*/ + 16];
			char evbuf[sizeof(",EVENT_VFORK_DONE (%u)") + sizeof(int)*3 /*paranoia:*/ + 16];
			strcpy(buf, "???");
			if (WIFSIGNALED(status))//Возник ли в дочернем процессе сигнал, который вызвал его озавершение?
#ifdef WCOREDUMP
				sprintf(buf, "WIFSIGNALED,%ssig=%s",
						WCOREDUMP(status) ? "core," : "",
						signame(WTERMSIG(status)));//Печатаем в буффер информацию о вызвавшем прерывание сигнале
#else
				sprintf(buf, "WIFSIGNALED,sig=%s",
						signame(WTERMSIG(status)));
#endif
			if (WIFEXITED(status))//Если дочерний процесс вышел -- печатаем информацию о коде завершения
				sprintf(buf, "WIFEXITED,exitcode=%u", WEXITSTATUS(status));
			if (WIFSTOPPED(status))//Если дочерний процесс был приостановлен -- печатаем информацию о сигнале, вызвавшем это
				sprintf(buf, "WIFSTOPPED,sig=%s", signame(WSTOPSIG(status)));
#ifdef WIFCONTINUED
			/* Should never be seen */
			if (WIFCONTINUED(status))
				strcpy(buf, "WIFCONTINUED");
#endif
			evbuf[0] = '\0';
			if (event != 0) {//((unsigned)status >> 16) !=0 -- Печатаем в буффер информацию о событии
				static const char *const event_names[] = {
					[PTRACE_EVENT_CLONE] = "CLONE",
					[PTRACE_EVENT_FORK]  = "FORK",
					[PTRACE_EVENT_VFORK] = "VFORK",
					[PTRACE_EVENT_VFORK_DONE] = "VFORK_DONE",
					[PTRACE_EVENT_EXEC]  = "EXEC",
					[PTRACE_EVENT_EXIT]  = "EXIT",
					/* [PTRACE_EVENT_STOP (=128)] would make biggish array */
				};
				const char *e = "??";
				if (event < ARRAY_SIZE(event_names))
					e = event_names[event];
				else if (event == PTRACE_EVENT_STOP)
					e = "STOP";
				sprintf(evbuf, ",EVENT_%s (%u)", e, event);//Печатаем в буффер информацию о событии
			}
			fprintf(stderr, " [wait(0x%06x) = %u] %s%s\n", status, pid, buf, evbuf);//Выводим в stderr отладочную информацию
		}

		/* Ищем пид в таблице */
		tcp = pid2tcb(pid);

		if (!tcp) {//Пид не был найден
			if (!WIFSTOPPED(status)) {
				/* This can happen if we inherited
				 * an unknown child.
				 * Такое может случиться, если был унаследован  потомок, который нам неизвестен
				 * Example:
				 * (sleep 1 & exec strace sleep 2)
				 */
				error_msg("Exit of unknown pid %u seen", pid);//Был остановлен неизвестный потомок
				continue;
			}
			if (followfork) {//Требуется ли отслеживать все порожденные процессы?
				/* We assume it's a fork/vfork/clone child */
				tcp = alloctcb(pid);//Это новый потомок
				tcp->flags |= TCB_ATTACHED | TCB_STARTUP | post_attach_sigstop;//Ставим ему соответствующие флаги
				newoutf(tcp);//Создаем новый выходной файл, если нужно
				if (!qflag)//И выводим информацию, если нужно
					fprintf(stderr, "Process %d attached\n",
						pid);
			} else {
				/* This can happen if a clone call used
				 * CLONE_PTRACE itself.
				 */
				ptrace(PTRACE_CONT, pid, (char *) 0, 0);//Ошибка в случае, если процесс-клон вызвал ptrace с параметром CLONE_PTRACE и своим pid-ом
				error_msg("Stop of unknown pid %u seen, PTRACE_CONTed it", pid);
				continue;
			}
		}
		clear_regs();//Сброс get_regs_error
		if (WIFSTOPPED(status))//Если процесс, в котором возникло прерывание был остановлен
			get_regs(pid);//Запоминаем регистры для pid

		/* Under Linux, execve changes pid to thread leader's pid,
		 * and we see this changed pid on EVENT_EXEC and later,
		 * execve sysexit. Leader "disappears" without exit
		 * notification. Let user know that, drop leader's tcb,
		 * and fix up pid in execve thread's tcb.
		 * Effectively, execve thread's tcb replaces leader's tcb.
		 *
		 * BTW, leader is 'stuck undead' (doesn't report WIFEXITED
		 * on exit syscall) in multithreaded programs exactly
		 * in order to handle this case.
		 *
		 * PTRACE_GETEVENTMSG returns old pid starting from Linux 3.0.
		 * On 2.6 and earlier, it can return garbage.
		 *
		 * В линукс вызов execve изменяет пид процесса на пид ведущего процесса
		 * Поэжтому мы увидим измененный пид в EVENT_EXEC и далее
		 * Процесс-лидер исчезает без сообщения о выходе. Мы даем знать пользователю,
		 * что мы сбрасываем запись о лидере из таблицы пидов
		 * и исправляем пид в таблице пидов процесса, порожденного execve
		 * Проще говоря, таблица пидов execve-потока заменяет оную таблицу процесса-лидера
		 *
		 * Кстати, процесс-лидер превращается в зомби (не сообщает сигнала WIFEXITED)
		 * при вызове системного вызова exit) в многопоточных программах именно для того,
		 * чтобы учесть этот случай.
		 *
		 * PTRACE_GETEVENTMSG возвращает старый пид, начиная с версии ядра 3.0
		 * В 2.6 и более ранних, он может вернуть мусор.
		 */
		if (event == PTRACE_EVENT_EXEC && os_release >= KERNEL_VERSION(3,0,0)) {//Возникло событие PTRACE_EVENT_EXEC в ядре новее, чем 3.0
			FILE *fp;
			struct tcb *execve_thread;
			long old_pid = 0;

			if (ptrace(PTRACE_GETEVENTMSG, pid, NULL, (long) &old_pid) < 0)//Берем информацию о только что возникшем событии
				goto dont_switch_tcbs;//Если при вызове возникла ошибка -- переходим к dont_switch_tcbs
			/* Avoid truncation in pid2tcb() param passing */
			if (old_pid > UINT_MAX)//Чтобы избежать ветвления в таблице пидов
				goto dont_switch_tcbs;//переходим к dont_switch_tcbs
			if (old_pid <= 0 || old_pid == pid)//Старый пид не был установлен или новый пид равен старому
				goto dont_switch_tcbs;//переходим к dont_switch_tcbs
			execve_thread = pid2tcb(old_pid);//Ищем запись об old_pid в таблице
			/* It should be !NULL, but I feel paranoid */
			if (!execve_thread)
				goto dont_switch_tcbs;//Если информации о старом pid нет в таблице--переходим к dont_switch_tcbs

			if (execve_thread->curcol != 0) {
				/*
				 * One case we are here is -ff:
				 * try "strace -oLOG -ff test/threaded_execve"
				 */
				fprintf(execve_thread->outf, " <pid changed to %d ...>\n", pid);
				/*execve_thread->curcol = 0; - no need, see code below */
			}
			/* Swap output FILEs (needed for -ff) */
			/*Меняем местами выходные файлы*/
			fp = execve_thread->outf;
			execve_thread->outf = tcp->outf;
			tcp->outf = fp;
			/* And their column positions */
			/* Номера текущих столбцов так же меняются местами*/
			execve_thread->curcol = tcp->curcol;
			tcp->curcol = 0;
			/* Drop leader, but close execve'd thread outfile (if -ff) */
			/* Убираем запись о лидере, но закрываем выводной файл для execve-треда */
			droptcb(tcp);
			/* Switch to the thread, reusing leader's outfile and pid */
			/*Переключаем треды, используя выводной файл лидера*/
			tcp = execve_thread;
			tcp->pid = pid;
			if (cflag != CFLAG_ONLY_STATS) {//Если дополнительный лог == CFLAG_ONLY_STATS
				printleader(tcp);//Печатаем шапку
				tprintf("+++ superseded by execve in pid %lu +++\n", old_pid);//Печатаем информацию о том, что поток был заморожен при вызове execve
				line_ended();//Начинаем новую строку
				tcp->flags |= TCB_REPRINT;//Флаг того, что нужно снова напечатать шапку
			}
		}

 dont_switch_tcbs:

		if (event == PTRACE_EVENT_EXEC) { //Возникло событие PTRACE_EVENT_EXEC?
			if (detach_on_execve && !skip_one_b_execve)
				detach(tcp); /* Отцепляемся от указанного процесса */
			skip_one_b_execve = 0;//Сбрасываем флаг того, что strace вызван как strace PROG  и мы должны скрыть отсоединение при первом вызове execve
		}

		/* Установка текущего выходного файла */
		current_tcp = tcp;

		if (cflag) {//Если требуется запоминать дополнительную информацию -- делаем это
			tv_sub(&tcp->dtime, &ru.ru_stime, &tcp->stime);
			tcp->stime = ru.ru_stime;
		}

		if (WIFSIGNALED(status)) {//Процесс был засигнален?
			if (pid == strace_child)//strace_child -- Процесс-демон и он был остановлен сигналом
				exit_code = 0x100 | WTERMSIG(status);
			if (cflag != CFLAG_ONLY_STATS//Нужно собирать дополнительную информацию CFLAG_ONLY_STATS
			 && (qual_flags[WTERMSIG(status)] & QUAL_SIGNAL) // И если в массиве флагов, указывающих на то, какие сигналы нужно собирать существует запись ля этого сигнала
			) {
				printleader(tcp);//Печатаем шапку
#ifdef WCOREDUMP
				tprintf("+++ killed by %s %s+++\n", //Сообщаем информацию о том, кто убил дочерний процесс
					signame(WTERMSIG(status)),
					WCOREDUMP(status) ? "(core dumped) " : "");
#else
				tprintf("+++ killed by %s +++\n",
					signame(WTERMSIG(status)));
#endif
				line_ended();
			}
			droptcb(tcp);//Удаляем запись о pid из таблицы
			continue;//Переход к следующей итерации
		}
		if (WIFEXITED(status)) {//Процесс завершился?
			if (pid == strace_child)
				exit_code = WEXITSTATUS(status);//Exit-code -- Exit-code  завершенного процесса
			if (cflag != CFLAG_ONLY_STATS && //Нужно собирать дополнительную информацию CFLAG_ONLY_STATS
			    qflag < 2) {//Не создавался отдельный файл для каждого треда
				printleader(tcp);//Печатаем шапку
				tprintf("+++ exited with %d +++\n", WEXITSTATUS(status));//Сообщаем о завершении процесса
				line_ended();//Переводим строку
			}
			droptcb(tcp);//Удаляем запись о pid из таблиц
			continue;
		}
		if (!WIFSTOPPED(status)) {//Процесс ... но не был остановлен -- паника
			fprintf(stderr, "PANIC: pid %u not stopped\n", pid);
			droptcb(tcp);//Удаляем запись о pid из таблиц
			continue;
		}

		//Этот процесс был остановлен впервые?
		if (tcp->flags & TCB_STARTUP) {
			if (debug_flag)//Сообщаем об инициализации
				fprintf(stderr, "pid %d has TCB_STARTUP, initializing it\n", tcp->pid);
			tcp->flags &= ~TCB_STARTUP;
			if (tcp->flags & TCB_BPTSET) {//Процесс остановился в брейкпоинте после fork?
				if (clearbpt(tcp) < 0) {//Удалось продолжеть процесс после брейкпоинта?
					/* Не удалось -- это фатально */
					droptcb(tcp);//Удаляем запись о процессе из таблице
					exit_code = 1;//Возникла ошибка
					return;
				}
			}

			if (!use_seize && ptrace_setoptions) {//Не используется опция sieze  и ptrace устанавливает не пустые опции процессам?
				if (debug_flag)//Отладочная инф-я
					fprintf(stderr, "setting opts 0x%x on pid %d\n", ptrace_setoptions, tcp->pid);
				if (ptrace(PTRACE_SETOPTIONS, tcp->pid, NULL, ptrace_setoptions) < 0) {//Устанавливаем требуемые опции
					if (errno != ESRCH) {
						/* Should never happen, really */
						perror_msg_and_die("PTRACE_SETOPTIONS");//Возникла ошибка, хотя процесс существует -- умираем
					}
				}
			}
		}

		sig = WSTOPSIG(status);//Процесс остановился из-за возникновения сигнала, если мы добрались досюда

		if (event != 0) {//Возник какой-то ptrace event?
			/* Ptrace event */
#if USE_SEIZE
			if (event == PTRACE_EVENT_STOP) {//STOP-событие?
				/*
				 * PTRACE_INTERRUPT-stop or group-stop.
				 * PTRACE_INTERRUPT-stop has sig == SIGTRAP here.
				 */
				if (sig == SIGSTOP
				 || sig == SIGTSTP
				 || sig == SIGTTIN
				 || sig == SIGTTOU
				) {
					stopped = 1;
					goto show_stopsig;//Выводим сообщение о возникновении SIGSTOP
				}
			}
#endif
			goto restart_tracee_with_sig_0;//Перезапускаем отслеживаемый процесс
		}

		/* Is this post-attach SIGSTOP?
		 * Interestingly, the process may stop
		 * with STOPSIG equal to some other signal
		 * than SIGSTOP if we happend to attach
		 * just before the process takes a signal.
		 *
		 * Был ли это SIGSTOP, вызванный из-за присоединения к нему ptrace?
		 * Интересно, что процесс может остановиться с
		 * STOPSIG, эквивалентным какому-то другому сигналу и следовательно
		 * SIGSTOP, если мы хотели присоединиться к процессу сразу
		 * после того, как он принял сигнал
		 */
		if (sig == SIGSTOP && (tcp->flags & TCB_IGNORE_ONE_SIGSTOP)) {//В процессе возник SIGSTOP и мы должны проигнорировать один SIGSTOP
			if (debug_flag)
				fprintf(stderr, "ignored SIGSTOP on pid %d\n", tcp->pid);//Сообщаем, если нужно
			tcp->flags &= ~TCB_IGNORE_ONE_SIGSTOP;//Убираем флаг
			goto restart_tracee_with_sig_0;//Перезапускаем отслеживаемый процесс
		}
		if (sig != syscall_trap_sig) {//Если не возник trap-сигнал
			siginfo_t si;

			/* Nonzero (true) if tracee is stopped by signal
			 * (as opposed to "tracee received signal").
			 * TOD: shouldn't we check for errno == EINVAL too?
			 * We can get ESRCH instead, you know...
			 */
			stopped = (ptrace(PTRACE_GETSIGINFO, pid, 0, (long) &si) < 0);//True, если отслеживаемый процесс был остановлен сигналом
#if USE_SEIZE
 show_stopsig:
#endif
			if (cflag != CFLAG_ONLY_STATS //Нужно собирать дополнительную инф-ю в соответствии  с CFLAG_ONLY_STATS?
			    && !hide_log_until_execve //И мы не прячем лог
			    && (qual_flags[sig] & QUAL_SIGNAL)//И этот сигнал должжен отслеживаться
			   ) {
				printleader(tcp);//Печатаем шапку
				if (!stopped) {
					tprintf("--- %s ", signame(sig));
					printsiginfo(&si, verbose(tcp));//Выводем информацию о сигнале, если процесс не был остановлен
					tprints(" ---\n");
				} else
					tprintf("--- stopped by %s ---\n",
						signame(sig));//Иначе выводим инф-ю о сигнале, который остановил процесс
				line_ended();//Новая строка
			}

			if (!stopped)//Процесс не остановлен
				/* It's signal-delivery-stop. Inject the signal */
				goto restart_tracee;//Перезапускаем процесс

			/* It's group-stop */
			if (use_seize) {//Групповая остановка?
				/*
				 * This ends ptrace-stop, but does *not* end group-stop.
				 * This makes stopping signals work properly on straced process
				 * (that is, process really stops. It used to continue to run).
				 */
				/*Разблокируем наблюдаемый процесс, но не отменяем групповую остановку
				 * Это позволяет останавливающему сигналу нормельно отработать на
				 * отслеживающих процисаах
				 * (процесс реально остановлен. но вызов приведет к продолжению работы)
				 * */

				if (ptrace_restart(PTRACE_LISTEN, tcp, 0) < 0) {//Разблокируем процесс
					/* Note: ptrace_restart emitted error message */
					exit_code = 1;
					return;
				}
				continue;
			}
			/* We don't have PTRACE_LISTEN support... */
			goto restart_tracee;
		}

		/* We handled quick cases, we are permitted to interrupt now. */
		/* Нужно прервать работу?*/
		if (interrupted)
			return;

		/* This should be syscall entry or exit.
		 * (Or it still can be that pesky post-execve SIGTRAP!)
		 * Handle it.
		 */
		if (trace_syscall(tcp) < 0) {
			/* ptrace() failed in trace_syscall().
			 * Likely a result of process disappearing mid-flight.
			 * Observed case: exit_group() or SIGKILL terminating
			 * all processes in thread group.
			 * We assume that ptrace error was caused by process death.
			 * We used to detach(tcp) here, but since we no longer
			 * implement "detach before death" policy/hack,
			 * we can let this process to report its death to us
			 * normally, via WIFEXITED or WIFSIGNALED wait status.
			 */
			continue;
		}
 restart_tracee_with_sig_0:
		sig = 0;
 restart_tracee:
		if (ptrace_restart(PTRACE_SYSCALL, tcp, sig) < 0) {
			/* Note: ptrace_restart emitted error message */
			exit_code = 1;
			return;
		}
	} /* while (1) */
}

int
main(int argc, char *argv[])
{
	//Инициализация
	init(argc, argv);

	/* Запуск работы программы */
	trace();

	//Освобождение ресурсов
	cleanup();
	fflush(NULL);//Для всех потоков запись всех, еще не записанных данных на диск
	if (shared_log != stderr) //Закрытие shared_log, если он связан не с stderr
		fclose(shared_log);
	if (popen_pid) {//Если был открыт процесс для записи в файл
		while (waitpid(popen_pid, NULL, 0) < 0 && errno == EINTR)//Цикл ожидания завершения процесса popen_pid
			;//Данный цикл продолжается до тех пор, пока waitpid возвращает ошибку EINTR
	}
	if (exit_code > 0xff) {//В случае, если
		/*Чтобы избежать потенцильного удаления файла ядра*/
		/* Avoid potential core file clobbering.  */
		struct_rlimit rlim = {0, 0};
		set_rlimit(RLIMIT_CORE, &rlim);//Размер core dump файлов ставится в 0

		/* Child was killed by a signal, mimic that.  */
		/*Если дочерний процесс был закончен из-за сигнала, это имитируется в главном*/
		exit_code &= 0xff;
		signal(exit_code, SIG_DFL);//Ставится обработчик по умолчанию для сигнала exit_code
		raise(exit_code);//искусственно вызываем сигнал exit_code
		/* Оригинальный комментарий:
		 * Paranoia - what if this signal is not fatal?
		 *  Exit with 128 + signo then.
		 *  Выходим с  signo+exit_code на всякий случай
		  */
		exit_code += 128;
	}

	return exit_code;
}
