
/* Expand compressed LP programs (in netlib format) to MPS format.
 * This is similar to the Fortran program emps.f , except that it
 * understands command-line arguments, including the -m option,
 * which causes "mystery lines" to be included in the output.
 * ("Mystery lines" allow extensions to MPS format.  At the time of
 * this writing, however, none of the netlib problems contain
 * mystery lines.)
 *
 * Written by David M. Gay of AT&T Bell Laboratories.
 *
 */

#include <stdio.h>
#include <string.h>

#define Void void
#include <stdlib.h>
void badchk(char *buf);
void cantopen(char *);
void colout(char *head, long nz, int what);
void namfetch(int, char s[8]);
void namstore(int, char s[8]);
void process(FILE *, char *infile1);
void scream(char *, char *);
void usage(char **, int rc);

/* Define trtab to make this source self-contained... */
char trtab[] = "!\"#$%&'()*+,-./0123456789;<=>?@\
                ABCDEFGHIJKLMNOPQRSTUVWXYZ[]^_`abcdefghijklmnopqrstuvwxyz{|}~";

char chkbuf[76], *infile, *lastl, *progname, *ss, invtrtab[256];

char *bigstore;
unsigned BSsize;

FILE *inf;
int blanksubst, canend, cn, just1, keepmyst = 1, kmax, ncs, sflag;
long nline, nrow;
char ***xargv;

int main(int argc, char **argv) {
    char *s, *se;
    FILE *f;
    static char *options[] = {
        "-1  {output only 1 nonzero per line}",
        "-b  {replace blanks within names by _'s}",
        "-m  {skip mystery lines}",
        "-S  {split output by problems: put each problem in the file",
        "\tnamed by the first word after \"NAME\" on the NAME line}",
        "-s  {like -S, but force file names to lower case}",
        0};

    for (s = invtrtab, se = s + sizeof(invtrtab); s < se; s++) *s = 92;
    for (s = se = trtab; *s; s++) invtrtab[(unsigned char)*s] = s - se;
    *chkbuf = ' ';

    progname = *argv;
    xargv = &argv;

    while ((s = *++argv))
        if (*s == '-')
            switch(s[1]) {

                case 0: process(stdin, "<stdin>"); break;
                case '1': just1 = 1; break;
                case 'b': blanksubst = '_'; break;
                case 'm': keepmyst = 0; break;
                case 'S': sflag = 1; break;
                case 's': sflag = 2; break;
                case '?': usage(options,0);
                default:
                          fprintf(stderr, "%s: invalid option %s\n", progname, s);
                          usage(options,1);
            }
        else {
            f = fopen(s, "r");
            if (!f) cantopen(s);
            process(f, s);
        }
    if (!infile) process(stdin, "<stdin>");
    return 0;
}

void cantopen(char *s) {
    fprintf(stderr, "%s: can't open %s\n", progname, s);
    exit(1);
}

void usage(char **o, int rc) {
    char *s;

    fprintf(stderr, "Usage: %s [options] [file ...]\nOptions:\n",
            progname);
    while ((s = *o++)) fprintf(stderr, "\t%s\n", s);
    exit(rc);
}

void scream(char *s, char *t) {
    long c;
    fprintf(stderr, "%s: ", progname);
    fprintf(stderr, s, t);
    /* separate computation of c to overcome DeSmet compiler bug */
    c = ftell(inf) - strlen(lastl);
    fprintf(stderr, ": line %ld (char %ld) of %s\n", nline, c, infile);
    exit(1);
}

FILE *newfile(int n) {
    char **av, *s1;
    FILE *f = 0;

    av = *xargv;
    if (*av && (s1 = *++av) && *s1 != '-') {
        fclose(inf);
        f = fopen(s1, "r");
        if (!f) cantopen(s1);
        inf = f;
        infile = s1;
        *xargv = av;
        nline = n;
    }
    return f;
}

char *fname[72];
long fline[72];

#define tr(x) Tr[x]

void early_eof(Void) {
    scream("premature end of file", lastl = "");
}

void checkchar(char *s) {
    int c;
    unsigned int x;
    char *Tr = invtrtab;

    for(x = 0; (c = *s); s++) {
        if (c == '\n')
        { *s = 0; break; }
        c = tr(c);
        if (x & 1)
            x = (x >> 1) + c + 16384;
        else
            x = (x >> 1) + c;
    }
    fname[ncs] = infile;
    fline[ncs] = nline;
    chkbuf[ncs++] = trtab[x % 92];
}

void checkline(FILE *f) {
    char chklin[76];
    canend = 0;
again:
    chkbuf[ncs++] = '\n';
    chkbuf[ncs] = 0;
    nline++;
    while(!fgets(chklin,76,f))
        if (!(f = newfile(1)))
            early_eof();
    if (strcmp(chklin,chkbuf)) {
        if (*chklin == ':' && ncs <= 72) {
            ncs--;
            checkchar(chklin);
            if (keepmyst)
                printf("%s\n",chklin+1);
            goto again;
        }
        badchk(chklin);
    }
    ncs = 1;
}

char *rdline(char s[77]) {
    FILE *f = inf;
again:
    nline++;
    if (!fgets(s, 77, f)) {
        if ((f = newfile(0)))
            goto again;
        if (canend)
            return 0;
        early_eof();
    }
    checkchar(s);
    if (ncs >= 72)
        checkline(f);
    if (*s == ':') {
        if (keepmyst)
            printf("%s\n",s+1);
        goto again;
    }
    return lastl = s;
}

void blankfix(char *s) {
    for(; *s; s++)
        if (*s == ' ')
            *s = blanksubst;
}

int exindx(char **s) {    /* expand supersparse index */
    char *Tr = invtrtab;
    char *z = *s;
    int k, x;

    k = tr((unsigned char)*z++);
    if (k >= 46) scream("exindx: Bad index in %s", z);
    if (k >= 23) x = k - 23;
    else {
        x = k;
        for(;;) {
            k = tr((unsigned char)*z++);
            x = x*46 + k;
            if (k >= 46) { x -= 46; break; }
        }
    }
    *s = z;
    return x;
}

char *exform(char *s0, char **Z) {    /* expand *Z into s0 */
    int ex, k, nd, nelim;
    char *d, db[32], sbuf[32], *s;
    long x, y = 0;
    char *Tr = invtrtab;
    char *z = *Z;

    d = db;
    k = tr((unsigned char)*z++);
    if (k < 46) { /* supersparse index */
        k = exindx(Z);
        if (k > kmax) {
            char msgbuf[64];
            sprintf(msgbuf, "index %u > kmax = %u in %%s", k, kmax);
            scream(msgbuf, z-1);
        }
        return ss + (k << 4);
    }
    s = sbuf;
    k -= 46;
    if (k >= 23) { *s++ = '-'; k -= 23; nelim = 11; }
    else nelim = 12;
    if (k >= 11) { /* integer floating-point */
        k -= 11;
        *d++ = '.';
        if (k >= 6) x = k - 6;
        else {
            x = k;
            for(;;) {
                k = tr((unsigned char)*z++);
                /* x = x*46 + k; */
                x *= 46; x += k; /* two stmts bypass DeSmet bug */
                if (k >= 46) { x -= 46; break; }
            }
        }
        if (!x) *d++ = '0';
        else do {
            *d++ = '0' + x%10;
            x /= 10;
        } while(x);
        do *s++ = *--d; while(d > db);
    }
    else { /* general floating-point */
        ex = (int)tr((unsigned char)*z++) - 50;
        x = tr((unsigned char)*z++);
        while(--k >= 0) {
            if (x >= 100000000) { y = x; x = tr((unsigned char)*z++); }
            /* else x = x*92 + tr(*z++); */
            else { x *= 92; x += tr((unsigned char)*z++); } /* bypass DeSmet bug */
        }
        if (y) {
            while(x > 1) { *d++ = x%10 + '0'; x /= 10; }
            for(;; y /= 10) {
                *d++ = y%10 + '0';
                if (y < 10) break;
            }
        }
        else if (x) for(;; x /= 10) {
            *d++ = x%10 + '0';
            if (x < 10) break;
        }
        else *d++ = '0';
        nd = d - db + ex;
        if (ex > 0) {
            if (nd < nelim || ex < 3) {
                while(d > db) *s++ = *--d;
                do *s++ = '0'; while(--ex);
                *s++ = '.';
            }
            else goto Eout;
        }
        else if (nd >= 0) {
            while(--nd >= 0) *s++ = *--d;
            *s++ = '.';
            while(d > db) *s++ = *--d;
        }
        else if (ex > -nelim) {
            *s++ = '.';
            while(++nd <= 0) *s++ = '0';
            while(d > db) *s++ = *--d;
        }
        else {
Eout:
            ex += d - db - 1;
            if (ex == -10) ex = -9;
            else {
                if (ex > 9 && ex <= d - db + 8) {
                    do { *s++ = *--d;
                    } while (--ex > 9);
                }
                *s++ = *--d;
            }
            *s++ = '.';
            while(d > db) *s++ = *--d;
            *s++ = 'E';
            if (ex < 0) { *s++ = '-'; ex = -ex; }
            while(ex) { *d++ = '0' + ex%10; ex /= 10; }
            while(d > db) *s++ = *--d;
        }
    }
    *s = 0;
    k = s - sbuf;
    s = s0;
    while(k++ < 12) *s++ = ' ';
    strcpy(s, sbuf);
    *Z = z;
    return s0;
}

void newofile(char *buf) {
    unsigned char *s, *t;
    int c;
    char namebuf[80];

    for(s = (unsigned char *)buf + 4; *s <= ' '; s++)
        if (!*s)
            scream("Blank NAME line","");
    t = (unsigned char *)namebuf;
    if (sflag == 2)
        while((c = *s++) > ' ')
            *t++ = c >= 'A' && c <= 'Z' ? c + 'a' - 'A' : c;
    else
        while((c = *s++) > ' ')
            *t++ = c;
    *t = 0;
    if (t < (unsigned char*)namebuf + 75)
        strcpy((char*)t, ".mps");
    if (!freopen(namebuf, "w", stdout))
        scream("can't open \"%s\"", namebuf);
}

void process(FILE *f, char *infile1) {
    char *b1, buf[80], *s, *ss0, *z;
    long ncol, colmx, nz, nrhs, rhsnz, nran, ranz, nbd, bdnz, ns;
    int i;

    infile = infile1;
    inf = f;
    nline = 0;
    canend = 0;
    ncs = 1;
    rdline(buf);
top:
    kmax = -1;
    ncs = 1;

    /* NAME line */

    while (strncmp(buf,"NAME",4))
        if (!rdline(buf))
            goto done;
    canend = 0;
    if (sflag)
        newofile(buf);
    printf("%s\n", buf);
    ncs = 1;

    /* problem statistics */

    rdline(buf);
    if (sscanf(buf,"%ld %ld %ld %ld %ld %ld %ld %ld", &nrow, &ncol,
                &colmx, &nz, &nrhs, &rhsnz, &nran, &ranz) != 8 ||
            rdline(buf), sscanf(buf, "%ld %ld %ld", &nbd, &bdnz, &ns) != 3)
        scream("Bad statistics line:\n%s\n", buf);
    ncs = 1;
    cn = nrow;
    i = cn + ncol;
    if (i != nrow + ncol) scream("Problem too big", "");

    /* read, expand number table */

    BSsize = nrow + ncol;
    ss0 = malloc((unsigned)(ns<<4) + (BSsize<<3));
    bigstore = ss0 + (ns<<4) - 8;
    if (!ss0) scream("malloc failure!","");
    ss = ss0 - 16;
    z = "";
    for(s = ss0, i = ns; i--; s += 16) {
        if (!*z) z = rdline(buf);
        exform(s, &z);
    }
    kmax = ns;

    /* read, print row names */

    b1 = buf + 1;
    for(i = 1; i <= nrow; i++) {
        rdline(buf);
        if (i == 1) printf("ROWS\n");
        if (blanksubst)
            blankfix(b1);
        printf(" %c  %s\n", *buf, b1);
        namstore(i, b1);
    }

    /* read, print columns */

    colout("COLUMNS", nz, 1);

    /* right-hand sides */

    colout("RHS", rhsnz, 2);

    /* ranges */

    colout("RANGES", ranz, 3);

    /* bounds */

    colout("BOUNDS", bdnz, 4);

    /* final checksum line... */

    if (ncs > 1)
        checkline(inf);

    printf("ENDATA\n");

    /* see whether there's another LP in this file... */

    free(ss0);
    canend = ncs = 1;
    if (rdline(buf))
        goto top;
done:
    fclose(inf);
}

void colout(char *head, long nz, int what) {
    static char *bt[] = {"UP", "LO", "FX", "FR", "MI", "PL"},
                fmt2[] = "    %-8.8s  %-8.8s  %-15.15s%-8.8s  %.15s\n";
    char buf[80], curcol[8], msgbuf[32],
    *rc1, *rc2,  rcbuf1[16], rcbuf2[16], rownm[2][8], *z;
    int first, k, n;

    if (!nz) {
        if (what <= 2) printf("%s\n", head);
        return;
    }

    first = 1;
    k = 0;
    z = "";
    *curcol = 0;
    while(nz--) {
        if (!*z) z = rdline(buf);
        if (first) { printf("%s\n", head); first = 0; }
        while(!(n = exindx(&z))) {
            if (k) {
                printf("    %-8.8s  %-8.8s  %.15s\n",
                        curcol, rownm[0], rc1);
                k = 0;
            }
            if (blanksubst) {
                if (*z) {
                    blankfix(z);
                } else {
                    z = head;
                }
            }
            strncpy(curcol, z, 8);
            if (what == 1) namstore(++cn, z);
            z = rdline( buf);
        }
        if (what >= 4) {
            if (n >= 7) {
                sprintf(msgbuf, "bad bound type index = %d",n);
                scream(msgbuf, "");
            }
            if (!*z) z = rdline(buf);
            namfetch((int)nrow + exindx(&z), rownm[0]);
            if (n-- >= 4) {
                printf(" %s %-8.8s  %.8s\n", bt[n],
                        curcol, *rownm);
                continue;
            }
        }
        else namfetch(n, rownm[k]);
        if (!*z) z = rdline(buf);
        if (k) rc2 = exform(rcbuf2, &z);
        else rc1 = exform(rcbuf1, &z);
        if (what <= 3) {
            if (just1)
                printf("    %-8.8s  %-8.8s  %.15s\n",
                        curcol, rownm[0], rc1);
            else {
                if (++k == 1) continue;
                printf(fmt2, curcol, rownm[0], rc1,
                        rownm[1], rc2);
                k = 0;
            }
        }
        else printf(" %s %-8.8s  %-8.8s  %.15s\n", bt[n], curcol,
                rownm[0], rc1);
    }
    if (k) printf("    %-8.8s  %-8.8s  %.15s\n", curcol, *rownm, rc1);
}

void badchk(char *buf) {
    int i;
    static char csl[] = "Check sum line =";
    char *mb = csl, msgbuf[64];

    fprintf(stderr, "%s: Check sum error: expected\n%s\nbut got\n%s\n",
            progname, chkbuf, buf);
    lastl = buf;
    if (*buf == ' ') {
        for(i = 1; chkbuf[i] == buf[i]; i++);
        sprintf(msgbuf, "Bad check sum for line %ld of %s\n%%s",
                fline[i], fname[i]);
        mb = msgbuf;
    }
    scream(mb, csl);
}

static char bmsg[] = "Bad i to %s";

void namstore(int i, char s[8]) {
    if (i <= 0 || i > BSsize) scream(bmsg, "namstore");
    strncpy(bigstore + (i<<3), s, 8);
}

void namfetch(int i, char s[8]) {
    if (i <= 0 || i > BSsize) scream(bmsg, "namfetch");
    strncpy(s, bigstore + (i<<3), 8);
}
