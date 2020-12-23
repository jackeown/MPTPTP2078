%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.crS3nanE5P

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:44 EST 2020

% Result     : Theorem 4.45s
% Output     : Refutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :  127 (1848 expanded)
%              Number of leaves         :   23 ( 537 expanded)
%              Depth                    :   31
%              Number of atoms          : 1194 (22520 expanded)
%              Number of equality atoms :  113 (2389 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(t23_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( C
          = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
       => ( ( ( k1_relat_1 @ C )
            = ( k1_tarski @ A ) )
          & ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( C
            = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
         => ( ( ( k1_relat_1 @ C )
              = ( k1_tarski @ A ) )
            & ( ( k2_relat_1 @ C )
              = ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_relat_1])).

thf('0',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X32: $i] :
      ( ( X32
        = ( k2_relat_1 @ X29 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X32 @ X29 ) @ ( sk_C_1 @ X32 @ X29 ) ) @ X29 )
      | ( r2_hidden @ ( sk_C_1 @ X32 @ X29 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('2',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_tarski @ ( k4_tarski @ X16 @ X17 ) @ ( k4_tarski @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13 = X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_2 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ X0 @ sk_C_2 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ( X7 != X6 ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('13',plain,(
    ! [X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ X0 @ sk_C_2 )
        = sk_B )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C_1 @ X0 @ sk_C_2 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13 = X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = sk_B )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( sk_B != X0 )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(eq_fact,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X29: $i,X32: $i] :
      ( ( X32
        = ( k2_relat_1 @ X29 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X32 @ X29 ) @ ( sk_C_1 @ X32 @ X29 ) ) @ X29 )
      | ( r2_hidden @ ( sk_C_1 @ X32 @ X29 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('20',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_2 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 ) @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(eq_fact,[status(thm)],['27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['18','28'])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( k1_tarski @ ( k4_tarski @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 )
    | ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['0','38'])).

thf('40',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['17'])).

thf('41',plain,(
    ! [X29: $i,X32: $i,X33: $i] :
      ( ( X32
        = ( k2_relat_1 @ X29 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X33 @ ( sk_C_1 @ X32 @ X29 ) ) @ X29 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X32 @ X29 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_2 )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 ) @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(eq_fact,[status(thm)],['27'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_2 )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['39','45'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('47',plain,(
    ! [X22: $i,X25: $i] :
      ( ( X25
        = ( k1_relat_1 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X25 @ X22 ) @ ( sk_D @ X25 @ X22 ) ) @ X22 )
      | ( r2_hidden @ ( sk_C @ X25 @ X22 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('48',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_2 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(eq_fact,[status(thm)],['51'])).

thf('53',plain,(
    ! [X22: $i,X25: $i] :
      ( ( X25
        = ( k1_relat_1 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X25 @ X22 ) @ ( sk_D @ X25 @ X22 ) ) @ X22 )
      | ( r2_hidden @ ( sk_C @ X25 @ X22 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('54',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('56',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 = X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X3 = X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_2 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C @ X0 @ sk_C_2 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ sk_C_2 )
        = sk_A )
      | ( X0
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ X0 @ sk_C_2 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13 = X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = sk_A )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference(eq_fact,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['39','45'])).

thf('69',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['66'])).

thf('70',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != ( k2_relat_1 @ sk_C_2 ) )
   <= ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['66'])).

thf('73',plain,(
    ( k1_relat_1 @ sk_C_2 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['71','72'])).

thf('74',plain,(
    ( k1_relat_1 @ sk_C_2 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['67','73'])).

thf('75',plain,
    ( ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['65','74'])).

thf('76',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['52','75'])).

thf('77',plain,(
    ( k1_relat_1 @ sk_C_2 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['67','73'])).

thf('78',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ ( k1_tarski @ ( k4_tarski @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['46','84'])).

thf('86',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X31 @ X29 ) @ X31 ) @ X29 )
      | ( X30
       != ( k2_relat_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('87',plain,(
    ! [X29: $i,X31: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X31 @ X29 ) @ X31 ) @ X29 )
      | ~ ( r2_hidden @ X31 @ ( k2_relat_1 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_B @ sk_C_2 ) @ sk_B ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_B @ sk_C_2 ) @ sk_B ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['85','87'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_2 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('91',plain,
    ( ( sk_D_3 @ sk_B @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,
    ( ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['65','74'])).

thf('94',plain,(
    ! [X22: $i,X25: $i,X26: $i] :
      ( ( X25
        = ( k1_relat_1 @ X22 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X25 @ X22 ) @ X26 ) @ X22 )
      | ~ ( r2_hidden @ ( sk_C @ X25 @ X22 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 )
      | ~ ( r2_hidden @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['65','74'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 )
      | ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ( k1_relat_1 @ sk_C_2 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['67','73'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 )
      | ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

thf('100',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('101',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference('sup-',[status(thm)],['92','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.crS3nanE5P
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:30:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 4.45/4.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.45/4.65  % Solved by: fo/fo7.sh
% 4.45/4.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.45/4.65  % done 2948 iterations in 4.205s
% 4.45/4.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.45/4.65  % SZS output start Refutation
% 4.45/4.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.45/4.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.45/4.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.45/4.65  thf(sk_A_type, type, sk_A: $i).
% 4.45/4.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.45/4.65  thf(sk_C_2_type, type, sk_C_2: $i).
% 4.45/4.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.45/4.65  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 4.45/4.65  thf(sk_B_type, type, sk_B: $i).
% 4.45/4.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.45/4.65  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 4.45/4.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 4.45/4.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.45/4.65  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 4.45/4.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.45/4.65  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 4.45/4.65  thf(t23_relat_1, conjecture,
% 4.45/4.65    (![A:$i,B:$i,C:$i]:
% 4.45/4.65     ( ( v1_relat_1 @ C ) =>
% 4.45/4.65       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 4.45/4.65         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 4.45/4.65           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 4.45/4.65  thf(zf_stmt_0, negated_conjecture,
% 4.45/4.65    (~( ![A:$i,B:$i,C:$i]:
% 4.45/4.65        ( ( v1_relat_1 @ C ) =>
% 4.45/4.65          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 4.45/4.65            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 4.45/4.65              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 4.45/4.65    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 4.45/4.65  thf('0', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 4.45/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.65  thf(d5_relat_1, axiom,
% 4.45/4.65    (![A:$i,B:$i]:
% 4.45/4.65     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 4.45/4.65       ( ![C:$i]:
% 4.45/4.65         ( ( r2_hidden @ C @ B ) <=>
% 4.45/4.65           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 4.45/4.65  thf('1', plain,
% 4.45/4.65      (![X29 : $i, X32 : $i]:
% 4.45/4.65         (((X32) = (k2_relat_1 @ X29))
% 4.45/4.65          | (r2_hidden @ 
% 4.45/4.65             (k4_tarski @ (sk_D_2 @ X32 @ X29) @ (sk_C_1 @ X32 @ X29)) @ X29)
% 4.45/4.65          | (r2_hidden @ (sk_C_1 @ X32 @ X29) @ X32))),
% 4.45/4.65      inference('cnf', [status(esa)], [d5_relat_1])).
% 4.45/4.65  thf('2', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 4.45/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.65  thf(t36_zfmisc_1, axiom,
% 4.45/4.65    (![A:$i,B:$i,C:$i]:
% 4.45/4.65     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 4.45/4.65         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 4.45/4.65       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 4.45/4.65         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 4.45/4.65  thf('3', plain,
% 4.45/4.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.45/4.65         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k2_tarski @ X17 @ X18))
% 4.45/4.65           = (k2_tarski @ (k4_tarski @ X16 @ X17) @ (k4_tarski @ X16 @ X18)))),
% 4.45/4.65      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 4.45/4.65  thf(t69_enumset1, axiom,
% 4.45/4.65    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.45/4.65  thf('4', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 4.45/4.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.45/4.65  thf('5', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i]:
% 4.45/4.65         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 4.45/4.65           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 4.45/4.65      inference('sup+', [status(thm)], ['3', '4'])).
% 4.45/4.65  thf('6', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 4.45/4.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.45/4.65  thf(t129_zfmisc_1, axiom,
% 4.45/4.65    (![A:$i,B:$i,C:$i,D:$i]:
% 4.45/4.65     ( ( r2_hidden @
% 4.45/4.65         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 4.45/4.65       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 4.45/4.65  thf('7', plain,
% 4.45/4.65      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 4.45/4.65         (((X13) = (X14))
% 4.45/4.65          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 4.45/4.65               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 4.45/4.65      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 4.45/4.65  thf('8', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.45/4.65         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 4.45/4.65             (k2_zfmisc_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 4.45/4.65          | ((X2) = (X0)))),
% 4.45/4.65      inference('sup-', [status(thm)], ['6', '7'])).
% 4.45/4.65  thf('9', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.45/4.65         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 4.45/4.65             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 4.45/4.65          | ((X2) = (X0)))),
% 4.45/4.65      inference('sup-', [status(thm)], ['5', '8'])).
% 4.45/4.65  thf('10', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i]:
% 4.45/4.65         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_2) | ((X0) = (sk_B)))),
% 4.45/4.65      inference('sup-', [status(thm)], ['2', '9'])).
% 4.45/4.65  thf('11', plain,
% 4.45/4.65      (![X0 : $i]:
% 4.45/4.65         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 4.45/4.65          | ((X0) = (k2_relat_1 @ sk_C_2))
% 4.45/4.65          | ((sk_C_1 @ X0 @ sk_C_2) = (sk_B)))),
% 4.45/4.65      inference('sup-', [status(thm)], ['1', '10'])).
% 4.45/4.65  thf(t128_zfmisc_1, axiom,
% 4.45/4.65    (![A:$i,B:$i,C:$i,D:$i]:
% 4.45/4.65     ( ( r2_hidden @
% 4.45/4.65         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 4.45/4.65       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 4.45/4.65  thf('12', plain,
% 4.45/4.65      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 4.45/4.65         ((r2_hidden @ (k4_tarski @ X7 @ X8) @ 
% 4.45/4.65           (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10))
% 4.45/4.65          | ~ (r2_hidden @ X8 @ X10)
% 4.45/4.65          | ((X7) != (X6)))),
% 4.45/4.65      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 4.45/4.65  thf('13', plain,
% 4.45/4.65      (![X6 : $i, X8 : $i, X10 : $i]:
% 4.45/4.65         (~ (r2_hidden @ X8 @ X10)
% 4.45/4.65          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 4.45/4.65             (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10)))),
% 4.45/4.65      inference('simplify', [status(thm)], ['12'])).
% 4.45/4.65  thf('14', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i]:
% 4.45/4.65         (((sk_C_1 @ X0 @ sk_C_2) = (sk_B))
% 4.45/4.65          | ((X0) = (k2_relat_1 @ sk_C_2))
% 4.45/4.65          | (r2_hidden @ (k4_tarski @ X1 @ (sk_C_1 @ X0 @ sk_C_2)) @ 
% 4.45/4.65             (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)))),
% 4.45/4.65      inference('sup-', [status(thm)], ['11', '13'])).
% 4.45/4.65  thf('15', plain,
% 4.45/4.65      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 4.45/4.65         (((X13) = (X14))
% 4.45/4.65          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 4.45/4.65               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 4.45/4.65      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 4.45/4.65  thf('16', plain,
% 4.45/4.65      (![X0 : $i]:
% 4.45/4.65         (((k1_tarski @ X0) = (k2_relat_1 @ sk_C_2))
% 4.45/4.65          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_2) = (sk_B))
% 4.45/4.65          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_2) = (X0)))),
% 4.45/4.65      inference('sup-', [status(thm)], ['14', '15'])).
% 4.45/4.65  thf('17', plain,
% 4.45/4.65      (![X0 : $i]:
% 4.45/4.65         (((sk_B) != (X0))
% 4.45/4.65          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_2) = (X0))
% 4.45/4.65          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_2)))),
% 4.45/4.65      inference('eq_fact', [status(thm)], ['16'])).
% 4.45/4.65  thf('18', plain,
% 4.45/4.65      ((((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2))
% 4.45/4.65        | ((sk_C_1 @ (k1_tarski @ sk_B) @ sk_C_2) = (sk_B)))),
% 4.45/4.65      inference('simplify', [status(thm)], ['17'])).
% 4.45/4.65  thf('19', plain,
% 4.45/4.65      (![X29 : $i, X32 : $i]:
% 4.45/4.65         (((X32) = (k2_relat_1 @ X29))
% 4.45/4.65          | (r2_hidden @ 
% 4.45/4.65             (k4_tarski @ (sk_D_2 @ X32 @ X29) @ (sk_C_1 @ X32 @ X29)) @ X29)
% 4.45/4.65          | (r2_hidden @ (sk_C_1 @ X32 @ X29) @ X32))),
% 4.45/4.65      inference('cnf', [status(esa)], [d5_relat_1])).
% 4.45/4.65  thf('20', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 4.45/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.65  thf('21', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 4.45/4.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.45/4.65  thf('22', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i]:
% 4.45/4.65         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 4.45/4.65           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 4.45/4.65      inference('sup+', [status(thm)], ['3', '4'])).
% 4.45/4.65  thf('23', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i]:
% 4.45/4.65         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 4.45/4.65           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 4.45/4.65      inference('sup+', [status(thm)], ['21', '22'])).
% 4.45/4.65  thf('24', plain,
% 4.45/4.65      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 4.45/4.65         ((r2_hidden @ X8 @ X9)
% 4.45/4.65          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ 
% 4.45/4.65               (k2_zfmisc_1 @ (k1_tarski @ X6) @ X9)))),
% 4.45/4.65      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 4.45/4.65  thf('25', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.45/4.65         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 4.45/4.65             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 4.45/4.65          | (r2_hidden @ X2 @ (k1_tarski @ X0)))),
% 4.45/4.65      inference('sup-', [status(thm)], ['23', '24'])).
% 4.45/4.65  thf('26', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i]:
% 4.45/4.65         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_2)
% 4.45/4.65          | (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 4.45/4.65      inference('sup-', [status(thm)], ['20', '25'])).
% 4.45/4.65  thf('27', plain,
% 4.45/4.65      (![X0 : $i]:
% 4.45/4.65         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 4.45/4.65          | ((X0) = (k2_relat_1 @ sk_C_2))
% 4.45/4.65          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_tarski @ sk_B)))),
% 4.45/4.65      inference('sup-', [status(thm)], ['19', '26'])).
% 4.45/4.65  thf('28', plain,
% 4.45/4.65      (((r2_hidden @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_C_2) @ 
% 4.45/4.65         (k1_tarski @ sk_B))
% 4.45/4.65        | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2)))),
% 4.45/4.65      inference('eq_fact', [status(thm)], ['27'])).
% 4.45/4.65  thf('29', plain,
% 4.45/4.65      (((r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 4.45/4.65        | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2))
% 4.45/4.65        | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2)))),
% 4.45/4.65      inference('sup+', [status(thm)], ['18', '28'])).
% 4.45/4.65  thf('30', plain,
% 4.45/4.65      ((((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2))
% 4.45/4.65        | (r2_hidden @ sk_B @ (k1_tarski @ sk_B)))),
% 4.45/4.65      inference('simplify', [status(thm)], ['29'])).
% 4.45/4.65  thf('31', plain,
% 4.45/4.65      (![X6 : $i, X8 : $i, X10 : $i]:
% 4.45/4.65         (~ (r2_hidden @ X8 @ X10)
% 4.45/4.65          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 4.45/4.65             (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10)))),
% 4.45/4.65      inference('simplify', [status(thm)], ['12'])).
% 4.45/4.65  thf('32', plain,
% 4.45/4.65      (![X0 : $i]:
% 4.45/4.65         (((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2))
% 4.45/4.65          | (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ 
% 4.45/4.65             (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ sk_B))))),
% 4.45/4.65      inference('sup-', [status(thm)], ['30', '31'])).
% 4.45/4.65  thf('33', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i]:
% 4.45/4.65         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 4.45/4.65           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 4.45/4.65      inference('sup+', [status(thm)], ['21', '22'])).
% 4.45/4.65  thf('34', plain,
% 4.45/4.65      (![X0 : $i]:
% 4.45/4.65         (((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2))
% 4.45/4.65          | (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ 
% 4.45/4.65             (k1_tarski @ (k4_tarski @ X0 @ sk_B))))),
% 4.45/4.65      inference('demod', [status(thm)], ['32', '33'])).
% 4.45/4.65  thf('35', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i]:
% 4.45/4.65         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 4.45/4.65           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 4.45/4.65      inference('sup+', [status(thm)], ['21', '22'])).
% 4.45/4.65  thf('36', plain,
% 4.45/4.65      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 4.45/4.65         ((r2_hidden @ X11 @ X12)
% 4.45/4.65          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 4.45/4.65               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 4.45/4.65      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 4.45/4.65  thf('37', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.45/4.65         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 4.45/4.65             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 4.45/4.65          | (r2_hidden @ X3 @ (k1_tarski @ X1)))),
% 4.45/4.65      inference('sup-', [status(thm)], ['35', '36'])).
% 4.45/4.65  thf('38', plain,
% 4.45/4.65      (![X0 : $i]:
% 4.45/4.65         (((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2))
% 4.45/4.65          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 4.45/4.65      inference('sup-', [status(thm)], ['34', '37'])).
% 4.45/4.65  thf('39', plain,
% 4.45/4.65      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_2)
% 4.45/4.65        | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2)))),
% 4.45/4.65      inference('sup+', [status(thm)], ['0', '38'])).
% 4.45/4.65  thf('40', plain,
% 4.45/4.65      ((((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2))
% 4.45/4.65        | ((sk_C_1 @ (k1_tarski @ sk_B) @ sk_C_2) = (sk_B)))),
% 4.45/4.65      inference('simplify', [status(thm)], ['17'])).
% 4.45/4.65  thf('41', plain,
% 4.45/4.65      (![X29 : $i, X32 : $i, X33 : $i]:
% 4.45/4.65         (((X32) = (k2_relat_1 @ X29))
% 4.45/4.65          | ~ (r2_hidden @ (k4_tarski @ X33 @ (sk_C_1 @ X32 @ X29)) @ X29)
% 4.45/4.65          | ~ (r2_hidden @ (sk_C_1 @ X32 @ X29) @ X32))),
% 4.45/4.65      inference('cnf', [status(esa)], [d5_relat_1])).
% 4.45/4.65  thf('42', plain,
% 4.45/4.65      (![X0 : $i]:
% 4.45/4.65         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_2)
% 4.45/4.65          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2))
% 4.45/4.65          | ~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_C_2) @ 
% 4.45/4.65               (k1_tarski @ sk_B))
% 4.45/4.65          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2)))),
% 4.45/4.65      inference('sup-', [status(thm)], ['40', '41'])).
% 4.45/4.65  thf('43', plain,
% 4.45/4.65      (![X0 : $i]:
% 4.45/4.65         (~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_C_2) @ 
% 4.45/4.65             (k1_tarski @ sk_B))
% 4.45/4.65          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2))
% 4.45/4.65          | ~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_2))),
% 4.45/4.65      inference('simplify', [status(thm)], ['42'])).
% 4.45/4.65  thf('44', plain,
% 4.45/4.65      (((r2_hidden @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_C_2) @ 
% 4.45/4.65         (k1_tarski @ sk_B))
% 4.45/4.65        | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2)))),
% 4.45/4.65      inference('eq_fact', [status(thm)], ['27'])).
% 4.45/4.65  thf('45', plain,
% 4.45/4.65      (![X0 : $i]:
% 4.45/4.65         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_2)
% 4.45/4.65          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2)))),
% 4.45/4.65      inference('clc', [status(thm)], ['43', '44'])).
% 4.45/4.65  thf('46', plain, (((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2))),
% 4.45/4.65      inference('clc', [status(thm)], ['39', '45'])).
% 4.45/4.65  thf(d4_relat_1, axiom,
% 4.45/4.65    (![A:$i,B:$i]:
% 4.45/4.65     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 4.45/4.65       ( ![C:$i]:
% 4.45/4.65         ( ( r2_hidden @ C @ B ) <=>
% 4.45/4.65           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 4.45/4.65  thf('47', plain,
% 4.45/4.65      (![X22 : $i, X25 : $i]:
% 4.45/4.65         (((X25) = (k1_relat_1 @ X22))
% 4.45/4.65          | (r2_hidden @ 
% 4.45/4.65             (k4_tarski @ (sk_C @ X25 @ X22) @ (sk_D @ X25 @ X22)) @ X22)
% 4.45/4.65          | (r2_hidden @ (sk_C @ X25 @ X22) @ X25))),
% 4.45/4.65      inference('cnf', [status(esa)], [d4_relat_1])).
% 4.45/4.65  thf('48', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 4.45/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.65  thf('49', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.45/4.65         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 4.45/4.65             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 4.45/4.65          | (r2_hidden @ X3 @ (k1_tarski @ X1)))),
% 4.45/4.65      inference('sup-', [status(thm)], ['35', '36'])).
% 4.45/4.65  thf('50', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i]:
% 4.45/4.65         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_2)
% 4.45/4.65          | (r2_hidden @ X1 @ (k1_tarski @ sk_A)))),
% 4.45/4.65      inference('sup-', [status(thm)], ['48', '49'])).
% 4.45/4.65  thf('51', plain,
% 4.45/4.65      (![X0 : $i]:
% 4.45/4.65         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ X0)
% 4.45/4.65          | ((X0) = (k1_relat_1 @ sk_C_2))
% 4.45/4.65          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ (k1_tarski @ sk_A)))),
% 4.45/4.65      inference('sup-', [status(thm)], ['47', '50'])).
% 4.45/4.65  thf('52', plain,
% 4.45/4.65      (((r2_hidden @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2) @ (k1_tarski @ sk_A))
% 4.45/4.65        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 4.45/4.65      inference('eq_fact', [status(thm)], ['51'])).
% 4.45/4.65  thf('53', plain,
% 4.45/4.65      (![X22 : $i, X25 : $i]:
% 4.45/4.65         (((X25) = (k1_relat_1 @ X22))
% 4.45/4.65          | (r2_hidden @ 
% 4.45/4.65             (k4_tarski @ (sk_C @ X25 @ X22) @ (sk_D @ X25 @ X22)) @ X22)
% 4.45/4.65          | (r2_hidden @ (sk_C @ X25 @ X22) @ X25))),
% 4.45/4.65      inference('cnf', [status(esa)], [d4_relat_1])).
% 4.45/4.65  thf('54', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 4.45/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.65  thf('55', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i]:
% 4.45/4.65         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 4.45/4.65           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 4.45/4.65      inference('sup+', [status(thm)], ['3', '4'])).
% 4.45/4.65  thf('56', plain,
% 4.45/4.65      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 4.45/4.65         (((X7) = (X6))
% 4.45/4.65          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ 
% 4.45/4.65               (k2_zfmisc_1 @ (k1_tarski @ X6) @ X9)))),
% 4.45/4.65      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 4.45/4.65  thf('57', plain,
% 4.45/4.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.45/4.66         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 4.45/4.66             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 4.45/4.66          | ((X3) = (X1)))),
% 4.45/4.66      inference('sup-', [status(thm)], ['55', '56'])).
% 4.45/4.66  thf('58', plain,
% 4.45/4.66      (![X0 : $i, X1 : $i]:
% 4.45/4.66         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_2) | ((X1) = (sk_A)))),
% 4.45/4.66      inference('sup-', [status(thm)], ['54', '57'])).
% 4.45/4.66  thf('59', plain,
% 4.45/4.66      (![X0 : $i]:
% 4.45/4.66         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ X0)
% 4.45/4.66          | ((X0) = (k1_relat_1 @ sk_C_2))
% 4.45/4.66          | ((sk_C @ X0 @ sk_C_2) = (sk_A)))),
% 4.45/4.66      inference('sup-', [status(thm)], ['53', '58'])).
% 4.45/4.66  thf('60', plain,
% 4.45/4.66      (![X6 : $i, X8 : $i, X10 : $i]:
% 4.45/4.66         (~ (r2_hidden @ X8 @ X10)
% 4.45/4.66          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 4.45/4.66             (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10)))),
% 4.45/4.66      inference('simplify', [status(thm)], ['12'])).
% 4.45/4.66  thf('61', plain,
% 4.45/4.66      (![X0 : $i, X1 : $i]:
% 4.45/4.66         (((sk_C @ X0 @ sk_C_2) = (sk_A))
% 4.45/4.66          | ((X0) = (k1_relat_1 @ sk_C_2))
% 4.45/4.66          | (r2_hidden @ (k4_tarski @ X1 @ (sk_C @ X0 @ sk_C_2)) @ 
% 4.45/4.66             (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)))),
% 4.45/4.66      inference('sup-', [status(thm)], ['59', '60'])).
% 4.45/4.66  thf('62', plain,
% 4.45/4.66      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 4.45/4.66         (((X13) = (X14))
% 4.45/4.66          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 4.45/4.66               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 4.45/4.66      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 4.45/4.66  thf('63', plain,
% 4.45/4.66      (![X0 : $i]:
% 4.45/4.66         (((k1_tarski @ X0) = (k1_relat_1 @ sk_C_2))
% 4.45/4.66          | ((sk_C @ (k1_tarski @ X0) @ sk_C_2) = (sk_A))
% 4.45/4.66          | ((sk_C @ (k1_tarski @ X0) @ sk_C_2) = (X0)))),
% 4.45/4.66      inference('sup-', [status(thm)], ['61', '62'])).
% 4.45/4.66  thf('64', plain,
% 4.45/4.66      (![X0 : $i]:
% 4.45/4.66         (((X0) != (sk_A))
% 4.45/4.66          | ((sk_C @ (k1_tarski @ X0) @ sk_C_2) = (sk_A))
% 4.45/4.66          | ((k1_tarski @ X0) = (k1_relat_1 @ sk_C_2)))),
% 4.45/4.66      inference('eq_fact', [status(thm)], ['63'])).
% 4.45/4.66  thf('65', plain,
% 4.45/4.66      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 4.45/4.66        | ((sk_C @ (k1_tarski @ sk_A) @ sk_C_2) = (sk_A)))),
% 4.45/4.66      inference('simplify', [status(thm)], ['64'])).
% 4.45/4.66  thf('66', plain,
% 4.45/4.66      ((((k1_relat_1 @ sk_C_2) != (k1_tarski @ sk_A))
% 4.45/4.66        | ((k2_relat_1 @ sk_C_2) != (k1_tarski @ sk_B)))),
% 4.45/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.66  thf('67', plain,
% 4.45/4.66      ((((k1_relat_1 @ sk_C_2) != (k1_tarski @ sk_A)))
% 4.45/4.66         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 4.45/4.66      inference('split', [status(esa)], ['66'])).
% 4.45/4.66  thf('68', plain, (((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2))),
% 4.45/4.66      inference('clc', [status(thm)], ['39', '45'])).
% 4.45/4.66  thf('69', plain,
% 4.45/4.66      ((((k2_relat_1 @ sk_C_2) != (k1_tarski @ sk_B)))
% 4.45/4.66         <= (~ (((k2_relat_1 @ sk_C_2) = (k1_tarski @ sk_B))))),
% 4.45/4.66      inference('split', [status(esa)], ['66'])).
% 4.45/4.66  thf('70', plain,
% 4.45/4.66      ((((k2_relat_1 @ sk_C_2) != (k2_relat_1 @ sk_C_2)))
% 4.45/4.66         <= (~ (((k2_relat_1 @ sk_C_2) = (k1_tarski @ sk_B))))),
% 4.45/4.66      inference('sup-', [status(thm)], ['68', '69'])).
% 4.45/4.66  thf('71', plain, ((((k2_relat_1 @ sk_C_2) = (k1_tarski @ sk_B)))),
% 4.45/4.66      inference('simplify', [status(thm)], ['70'])).
% 4.45/4.66  thf('72', plain,
% 4.45/4.66      (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))) | 
% 4.45/4.66       ~ (((k2_relat_1 @ sk_C_2) = (k1_tarski @ sk_B)))),
% 4.45/4.66      inference('split', [status(esa)], ['66'])).
% 4.45/4.66  thf('73', plain, (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A)))),
% 4.45/4.66      inference('sat_resolution*', [status(thm)], ['71', '72'])).
% 4.45/4.66  thf('74', plain, (((k1_relat_1 @ sk_C_2) != (k1_tarski @ sk_A))),
% 4.45/4.66      inference('simpl_trail', [status(thm)], ['67', '73'])).
% 4.45/4.66  thf('75', plain, (((sk_C @ (k1_tarski @ sk_A) @ sk_C_2) = (sk_A))),
% 4.45/4.66      inference('simplify_reflect-', [status(thm)], ['65', '74'])).
% 4.45/4.66  thf('76', plain,
% 4.45/4.66      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 4.45/4.66        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 4.45/4.66      inference('demod', [status(thm)], ['52', '75'])).
% 4.45/4.66  thf('77', plain, (((k1_relat_1 @ sk_C_2) != (k1_tarski @ sk_A))),
% 4.45/4.66      inference('simpl_trail', [status(thm)], ['67', '73'])).
% 4.45/4.66  thf('78', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_A))),
% 4.45/4.66      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 4.45/4.66  thf('79', plain,
% 4.45/4.66      (![X6 : $i, X8 : $i, X10 : $i]:
% 4.45/4.66         (~ (r2_hidden @ X8 @ X10)
% 4.45/4.66          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 4.45/4.66             (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10)))),
% 4.45/4.66      inference('simplify', [status(thm)], ['12'])).
% 4.45/4.66  thf('80', plain,
% 4.45/4.66      (![X0 : $i]:
% 4.45/4.66         (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ 
% 4.45/4.66          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 4.45/4.66      inference('sup-', [status(thm)], ['78', '79'])).
% 4.45/4.66  thf('81', plain,
% 4.45/4.66      (![X0 : $i, X1 : $i]:
% 4.45/4.66         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 4.45/4.66           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 4.45/4.66      inference('sup+', [status(thm)], ['21', '22'])).
% 4.45/4.66  thf('82', plain,
% 4.45/4.66      (![X0 : $i]:
% 4.45/4.66         (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ 
% 4.45/4.66          (k1_tarski @ (k4_tarski @ X0 @ sk_A)))),
% 4.45/4.66      inference('demod', [status(thm)], ['80', '81'])).
% 4.45/4.66  thf('83', plain,
% 4.45/4.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.45/4.66         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 4.45/4.66             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 4.45/4.66          | (r2_hidden @ X3 @ (k1_tarski @ X1)))),
% 4.45/4.66      inference('sup-', [status(thm)], ['35', '36'])).
% 4.45/4.66  thf('84', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.45/4.66      inference('sup-', [status(thm)], ['82', '83'])).
% 4.45/4.66  thf('85', plain, ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 4.45/4.66      inference('sup+', [status(thm)], ['46', '84'])).
% 4.45/4.66  thf('86', plain,
% 4.45/4.66      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.45/4.66         (~ (r2_hidden @ X31 @ X30)
% 4.45/4.66          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X31 @ X29) @ X31) @ X29)
% 4.45/4.66          | ((X30) != (k2_relat_1 @ X29)))),
% 4.45/4.66      inference('cnf', [status(esa)], [d5_relat_1])).
% 4.45/4.66  thf('87', plain,
% 4.45/4.66      (![X29 : $i, X31 : $i]:
% 4.45/4.66         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X31 @ X29) @ X31) @ X29)
% 4.45/4.66          | ~ (r2_hidden @ X31 @ (k2_relat_1 @ X29)))),
% 4.45/4.66      inference('simplify', [status(thm)], ['86'])).
% 4.45/4.66  thf('88', plain,
% 4.45/4.66      ((r2_hidden @ (k4_tarski @ (sk_D_3 @ sk_B @ sk_C_2) @ sk_B) @ sk_C_2)),
% 4.45/4.66      inference('sup-', [status(thm)], ['85', '87'])).
% 4.45/4.66  thf('89', plain,
% 4.45/4.66      ((r2_hidden @ (k4_tarski @ (sk_D_3 @ sk_B @ sk_C_2) @ sk_B) @ sk_C_2)),
% 4.45/4.66      inference('sup-', [status(thm)], ['85', '87'])).
% 4.45/4.66  thf('90', plain,
% 4.45/4.66      (![X0 : $i, X1 : $i]:
% 4.45/4.66         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_2) | ((X1) = (sk_A)))),
% 4.45/4.66      inference('sup-', [status(thm)], ['54', '57'])).
% 4.45/4.66  thf('91', plain, (((sk_D_3 @ sk_B @ sk_C_2) = (sk_A))),
% 4.45/4.66      inference('sup-', [status(thm)], ['89', '90'])).
% 4.45/4.66  thf('92', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_2)),
% 4.45/4.66      inference('demod', [status(thm)], ['88', '91'])).
% 4.45/4.66  thf('93', plain, (((sk_C @ (k1_tarski @ sk_A) @ sk_C_2) = (sk_A))),
% 4.45/4.66      inference('simplify_reflect-', [status(thm)], ['65', '74'])).
% 4.45/4.66  thf('94', plain,
% 4.45/4.66      (![X22 : $i, X25 : $i, X26 : $i]:
% 4.45/4.66         (((X25) = (k1_relat_1 @ X22))
% 4.45/4.66          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X25 @ X22) @ X26) @ X22)
% 4.45/4.66          | ~ (r2_hidden @ (sk_C @ X25 @ X22) @ X25))),
% 4.45/4.66      inference('cnf', [status(esa)], [d4_relat_1])).
% 4.45/4.66  thf('95', plain,
% 4.45/4.66      (![X0 : $i]:
% 4.45/4.66         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2)
% 4.45/4.66          | ~ (r2_hidden @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2) @ 
% 4.45/4.66               (k1_tarski @ sk_A))
% 4.45/4.66          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 4.45/4.66      inference('sup-', [status(thm)], ['93', '94'])).
% 4.45/4.66  thf('96', plain, (((sk_C @ (k1_tarski @ sk_A) @ sk_C_2) = (sk_A))),
% 4.45/4.66      inference('simplify_reflect-', [status(thm)], ['65', '74'])).
% 4.45/4.66  thf('97', plain,
% 4.45/4.66      (![X0 : $i]:
% 4.45/4.66         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2)
% 4.45/4.66          | ~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 4.45/4.66          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 4.45/4.66      inference('demod', [status(thm)], ['95', '96'])).
% 4.45/4.66  thf('98', plain, (((k1_relat_1 @ sk_C_2) != (k1_tarski @ sk_A))),
% 4.45/4.66      inference('simpl_trail', [status(thm)], ['67', '73'])).
% 4.45/4.66  thf('99', plain,
% 4.45/4.66      (![X0 : $i]:
% 4.45/4.66         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2)
% 4.45/4.66          | ~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 4.45/4.66      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 4.45/4.66  thf('100', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_A))),
% 4.45/4.66      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 4.45/4.66  thf('101', plain,
% 4.45/4.66      (![X0 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2)),
% 4.45/4.66      inference('demod', [status(thm)], ['99', '100'])).
% 4.45/4.66  thf('102', plain, ($false), inference('sup-', [status(thm)], ['92', '101'])).
% 4.45/4.66  
% 4.45/4.66  % SZS output end Refutation
% 4.45/4.66  
% 4.45/4.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
