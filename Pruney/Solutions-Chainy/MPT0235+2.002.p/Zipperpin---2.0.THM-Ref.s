%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KT2FTllz2v

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 107 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :   21
%              Number of atoms          :  756 (1870 expanded)
%              Number of equality atoms :   83 ( 232 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t30_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ( k1_zfmisc_1 @ ( k1_tarski @ A ) )
      = ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_zfmisc_1 @ ( k1_tarski @ A ) )
        = ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_zfmisc_1])).

thf('0',plain,(
    ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) )
 != ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14
        = ( k1_zfmisc_1 @ X11 ) )
      | ( r1_tarski @ ( sk_C @ X14 @ X11 ) @ X11 )
      | ( r2_hidden @ ( sk_C @ X14 @ X11 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16
        = ( k1_tarski @ X15 ) )
      | ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( X1
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( X6 = X5 )
      | ( X6 = X2 )
      | ( X4
       != ( k2_tarski @ X5 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('5',plain,(
    ! [X2: $i,X5: $i,X6: $i] :
      ( ( X6 = X2 )
      | ( X6 = X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_tarski @ X5 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X2 ) ) )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
        = X1 )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = X2 )
      | ( ( k2_tarski @ X0 @ X2 )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ X2 )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != X1 )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ X1 ) @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( ( k2_tarski @ k1_xboole_0 @ X1 )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('12',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14
        = ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ ( sk_C @ X14 @ X11 ) @ X11 )
      | ~ ( r2_hidden @ ( sk_C @ X14 @ X11 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ ( k1_tarski @ X17 ) )
      | ( X16
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('15',plain,(
    ! [X17: $i] :
      ( r1_tarski @ ( k1_tarski @ X17 ) @ ( k1_tarski @ X17 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_tarski @ X0 ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3 != X2 )
      | ( r2_hidden @ X3 @ X4 )
      | ( X4
       != ( k2_tarski @ X5 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('20',plain,(
    ! [X2: $i,X5: $i] :
      ( r2_hidden @ X2 @ ( k2_tarski @ X5 @ X2 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('24',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14
        = ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ ( sk_C @ X14 @ X11 ) @ X11 )
      | ~ ( r2_hidden @ ( sk_C @ X14 @ X11 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ ( k1_tarski @ X17 ) )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('27',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X17 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3 != X5 )
      | ( r2_hidden @ X3 @ X4 )
      | ( X4
       != ( k2_tarski @ X5 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('32',plain,(
    ! [X2: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k2_tarski @ X5 @ X2 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) )
 != ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KT2FTllz2v
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 76 iterations in 0.101s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.55  thf(t30_zfmisc_1, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( k1_zfmisc_1 @ ( k1_tarski @ A ) ) =
% 0.21/0.55       ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( k1_zfmisc_1 @ ( k1_tarski @ A ) ) =
% 0.21/0.55          ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ A ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t30_zfmisc_1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (((k1_zfmisc_1 @ (k1_tarski @ sk_A))
% 0.21/0.55         != (k2_tarski @ k1_xboole_0 @ (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d1_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X11 : $i, X14 : $i]:
% 0.21/0.55         (((X14) = (k1_zfmisc_1 @ X11))
% 0.21/0.55          | (r1_tarski @ (sk_C @ X14 @ X11) @ X11)
% 0.21/0.55          | (r2_hidden @ (sk_C @ X14 @ X11) @ X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.55  thf(l3_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X15 : $i, X16 : $i]:
% 0.21/0.55         (((X16) = (k1_tarski @ X15))
% 0.21/0.55          | ((X16) = (k1_xboole_0))
% 0.21/0.55          | ~ (r1_tarski @ X16 @ (k1_tarski @ X15)))),
% 0.21/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X1)
% 0.21/0.55          | ((X1) = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 0.21/0.55          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 0.21/0.55          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (k1_tarski @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf(d2_tarski, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.55       ( ![D:$i]:
% 0.21/0.55         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X2 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X6 @ X4)
% 0.21/0.55          | ((X6) = (X5))
% 0.21/0.55          | ((X6) = (X2))
% 0.21/0.55          | ((X4) != (k2_tarski @ X5 @ X2)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X2 : $i, X5 : $i, X6 : $i]:
% 0.21/0.55         (((X6) = (X2))
% 0.21/0.55          | ((X6) = (X5))
% 0.21/0.55          | ~ (r2_hidden @ X6 @ (k2_tarski @ X5 @ X2)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((sk_C @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)) = (k1_tarski @ X2))
% 0.21/0.55          | ((sk_C @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)) = (k1_xboole_0))
% 0.21/0.55          | ((k2_tarski @ X1 @ X0) = (k1_zfmisc_1 @ (k1_tarski @ X2)))
% 0.21/0.55          | ((sk_C @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)) = (X1))
% 0.21/0.55          | ((sk_C @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)) = (X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((X0) != (k1_xboole_0))
% 0.21/0.55          | ((sk_C @ (k2_tarski @ X0 @ X2) @ (k1_tarski @ X1)) = (X2))
% 0.21/0.55          | ((k2_tarski @ X0 @ X2) = (k1_zfmisc_1 @ (k1_tarski @ X1)))
% 0.21/0.55          | ((sk_C @ (k2_tarski @ X0 @ X2) @ (k1_tarski @ X1)) = (k1_xboole_0))
% 0.21/0.55          | ((sk_C @ (k2_tarski @ X0 @ X2) @ (k1_tarski @ X1))
% 0.21/0.55              = (k1_tarski @ X1)))),
% 0.21/0.55      inference('eq_fact', [status(thm)], ['6'])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i]:
% 0.21/0.55         (((sk_C @ (k2_tarski @ k1_xboole_0 @ X2) @ (k1_tarski @ X1))
% 0.21/0.55            = (k1_tarski @ X1))
% 0.21/0.55          | ((sk_C @ (k2_tarski @ k1_xboole_0 @ X2) @ (k1_tarski @ X1))
% 0.21/0.55              = (k1_xboole_0))
% 0.21/0.55          | ((k2_tarski @ k1_xboole_0 @ X2) = (k1_zfmisc_1 @ (k1_tarski @ X1)))
% 0.21/0.55          | ((sk_C @ (k2_tarski @ k1_xboole_0 @ X2) @ (k1_tarski @ X1)) = (X2)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k1_tarski @ X0) != (X1))
% 0.21/0.55          | ((sk_C @ (k2_tarski @ k1_xboole_0 @ X1) @ (k1_tarski @ X0)) = (X1))
% 0.21/0.55          | ((k2_tarski @ k1_xboole_0 @ X1) = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 0.21/0.55          | ((sk_C @ (k2_tarski @ k1_xboole_0 @ X1) @ (k1_tarski @ X0))
% 0.21/0.55              = (k1_xboole_0)))),
% 0.21/0.55      inference('eq_fact', [status(thm)], ['8'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.55            (k1_tarski @ X0)) = (k1_xboole_0))
% 0.21/0.55          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.55              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 0.21/0.55          | ((sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.55              (k1_tarski @ X0)) = (k1_tarski @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.55            (k1_tarski @ X0)) = (k1_xboole_0))
% 0.21/0.55          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.55              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 0.21/0.55          | ((sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.55              (k1_tarski @ X0)) = (k1_tarski @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X11 : $i, X14 : $i]:
% 0.21/0.55         (((X14) = (k1_zfmisc_1 @ X11))
% 0.21/0.55          | ~ (r1_tarski @ (sk_C @ X14 @ X11) @ X11)
% 0.21/0.55          | ~ (r2_hidden @ (sk_C @ X14 @ X11) @ X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.21/0.55          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.55              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 0.21/0.55          | ((sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.55              (k1_tarski @ X0)) = (k1_xboole_0))
% 0.21/0.55          | ~ (r2_hidden @ 
% 0.21/0.55               (sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.55                (k1_tarski @ X0)) @ 
% 0.21/0.55               (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 0.21/0.55          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.55              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         ((r1_tarski @ X16 @ (k1_tarski @ X17)) | ((X16) != (k1_tarski @ X17)))),
% 0.21/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X17 : $i]: (r1_tarski @ (k1_tarski @ X17) @ (k1_tarski @ X17))),
% 0.21/0.55      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.55            = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 0.21/0.55          | ((sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.55              (k1_tarski @ X0)) = (k1_xboole_0))
% 0.21/0.55          | ~ (r2_hidden @ 
% 0.21/0.55               (sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.55                (k1_tarski @ X0)) @ 
% 0.21/0.55               (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 0.21/0.56          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['13', '15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r2_hidden @ 
% 0.21/0.56             (sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.56              (k1_tarski @ X0)) @ 
% 0.21/0.56             (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 0.21/0.56          | ((sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.56              (k1_tarski @ X0)) = (k1_xboole_0))
% 0.21/0.56          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r2_hidden @ (k1_tarski @ X0) @ 
% 0.21/0.56             (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 0.21/0.56          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 0.21/0.56          | ((sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.56              (k1_tarski @ X0)) = (k1_xboole_0))
% 0.21/0.56          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 0.21/0.56          | ((sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.56              (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['10', '17'])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         (((X3) != (X2))
% 0.21/0.56          | (r2_hidden @ X3 @ X4)
% 0.21/0.56          | ((X4) != (k2_tarski @ X5 @ X2)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X2 : $i, X5 : $i]: (r2_hidden @ X2 @ (k2_tarski @ X5 @ X2))),
% 0.21/0.56      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56            = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 0.21/0.56          | ((sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.56              (k1_tarski @ X0)) = (k1_xboole_0))
% 0.21/0.56          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 0.21/0.56          | ((sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.56              (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['18', '20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.56            (k1_tarski @ X0)) = (k1_xboole_0))
% 0.21/0.56          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.56            (k1_tarski @ X0)) = (k1_xboole_0))
% 0.21/0.56          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X11 : $i, X14 : $i]:
% 0.21/0.56         (((X14) = (k1_zfmisc_1 @ X11))
% 0.21/0.56          | ~ (r1_tarski @ (sk_C @ X14 @ X11) @ X11)
% 0.21/0.56          | ~ (r2_hidden @ (sk_C @ X14 @ X11) @ X14))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 0.21/0.56          | ~ (r2_hidden @ 
% 0.21/0.56               (sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.56                (k1_tarski @ X0)) @ 
% 0.21/0.56               (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 0.21/0.56          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i]:
% 0.21/0.56         ((r1_tarski @ X16 @ (k1_tarski @ X17)) | ((X16) != (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X17))),
% 0.21/0.56      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56            = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 0.21/0.56          | ~ (r2_hidden @ 
% 0.21/0.56               (sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.56                (k1_tarski @ X0)) @ 
% 0.21/0.56               (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 0.21/0.56          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['25', '27'])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r2_hidden @ 
% 0.21/0.56             (sk_C @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 0.21/0.56              (k1_tarski @ X0)) @ 
% 0.21/0.56             (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 0.21/0.56          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r2_hidden @ k1_xboole_0 @ 
% 0.21/0.56             (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 0.21/0.56          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 0.21/0.56          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['22', '29'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         (((X3) != (X5))
% 0.21/0.56          | (r2_hidden @ X3 @ X4)
% 0.21/0.56          | ((X4) != (k2_tarski @ X5 @ X2)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (![X2 : $i, X5 : $i]: (r2_hidden @ X5 @ (k2_tarski @ X5 @ X2))),
% 0.21/0.56      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56            = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 0.21/0.56          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['30', '32'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56           = (k1_zfmisc_1 @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (((k1_zfmisc_1 @ (k1_tarski @ sk_A))
% 0.21/0.56         != (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['0', '34'])).
% 0.21/0.56  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
