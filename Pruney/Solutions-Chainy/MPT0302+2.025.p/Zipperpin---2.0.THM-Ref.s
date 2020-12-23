%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mJpZo9wvOJ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:08 EST 2020

% Result     : Theorem 20.66s
% Output     : Refutation 20.66s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 216 expanded)
%              Number of leaves         :   18 (  72 expanded)
%              Depth                    :   19
%              Number of atoms          :  554 (1828 expanded)
%              Number of equality atoms :   30 ( 140 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_xboole_0 @ X10 @ X12 )
      | ( X10 = X12 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X20 ) )
      | ~ ( r2_hidden @ X18 @ X20 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('19',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ sk_B )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_xboole_0 @ X13 @ X14 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('32',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r2_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','32'])).

thf('34',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_xboole_0 @ X10 @ X12 )
      | ( X10 = X12 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('37',plain,
    ( ( sk_A = sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('41',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['41','55'])).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_xboole_0 @ X13 @ X14 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('58',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mJpZo9wvOJ
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 20.66/20.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 20.66/20.88  % Solved by: fo/fo7.sh
% 20.66/20.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.66/20.88  % done 7382 iterations in 20.465s
% 20.66/20.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 20.66/20.88  % SZS output start Refutation
% 20.66/20.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 20.66/20.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 20.66/20.88  thf(sk_A_type, type, sk_A: $i).
% 20.66/20.88  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 20.66/20.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 20.66/20.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 20.66/20.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 20.66/20.88  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 20.66/20.88  thf(sk_B_type, type, sk_B: $i).
% 20.66/20.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 20.66/20.88  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 20.66/20.88  thf(d3_tarski, axiom,
% 20.66/20.88    (![A:$i,B:$i]:
% 20.66/20.88     ( ( r1_tarski @ A @ B ) <=>
% 20.66/20.88       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 20.66/20.88  thf('0', plain,
% 20.66/20.88      (![X1 : $i, X3 : $i]:
% 20.66/20.88         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 20.66/20.88      inference('cnf', [status(esa)], [d3_tarski])).
% 20.66/20.88  thf(t2_boole, axiom,
% 20.66/20.88    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 20.66/20.88  thf('1', plain,
% 20.66/20.88      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 20.66/20.88      inference('cnf', [status(esa)], [t2_boole])).
% 20.66/20.88  thf(d4_xboole_0, axiom,
% 20.66/20.88    (![A:$i,B:$i,C:$i]:
% 20.66/20.88     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 20.66/20.88       ( ![D:$i]:
% 20.66/20.88         ( ( r2_hidden @ D @ C ) <=>
% 20.66/20.88           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 20.66/20.88  thf('2', plain,
% 20.66/20.88      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 20.66/20.88         (~ (r2_hidden @ X8 @ X7)
% 20.66/20.88          | (r2_hidden @ X8 @ X5)
% 20.66/20.88          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 20.66/20.88      inference('cnf', [status(esa)], [d4_xboole_0])).
% 20.66/20.88  thf('3', plain,
% 20.66/20.88      (![X5 : $i, X6 : $i, X8 : $i]:
% 20.66/20.88         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 20.66/20.88      inference('simplify', [status(thm)], ['2'])).
% 20.66/20.88  thf('4', plain,
% 20.66/20.88      (![X0 : $i, X1 : $i]:
% 20.66/20.88         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 20.66/20.88      inference('sup-', [status(thm)], ['1', '3'])).
% 20.66/20.88  thf('5', plain,
% 20.66/20.88      (![X0 : $i, X1 : $i]:
% 20.66/20.88         ((r1_tarski @ k1_xboole_0 @ X0)
% 20.66/20.88          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X1))),
% 20.66/20.88      inference('sup-', [status(thm)], ['0', '4'])).
% 20.66/20.88  thf('6', plain,
% 20.66/20.88      (![X1 : $i, X3 : $i]:
% 20.66/20.88         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 20.66/20.88      inference('cnf', [status(esa)], [d3_tarski])).
% 20.66/20.88  thf('7', plain,
% 20.66/20.88      (![X0 : $i]:
% 20.66/20.88         ((r1_tarski @ k1_xboole_0 @ X0) | (r1_tarski @ k1_xboole_0 @ X0))),
% 20.66/20.88      inference('sup-', [status(thm)], ['5', '6'])).
% 20.66/20.88  thf('8', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 20.66/20.88      inference('simplify', [status(thm)], ['7'])).
% 20.66/20.88  thf(d8_xboole_0, axiom,
% 20.66/20.88    (![A:$i,B:$i]:
% 20.66/20.88     ( ( r2_xboole_0 @ A @ B ) <=>
% 20.66/20.88       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 20.66/20.88  thf('9', plain,
% 20.66/20.88      (![X10 : $i, X12 : $i]:
% 20.66/20.88         ((r2_xboole_0 @ X10 @ X12)
% 20.66/20.88          | ((X10) = (X12))
% 20.66/20.88          | ~ (r1_tarski @ X10 @ X12))),
% 20.66/20.88      inference('cnf', [status(esa)], [d8_xboole_0])).
% 20.66/20.88  thf('10', plain,
% 20.66/20.88      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 20.66/20.88      inference('sup-', [status(thm)], ['8', '9'])).
% 20.66/20.88  thf('11', plain,
% 20.66/20.88      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 20.66/20.88      inference('sup-', [status(thm)], ['8', '9'])).
% 20.66/20.88  thf(t6_xboole_0, axiom,
% 20.66/20.88    (![A:$i,B:$i]:
% 20.66/20.88     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 20.66/20.88          ( ![C:$i]:
% 20.66/20.88            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 20.66/20.88  thf('12', plain,
% 20.66/20.88      (![X13 : $i, X14 : $i]:
% 20.66/20.88         (~ (r2_xboole_0 @ X13 @ X14)
% 20.66/20.88          | (r2_hidden @ (sk_C_1 @ X14 @ X13) @ X14))),
% 20.66/20.88      inference('cnf', [status(esa)], [t6_xboole_0])).
% 20.66/20.88  thf('13', plain,
% 20.66/20.88      (![X0 : $i]:
% 20.66/20.88         (((k1_xboole_0) = (X0))
% 20.66/20.88          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 20.66/20.88      inference('sup-', [status(thm)], ['11', '12'])).
% 20.66/20.88  thf('14', plain,
% 20.66/20.88      (![X1 : $i, X3 : $i]:
% 20.66/20.88         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 20.66/20.88      inference('cnf', [status(esa)], [d3_tarski])).
% 20.66/20.88  thf('15', plain,
% 20.66/20.88      (![X1 : $i, X3 : $i]:
% 20.66/20.88         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 20.66/20.88      inference('cnf', [status(esa)], [d3_tarski])).
% 20.66/20.88  thf(l54_zfmisc_1, axiom,
% 20.66/20.88    (![A:$i,B:$i,C:$i,D:$i]:
% 20.66/20.88     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 20.66/20.88       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 20.66/20.88  thf('16', plain,
% 20.66/20.88      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 20.66/20.88         ((r2_hidden @ (k4_tarski @ X16 @ X18) @ (k2_zfmisc_1 @ X17 @ X20))
% 20.66/20.88          | ~ (r2_hidden @ X18 @ X20)
% 20.66/20.88          | ~ (r2_hidden @ X16 @ X17))),
% 20.66/20.88      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 20.66/20.88  thf('17', plain,
% 20.66/20.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 20.66/20.88         ((r1_tarski @ X0 @ X1)
% 20.66/20.88          | ~ (r2_hidden @ X3 @ X2)
% 20.66/20.88          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 20.66/20.88             (k2_zfmisc_1 @ X2 @ X0)))),
% 20.66/20.88      inference('sup-', [status(thm)], ['15', '16'])).
% 20.66/20.88  thf('18', plain,
% 20.66/20.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 20.66/20.88         ((r1_tarski @ X0 @ X1)
% 20.66/20.88          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 20.66/20.88             (k2_zfmisc_1 @ X0 @ X2))
% 20.66/20.88          | (r1_tarski @ X2 @ X3))),
% 20.66/20.88      inference('sup-', [status(thm)], ['14', '17'])).
% 20.66/20.88  thf(t114_zfmisc_1, conjecture,
% 20.66/20.88    (![A:$i,B:$i]:
% 20.66/20.88     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 20.66/20.88       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 20.66/20.88         ( ( A ) = ( B ) ) ) ))).
% 20.66/20.88  thf(zf_stmt_0, negated_conjecture,
% 20.66/20.88    (~( ![A:$i,B:$i]:
% 20.66/20.88        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 20.66/20.88          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 20.66/20.88            ( ( A ) = ( B ) ) ) ) )),
% 20.66/20.88    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 20.66/20.88  thf('19', plain,
% 20.66/20.88      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 20.66/20.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.66/20.88  thf('20', plain,
% 20.66/20.88      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 20.66/20.88         ((r2_hidden @ X16 @ X17)
% 20.66/20.88          | ~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ (k2_zfmisc_1 @ X17 @ X19)))),
% 20.66/20.88      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 20.66/20.88  thf('21', plain,
% 20.66/20.88      (![X0 : $i, X1 : $i]:
% 20.66/20.88         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 20.66/20.88          | (r2_hidden @ X1 @ sk_B))),
% 20.66/20.88      inference('sup-', [status(thm)], ['19', '20'])).
% 20.66/20.88  thf('22', plain,
% 20.66/20.88      (![X0 : $i, X1 : $i]:
% 20.66/20.88         ((r1_tarski @ sk_B @ X0)
% 20.66/20.88          | (r1_tarski @ sk_A @ X1)
% 20.66/20.88          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_B))),
% 20.66/20.88      inference('sup-', [status(thm)], ['18', '21'])).
% 20.66/20.88  thf('23', plain,
% 20.66/20.88      (![X1 : $i, X3 : $i]:
% 20.66/20.88         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 20.66/20.88      inference('cnf', [status(esa)], [d3_tarski])).
% 20.66/20.88  thf('24', plain,
% 20.66/20.88      (![X0 : $i]:
% 20.66/20.88         ((r1_tarski @ sk_A @ sk_B)
% 20.66/20.88          | (r1_tarski @ sk_B @ X0)
% 20.66/20.88          | (r1_tarski @ sk_A @ sk_B))),
% 20.66/20.88      inference('sup-', [status(thm)], ['22', '23'])).
% 20.66/20.88  thf('25', plain,
% 20.66/20.88      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | (r1_tarski @ sk_A @ sk_B))),
% 20.66/20.88      inference('simplify', [status(thm)], ['24'])).
% 20.66/20.88  thf('26', plain,
% 20.66/20.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.66/20.88         (~ (r2_hidden @ X0 @ X1)
% 20.66/20.88          | (r2_hidden @ X0 @ X2)
% 20.66/20.88          | ~ (r1_tarski @ X1 @ X2))),
% 20.66/20.88      inference('cnf', [status(esa)], [d3_tarski])).
% 20.66/20.88  thf('27', plain,
% 20.66/20.88      (![X0 : $i, X1 : $i]:
% 20.66/20.88         ((r1_tarski @ sk_A @ sk_B)
% 20.66/20.88          | (r2_hidden @ X1 @ X0)
% 20.66/20.88          | ~ (r2_hidden @ X1 @ sk_B))),
% 20.66/20.88      inference('sup-', [status(thm)], ['25', '26'])).
% 20.66/20.88  thf('28', plain,
% 20.66/20.88      (![X0 : $i]:
% 20.66/20.88         (((k1_xboole_0) = (sk_B))
% 20.66/20.88          | (r2_hidden @ (sk_C_1 @ sk_B @ k1_xboole_0) @ X0)
% 20.66/20.88          | (r1_tarski @ sk_A @ sk_B))),
% 20.66/20.88      inference('sup-', [status(thm)], ['13', '27'])).
% 20.66/20.88  thf('29', plain, (((sk_B) != (k1_xboole_0))),
% 20.66/20.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.66/20.88  thf('30', plain,
% 20.66/20.88      (![X0 : $i]:
% 20.66/20.88         ((r2_hidden @ (sk_C_1 @ sk_B @ k1_xboole_0) @ X0)
% 20.66/20.88          | (r1_tarski @ sk_A @ sk_B))),
% 20.66/20.88      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 20.66/20.88  thf('31', plain,
% 20.66/20.88      (![X13 : $i, X14 : $i]:
% 20.66/20.88         (~ (r2_xboole_0 @ X13 @ X14)
% 20.66/20.88          | ~ (r2_hidden @ (sk_C_1 @ X14 @ X13) @ X13))),
% 20.66/20.88      inference('cnf', [status(esa)], [t6_xboole_0])).
% 20.66/20.88  thf('32', plain,
% 20.66/20.88      (((r1_tarski @ sk_A @ sk_B) | ~ (r2_xboole_0 @ k1_xboole_0 @ sk_B))),
% 20.66/20.88      inference('sup-', [status(thm)], ['30', '31'])).
% 20.66/20.88  thf('33', plain, ((((k1_xboole_0) = (sk_B)) | (r1_tarski @ sk_A @ sk_B))),
% 20.66/20.88      inference('sup-', [status(thm)], ['10', '32'])).
% 20.66/20.88  thf('34', plain, (((sk_B) != (k1_xboole_0))),
% 20.66/20.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.66/20.88  thf('35', plain, ((r1_tarski @ sk_A @ sk_B)),
% 20.66/20.88      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 20.66/20.88  thf('36', plain,
% 20.66/20.88      (![X10 : $i, X12 : $i]:
% 20.66/20.88         ((r2_xboole_0 @ X10 @ X12)
% 20.66/20.88          | ((X10) = (X12))
% 20.66/20.88          | ~ (r1_tarski @ X10 @ X12))),
% 20.66/20.88      inference('cnf', [status(esa)], [d8_xboole_0])).
% 20.66/20.88  thf('37', plain, ((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B))),
% 20.66/20.88      inference('sup-', [status(thm)], ['35', '36'])).
% 20.66/20.88  thf('38', plain, (((sk_A) != (sk_B))),
% 20.66/20.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.66/20.88  thf('39', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 20.66/20.88      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 20.66/20.88  thf('40', plain,
% 20.66/20.88      (![X13 : $i, X14 : $i]:
% 20.66/20.88         (~ (r2_xboole_0 @ X13 @ X14)
% 20.66/20.88          | (r2_hidden @ (sk_C_1 @ X14 @ X13) @ X14))),
% 20.66/20.88      inference('cnf', [status(esa)], [t6_xboole_0])).
% 20.66/20.88  thf('41', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B)),
% 20.66/20.88      inference('sup-', [status(thm)], ['39', '40'])).
% 20.66/20.88  thf('42', plain,
% 20.66/20.88      (![X0 : $i]:
% 20.66/20.88         (((k1_xboole_0) = (X0))
% 20.66/20.88          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 20.66/20.88      inference('sup-', [status(thm)], ['11', '12'])).
% 20.66/20.88  thf('43', plain,
% 20.66/20.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 20.66/20.88         ((r1_tarski @ X0 @ X1)
% 20.66/20.88          | ~ (r2_hidden @ X3 @ X2)
% 20.66/20.88          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 20.66/20.88             (k2_zfmisc_1 @ X2 @ X0)))),
% 20.66/20.88      inference('sup-', [status(thm)], ['15', '16'])).
% 20.66/20.88  thf('44', plain,
% 20.66/20.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.66/20.88         (((k1_xboole_0) = (X0))
% 20.66/20.88          | (r2_hidden @ 
% 20.66/20.88             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 20.66/20.88             (k2_zfmisc_1 @ X0 @ X1))
% 20.66/20.88          | (r1_tarski @ X1 @ X2))),
% 20.66/20.88      inference('sup-', [status(thm)], ['42', '43'])).
% 20.66/20.88  thf('45', plain,
% 20.66/20.88      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 20.66/20.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.66/20.88  thf('46', plain,
% 20.66/20.88      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 20.66/20.88         ((r2_hidden @ X18 @ X19)
% 20.66/20.88          | ~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ (k2_zfmisc_1 @ X17 @ X19)))),
% 20.66/20.88      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 20.66/20.88  thf('47', plain,
% 20.66/20.88      (![X0 : $i, X1 : $i]:
% 20.66/20.88         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 20.66/20.88          | (r2_hidden @ X0 @ sk_A))),
% 20.66/20.88      inference('sup-', [status(thm)], ['45', '46'])).
% 20.66/20.88  thf('48', plain,
% 20.66/20.88      (![X0 : $i]:
% 20.66/20.88         ((r1_tarski @ sk_B @ X0)
% 20.66/20.88          | ((k1_xboole_0) = (sk_A))
% 20.66/20.88          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 20.66/20.88      inference('sup-', [status(thm)], ['44', '47'])).
% 20.66/20.88  thf('49', plain, (((sk_A) != (k1_xboole_0))),
% 20.66/20.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.66/20.88  thf('50', plain,
% 20.66/20.88      (![X0 : $i]:
% 20.66/20.88         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 20.66/20.88      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 20.66/20.88  thf('51', plain,
% 20.66/20.88      (![X1 : $i, X3 : $i]:
% 20.66/20.88         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 20.66/20.88      inference('cnf', [status(esa)], [d3_tarski])).
% 20.66/20.88  thf('52', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 20.66/20.88      inference('sup-', [status(thm)], ['50', '51'])).
% 20.66/20.88  thf('53', plain, ((r1_tarski @ sk_B @ sk_A)),
% 20.66/20.88      inference('simplify', [status(thm)], ['52'])).
% 20.66/20.88  thf('54', plain,
% 20.66/20.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.66/20.88         (~ (r2_hidden @ X0 @ X1)
% 20.66/20.88          | (r2_hidden @ X0 @ X2)
% 20.66/20.88          | ~ (r1_tarski @ X1 @ X2))),
% 20.66/20.88      inference('cnf', [status(esa)], [d3_tarski])).
% 20.66/20.88  thf('55', plain,
% 20.66/20.88      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 20.66/20.88      inference('sup-', [status(thm)], ['53', '54'])).
% 20.66/20.88  thf('56', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)),
% 20.66/20.88      inference('sup-', [status(thm)], ['41', '55'])).
% 20.66/20.88  thf('57', plain,
% 20.66/20.88      (![X13 : $i, X14 : $i]:
% 20.66/20.88         (~ (r2_xboole_0 @ X13 @ X14)
% 20.66/20.88          | ~ (r2_hidden @ (sk_C_1 @ X14 @ X13) @ X13))),
% 20.66/20.88      inference('cnf', [status(esa)], [t6_xboole_0])).
% 20.66/20.88  thf('58', plain, (~ (r2_xboole_0 @ sk_A @ sk_B)),
% 20.66/20.88      inference('sup-', [status(thm)], ['56', '57'])).
% 20.66/20.88  thf('59', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 20.66/20.88      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 20.66/20.88  thf('60', plain, ($false), inference('demod', [status(thm)], ['58', '59'])).
% 20.66/20.88  
% 20.66/20.88  % SZS output end Refutation
% 20.66/20.88  
% 20.66/20.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
