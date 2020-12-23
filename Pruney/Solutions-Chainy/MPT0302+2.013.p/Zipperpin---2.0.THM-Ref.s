%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4Fq69uVw2S

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:07 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 100 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :   18
%              Number of atoms          :  482 ( 873 expanded)
%              Number of equality atoms :   28 (  65 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X7 ) )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ k1_xboole_0 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(condensation,[status(thm)],['13'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X18 ) )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C_1 @ X2 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( k1_xboole_0 = X2 ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

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

thf('18',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(condensation,[status(thm)],['13'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X18 ) )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['30','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4Fq69uVw2S
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.71  % Solved by: fo/fo7.sh
% 0.52/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.71  % done 441 iterations in 0.265s
% 0.52/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.71  % SZS output start Refutation
% 0.52/0.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.52/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.71  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.52/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.71  thf(d3_tarski, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( r1_tarski @ A @ B ) <=>
% 0.52/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.52/0.71  thf('0', plain,
% 0.52/0.71      (![X1 : $i, X3 : $i]:
% 0.52/0.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.71  thf(t2_tarski, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.52/0.71       ( ( A ) = ( B ) ) ))).
% 0.52/0.71  thf('1', plain,
% 0.52/0.71      (![X8 : $i, X9 : $i]:
% 0.52/0.71         (((X9) = (X8))
% 0.52/0.71          | (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 0.52/0.71          | (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X9))),
% 0.52/0.71      inference('cnf', [status(esa)], [t2_tarski])).
% 0.52/0.71  thf(t5_boole, axiom,
% 0.52/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.71  thf('2', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.52/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.52/0.71  thf('3', plain,
% 0.52/0.71      (![X1 : $i, X3 : $i]:
% 0.52/0.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.71  thf(t1_xboole_0, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.52/0.71       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.52/0.71  thf('4', plain,
% 0.52/0.71      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.52/0.71         ((r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X7))
% 0.52/0.71          | (r2_hidden @ X4 @ X5)
% 0.52/0.71          | ~ (r2_hidden @ X4 @ X7))),
% 0.52/0.71      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.52/0.71  thf('5', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         ((r1_tarski @ X0 @ X1)
% 0.52/0.71          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.52/0.71          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k5_xboole_0 @ X2 @ X0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.71  thf('6', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((r2_hidden @ (sk_C @ X1 @ k1_xboole_0) @ X0)
% 0.52/0.71          | (r2_hidden @ (sk_C @ X1 @ k1_xboole_0) @ X0)
% 0.52/0.71          | (r1_tarski @ k1_xboole_0 @ X1))),
% 0.52/0.71      inference('sup+', [status(thm)], ['2', '5'])).
% 0.52/0.71  thf('7', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((r1_tarski @ k1_xboole_0 @ X1)
% 0.52/0.71          | (r2_hidden @ (sk_C @ X1 @ k1_xboole_0) @ X0))),
% 0.52/0.71      inference('simplify', [status(thm)], ['6'])).
% 0.52/0.71  thf('8', plain,
% 0.52/0.71      (![X1 : $i, X3 : $i]:
% 0.52/0.71         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.71  thf('9', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((r1_tarski @ k1_xboole_0 @ X0) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.52/0.71  thf('10', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.52/0.71      inference('simplify', [status(thm)], ['9'])).
% 0.52/0.71  thf('11', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         (~ (r2_hidden @ X0 @ X1)
% 0.52/0.71          | (r2_hidden @ X0 @ X2)
% 0.52/0.71          | ~ (r1_tarski @ X1 @ X2))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.71  thf('12', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.71  thf('13', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.52/0.71          | ((k1_xboole_0) = (X0))
% 0.52/0.71          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['1', '12'])).
% 0.52/0.71  thf('14', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.52/0.71          | ((k1_xboole_0) = (X0)))),
% 0.52/0.71      inference('condensation', [status(thm)], ['13'])).
% 0.52/0.71  thf(l54_zfmisc_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.71     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.52/0.71       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.52/0.71  thf('15', plain,
% 0.52/0.71      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.52/0.71         ((r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X18))
% 0.52/0.71          | ~ (r2_hidden @ X16 @ X18)
% 0.52/0.71          | ~ (r2_hidden @ X14 @ X15))),
% 0.52/0.71      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.52/0.71  thf('16', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         (((k1_xboole_0) = (X0))
% 0.52/0.71          | ~ (r2_hidden @ X2 @ X1)
% 0.52/0.71          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_1 @ X0 @ k1_xboole_0)) @ 
% 0.52/0.71             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.71  thf('17', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         ((r1_tarski @ X0 @ X1)
% 0.52/0.71          | (r2_hidden @ 
% 0.52/0.71             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C_1 @ X2 @ k1_xboole_0)) @ 
% 0.52/0.71             (k2_zfmisc_1 @ X0 @ X2))
% 0.52/0.71          | ((k1_xboole_0) = (X2)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['0', '16'])).
% 0.52/0.71  thf(t114_zfmisc_1, conjecture,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.52/0.71       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.71         ( ( A ) = ( B ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.71    (~( ![A:$i,B:$i]:
% 0.52/0.71        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.52/0.71          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.71            ( ( A ) = ( B ) ) ) ) )),
% 0.52/0.71    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 0.52/0.71  thf('18', plain,
% 0.52/0.71      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('19', plain,
% 0.52/0.71      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.71         ((r2_hidden @ X14 @ X15)
% 0.52/0.71          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X17)))),
% 0.52/0.71      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.52/0.71  thf('20', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.52/0.71          | (r2_hidden @ X1 @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['18', '19'])).
% 0.52/0.71  thf('21', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (((k1_xboole_0) = (sk_B))
% 0.52/0.71          | (r1_tarski @ sk_A @ X0)
% 0.52/0.71          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['17', '20'])).
% 0.52/0.71  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('23', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.52/0.71      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.52/0.71  thf('24', plain,
% 0.52/0.71      (![X1 : $i, X3 : $i]:
% 0.52/0.71         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.71  thf('25', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.71  thf('26', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.52/0.71      inference('simplify', [status(thm)], ['25'])).
% 0.52/0.71  thf(d10_xboole_0, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.71  thf('27', plain,
% 0.52/0.71      (![X10 : $i, X12 : $i]:
% 0.52/0.71         (((X10) = (X12))
% 0.52/0.71          | ~ (r1_tarski @ X12 @ X10)
% 0.52/0.71          | ~ (r1_tarski @ X10 @ X12))),
% 0.52/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.71  thf('28', plain, ((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['26', '27'])).
% 0.52/0.71  thf('29', plain, (((sk_A) != (sk_B))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('30', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.52/0.71      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.52/0.71  thf('31', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.52/0.71          | ((k1_xboole_0) = (X0)))),
% 0.52/0.71      inference('condensation', [status(thm)], ['13'])).
% 0.52/0.71  thf('32', plain,
% 0.52/0.71      (![X1 : $i, X3 : $i]:
% 0.52/0.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.71  thf('33', plain,
% 0.52/0.71      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.52/0.71         ((r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X18))
% 0.52/0.71          | ~ (r2_hidden @ X16 @ X18)
% 0.52/0.71          | ~ (r2_hidden @ X14 @ X15))),
% 0.52/0.71      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.52/0.71  thf('34', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.71         ((r1_tarski @ X0 @ X1)
% 0.52/0.71          | ~ (r2_hidden @ X3 @ X2)
% 0.52/0.71          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.52/0.71             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['32', '33'])).
% 0.52/0.71  thf('35', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         (((k1_xboole_0) = (X0))
% 0.52/0.71          | (r2_hidden @ 
% 0.52/0.71             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 0.52/0.71             (k2_zfmisc_1 @ X0 @ X1))
% 0.52/0.71          | (r1_tarski @ X1 @ X2))),
% 0.52/0.71      inference('sup-', [status(thm)], ['31', '34'])).
% 0.52/0.71  thf('36', plain,
% 0.52/0.71      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('37', plain,
% 0.52/0.71      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.71         ((r2_hidden @ X16 @ X17)
% 0.52/0.71          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X17)))),
% 0.52/0.71      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.52/0.71  thf('38', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.52/0.71          | (r2_hidden @ X0 @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.52/0.71  thf('39', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((r1_tarski @ sk_B @ X0)
% 0.52/0.71          | ((k1_xboole_0) = (sk_A))
% 0.52/0.71          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['35', '38'])).
% 0.52/0.71  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('41', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.52/0.71      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.52/0.71  thf('42', plain,
% 0.52/0.71      (![X1 : $i, X3 : $i]:
% 0.52/0.71         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.71  thf('43', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['41', '42'])).
% 0.52/0.71  thf('44', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.52/0.71      inference('simplify', [status(thm)], ['43'])).
% 0.52/0.71  thf('45', plain, ($false), inference('demod', [status(thm)], ['30', '44'])).
% 0.52/0.71  
% 0.52/0.71  % SZS output end Refutation
% 0.52/0.71  
% 0.52/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
