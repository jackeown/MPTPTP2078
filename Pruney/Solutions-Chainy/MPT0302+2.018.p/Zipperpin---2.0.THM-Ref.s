%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ISok3Cz5D0

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:07 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 163 expanded)
%              Number of leaves         :   19 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  492 (1256 expanded)
%              Number of equality atoms :   23 (  96 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X18 ) )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

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

thf('5',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_xboole_0 @ X7 @ X9 )
      | ( X7 = X9 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['19'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('simplify_reflect+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['8','22'])).

thf('24',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_xboole_0 @ X7 @ X9 )
      | ( X7 = X9 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('28',plain,
    ( ( sk_B_1 = sk_A )
    | ( r2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_xboole_0 @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('32',plain,(
    r2_hidden @ ( sk_C_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X18 ) )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('43',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r2_hidden @ ( sk_C_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['32','53'])).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_xboole_0 @ X12 @ X13 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X13 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('56',plain,(
    ~ ( r2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r2_xboole_0 @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ISok3Cz5D0
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 218 iterations in 0.176s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.62  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.42/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.62  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.42/0.62  thf(d1_xboole_0, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.62  thf(d3_tarski, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.42/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      (![X4 : $i, X6 : $i]:
% 0.42/0.62         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf(l54_zfmisc_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.42/0.62       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.42/0.62         ((r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X18))
% 0.42/0.62          | ~ (r2_hidden @ X16 @ X18)
% 0.42/0.62          | ~ (r2_hidden @ X14 @ X15))),
% 0.42/0.62      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.62         ((r1_tarski @ X0 @ X1)
% 0.42/0.62          | ~ (r2_hidden @ X3 @ X2)
% 0.42/0.62          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.42/0.62             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((v1_xboole_0 @ X0)
% 0.42/0.62          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_C @ X2 @ X1)) @ 
% 0.42/0.62             (k2_zfmisc_1 @ X0 @ X1))
% 0.42/0.62          | (r1_tarski @ X1 @ X2))),
% 0.42/0.62      inference('sup-', [status(thm)], ['0', '3'])).
% 0.42/0.62  thf(t114_zfmisc_1, conjecture,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.42/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.42/0.62         ( ( A ) = ( B ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i]:
% 0.42/0.62        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.42/0.62          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.42/0.62            ( ( A ) = ( B ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.62         ((r2_hidden @ X16 @ X17)
% 0.42/0.62          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X17)))),
% 0.42/0.62      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.42/0.62          | (r2_hidden @ X0 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r1_tarski @ sk_B_1 @ X0)
% 0.42/0.62          | (v1_xboole_0 @ sk_A)
% 0.42/0.62          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['4', '7'])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (![X4 : $i, X6 : $i]:
% 0.42/0.62         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.42/0.62  thf(d8_xboole_0, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.42/0.62       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X7 : $i, X9 : $i]:
% 0.42/0.62         ((r2_xboole_0 @ X7 @ X9) | ((X7) = (X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.42/0.62      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | (r2_xboole_0 @ X1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.42/0.62  thf(t6_xboole_0, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.42/0.62          ( ![C:$i]:
% 0.42/0.62            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i]:
% 0.42/0.62         (~ (r2_xboole_0 @ X12 @ X13)
% 0.42/0.62          | (r2_hidden @ (sk_C_2 @ X13 @ X12) @ X13))),
% 0.42/0.62      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((X1) = (X0))
% 0.42/0.62          | ~ (v1_xboole_0 @ X1)
% 0.42/0.62          | (r2_hidden @ (sk_C_2 @ X0 @ X1) @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.62  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((X0) != (k1_xboole_0))
% 0.42/0.62          | ~ (v1_xboole_0 @ sk_A)
% 0.42/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.42/0.62  thf('20', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_A))),
% 0.42/0.62      inference('simplify', [status(thm)], ['19'])).
% 0.42/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.42/0.62  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.62  thf('22', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.42/0.62      inference('simplify_reflect+', [status(thm)], ['20', '21'])).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A) | (r1_tarski @ sk_B_1 @ X0))),
% 0.42/0.62      inference('clc', [status(thm)], ['8', '22'])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (![X4 : $i, X6 : $i]:
% 0.42/0.62         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (((r1_tarski @ sk_B_1 @ sk_A) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.62  thf('26', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.42/0.62      inference('simplify', [status(thm)], ['25'])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (![X7 : $i, X9 : $i]:
% 0.42/0.62         ((r2_xboole_0 @ X7 @ X9) | ((X7) = (X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.42/0.62      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.42/0.62  thf('28', plain, ((((sk_B_1) = (sk_A)) | (r2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.42/0.62  thf('29', plain, (((sk_A) != (sk_B_1))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('30', plain, ((r2_xboole_0 @ sk_B_1 @ sk_A)),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i]:
% 0.42/0.62         (~ (r2_xboole_0 @ X12 @ X13)
% 0.42/0.62          | (r2_hidden @ (sk_C_2 @ X13 @ X12) @ X13))),
% 0.42/0.62      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.42/0.62  thf('32', plain, ((r2_hidden @ (sk_C_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.42/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      (![X4 : $i, X6 : $i]:
% 0.42/0.62         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.42/0.62         ((r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X18))
% 0.42/0.62          | ~ (r2_hidden @ X16 @ X18)
% 0.42/0.62          | ~ (r2_hidden @ X14 @ X15))),
% 0.42/0.62      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((v1_xboole_0 @ X0)
% 0.42/0.62          | ~ (r2_hidden @ X2 @ X1)
% 0.42/0.62          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.42/0.62             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.42/0.62  thf('37', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((r1_tarski @ X0 @ X1)
% 0.42/0.62          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_B @ X2)) @ 
% 0.42/0.62             (k2_zfmisc_1 @ X0 @ X2))
% 0.42/0.62          | (v1_xboole_0 @ X2))),
% 0.42/0.62      inference('sup-', [status(thm)], ['33', '36'])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('39', plain,
% 0.42/0.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.62         ((r2_hidden @ X14 @ X15)
% 0.42/0.62          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X17)))),
% 0.42/0.62      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.42/0.62  thf('40', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.42/0.62          | (r2_hidden @ X1 @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((v1_xboole_0 @ sk_B_1)
% 0.42/0.62          | (r1_tarski @ sk_A @ X0)
% 0.42/0.62          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['37', '40'])).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.62  thf('43', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((X0) != (k1_xboole_0))
% 0.42/0.62          | ~ (v1_xboole_0 @ sk_B_1)
% 0.42/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.42/0.62      inference('simplify', [status(thm)], ['44'])).
% 0.42/0.62  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.62  thf('47', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.42/0.62      inference('simplify_reflect+', [status(thm)], ['45', '46'])).
% 0.42/0.62  thf('48', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_1) | (r1_tarski @ sk_A @ X0))),
% 0.42/0.62      inference('clc', [status(thm)], ['41', '47'])).
% 0.42/0.62  thf('49', plain,
% 0.42/0.62      (![X4 : $i, X6 : $i]:
% 0.42/0.62         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('50', plain,
% 0.42/0.62      (((r1_tarski @ sk_A @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.42/0.62  thf('51', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.42/0.62      inference('simplify', [status(thm)], ['50'])).
% 0.42/0.62  thf('52', plain,
% 0.42/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X3 @ X4)
% 0.42/0.62          | (r2_hidden @ X3 @ X5)
% 0.42/0.62          | ~ (r1_tarski @ X4 @ X5))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('53', plain,
% 0.42/0.62      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['51', '52'])).
% 0.42/0.62  thf('54', plain, ((r2_hidden @ (sk_C_2 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['32', '53'])).
% 0.42/0.62  thf('55', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i]:
% 0.42/0.62         (~ (r2_xboole_0 @ X12 @ X13)
% 0.42/0.62          | ~ (r2_hidden @ (sk_C_2 @ X13 @ X12) @ X12))),
% 0.42/0.62      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.42/0.62  thf('56', plain, (~ (r2_xboole_0 @ sk_B_1 @ sk_A)),
% 0.42/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.42/0.62  thf('57', plain, ((r2_xboole_0 @ sk_B_1 @ sk_A)),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.42/0.62  thf('58', plain, ($false), inference('demod', [status(thm)], ['56', '57'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
