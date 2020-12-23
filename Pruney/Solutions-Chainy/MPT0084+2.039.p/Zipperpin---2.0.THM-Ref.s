%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SD7Efjtu4R

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:24 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 108 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :   20
%              Number of atoms          :  496 ( 764 expanded)
%              Number of equality atoms :   55 (  80 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','21'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('30',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('37',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['7','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['44','53'])).

thf('55',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SD7Efjtu4R
% 0.15/0.34  % Computer   : n012.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 20:45:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 254 iterations in 0.112s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.57  thf(t77_xboole_1, conjecture,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.39/0.57          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.57        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.39/0.57             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.39/0.57  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(l32_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X3 : $i, X5 : $i]:
% 0.39/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.39/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.57  thf('3', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf(t48_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X20 : $i, X21 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.39/0.57           = (k3_xboole_0 @ X20 @ X21))),
% 0.39/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.39/0.57      inference('sup+', [status(thm)], ['3', '4'])).
% 0.39/0.57  thf(t3_boole, axiom,
% 0.39/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.57  thf('6', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.57  thf('7', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.39/0.57      inference('demod', [status(thm)], ['5', '6'])).
% 0.39/0.57  thf('8', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(d7_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.39/0.57       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf(t47_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X18 : $i, X19 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 0.39/0.57           = (k4_xboole_0 @ X18 @ X19))),
% 0.39/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.39/0.57         = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['10', '11'])).
% 0.39/0.57  thf('13', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (((sk_A) = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.39/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X20 : $i, X21 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.39/0.57           = (k3_xboole_0 @ X20 @ X21))),
% 0.39/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.57  thf(t36_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.39/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X3 : $i, X5 : $i]:
% 0.39/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.39/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['15', '18'])).
% 0.39/0.57  thf(t49_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.39/0.57       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 0.39/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 0.39/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['19', '20'])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A) = (k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['14', '21'])).
% 0.39/0.57  thf(t16_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.57       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 0.39/0.57           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ sk_A)) = (k1_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['22', '23'])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X18 : $i, X19 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 0.39/0.57           = (k4_xboole_0 @ X18 @ X19))),
% 0.39/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 0.39/0.57         = (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.39/0.57  thf('27', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (((sk_B) = (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['19', '20'])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      (((k3_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['28', '29'])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 0.39/0.57           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 0.39/0.57           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X0 : $i, X2 : $i]:
% 0.39/0.57         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.39/0.57          | (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.39/0.57          | (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.39/0.57             (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['32', '35'])).
% 0.39/0.57  thf(t2_boole, axiom,
% 0.39/0.57    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t2_boole])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.57          | (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.39/0.57             (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('demod', [status(thm)], ['36', '37'])).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C) @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('simplify', [status(thm)], ['38'])).
% 0.39/0.57  thf('40', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('sup+', [status(thm)], ['7', '39'])).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.39/0.57          | (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.57        | (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_A) @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.39/0.57  thf('45', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.39/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.57  thf('47', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.39/0.57      inference('sup+', [status(thm)], ['45', '46'])).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      (![X3 : $i, X5 : $i]:
% 0.39/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.39/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.57  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.39/0.57  thf('50', plain,
% 0.39/0.57      (![X20 : $i, X21 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.39/0.57           = (k3_xboole_0 @ X20 @ X21))),
% 0.39/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.57  thf('51', plain,
% 0.39/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['49', '50'])).
% 0.39/0.57  thf('52', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.57  thf('53', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.57  thf('54', plain,
% 0.39/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['44', '53'])).
% 0.39/0.57  thf('55', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.39/0.57      inference('simplify', [status(thm)], ['54'])).
% 0.39/0.57  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
