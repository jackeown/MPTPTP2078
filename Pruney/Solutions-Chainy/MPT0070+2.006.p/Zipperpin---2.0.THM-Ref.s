%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9dpTqdEhw4

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:33 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   69 (  86 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :   17
%              Number of atoms          :  451 ( 598 expanded)
%              Number of equality atoms :   51 (  64 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t63_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['6','23'])).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('34',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['4','40'])).

thf('42',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['3','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9dpTqdEhw4
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.72  % Solved by: fo/fo7.sh
% 0.47/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.72  % done 783 iterations in 0.273s
% 0.47/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.72  % SZS output start Refutation
% 0.47/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.72  thf(t63_xboole_1, conjecture,
% 0.47/0.72    (![A:$i,B:$i,C:$i]:
% 0.47/0.72     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.47/0.72       ( r1_xboole_0 @ A @ C ) ))).
% 0.47/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.72        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.47/0.72          ( r1_xboole_0 @ A @ C ) ) )),
% 0.47/0.72    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.47/0.72  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf(t28_xboole_1, axiom,
% 0.47/0.72    (![A:$i,B:$i]:
% 0.47/0.72     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.47/0.72  thf('2', plain,
% 0.47/0.72      (![X8 : $i, X9 : $i]:
% 0.47/0.72         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.47/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.72  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.47/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.72  thf(commutativity_k3_xboole_0, axiom,
% 0.47/0.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.47/0.72  thf('4', plain,
% 0.47/0.72      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.47/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.72  thf(t48_xboole_1, axiom,
% 0.47/0.72    (![A:$i,B:$i]:
% 0.47/0.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.72  thf('5', plain,
% 0.47/0.72      (![X17 : $i, X18 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.47/0.72           = (k3_xboole_0 @ X17 @ X18))),
% 0.47/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.72  thf(commutativity_k2_xboole_0, axiom,
% 0.47/0.72    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.47/0.72  thf('6', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.47/0.72  thf('7', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf(d7_xboole_0, axiom,
% 0.47/0.72    (![A:$i,B:$i]:
% 0.47/0.72     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.47/0.72       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.72  thf('8', plain,
% 0.47/0.72      (![X4 : $i, X5 : $i]:
% 0.47/0.72         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.47/0.72      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.47/0.72  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.47/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.72  thf('10', plain,
% 0.47/0.72      (![X17 : $i, X18 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.47/0.72           = (k3_xboole_0 @ X17 @ X18))),
% 0.47/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.72  thf('11', plain,
% 0.47/0.72      (![X17 : $i, X18 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.47/0.72           = (k3_xboole_0 @ X17 @ X18))),
% 0.47/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.72  thf('12', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.47/0.72           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.47/0.72      inference('sup+', [status(thm)], ['10', '11'])).
% 0.47/0.72  thf(t36_xboole_1, axiom,
% 0.47/0.72    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.47/0.72  thf('13', plain,
% 0.47/0.72      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.47/0.72      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.47/0.72  thf('14', plain,
% 0.47/0.72      (![X8 : $i, X9 : $i]:
% 0.47/0.72         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.47/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.72  thf('15', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]:
% 0.47/0.72         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.47/0.72           = (k4_xboole_0 @ X0 @ X1))),
% 0.47/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.72  thf('16', plain,
% 0.47/0.72      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.47/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.72  thf('17', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]:
% 0.47/0.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.47/0.72           = (k4_xboole_0 @ X0 @ X1))),
% 0.47/0.72      inference('demod', [status(thm)], ['15', '16'])).
% 0.47/0.72  thf('18', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.47/0.72           = (k4_xboole_0 @ X1 @ X0))),
% 0.47/0.72      inference('demod', [status(thm)], ['12', '17'])).
% 0.47/0.72  thf('19', plain,
% 0.47/0.72      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.47/0.72      inference('sup+', [status(thm)], ['9', '18'])).
% 0.47/0.72  thf(t3_boole, axiom,
% 0.47/0.72    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.72  thf('20', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.47/0.72      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.72  thf('21', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.47/0.72      inference('demod', [status(thm)], ['19', '20'])).
% 0.47/0.72  thf(t41_xboole_1, axiom,
% 0.47/0.72    (![A:$i,B:$i,C:$i]:
% 0.47/0.72     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.47/0.72       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.47/0.72  thf('22', plain,
% 0.47/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.47/0.72           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.47/0.72      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.47/0.72  thf('23', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ sk_B @ X0)
% 0.47/0.72           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))),
% 0.47/0.72      inference('sup+', [status(thm)], ['21', '22'])).
% 0.47/0.72  thf('24', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ sk_B @ X0)
% 0.47/0.72           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_C)))),
% 0.47/0.72      inference('sup+', [status(thm)], ['6', '23'])).
% 0.47/0.72  thf('25', plain,
% 0.47/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.47/0.72           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.47/0.72      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.47/0.72  thf('26', plain,
% 0.47/0.72      (![X17 : $i, X18 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.47/0.72           = (k3_xboole_0 @ X17 @ X18))),
% 0.47/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.72  thf('27', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ X2 @ 
% 0.47/0.72           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 0.47/0.72           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.47/0.72      inference('sup+', [status(thm)], ['25', '26'])).
% 0.47/0.72  thf('28', plain,
% 0.47/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.47/0.72           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.47/0.72      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.47/0.72  thf('29', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ X2 @ 
% 0.47/0.72           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 0.47/0.72           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.47/0.72      inference('demod', [status(thm)], ['27', '28'])).
% 0.47/0.72  thf('30', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ X0)))
% 0.47/0.72           = (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_C))),
% 0.47/0.72      inference('sup+', [status(thm)], ['24', '29'])).
% 0.47/0.72  thf('31', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.47/0.72      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.72  thf('32', plain,
% 0.47/0.72      (![X17 : $i, X18 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.47/0.72           = (k3_xboole_0 @ X17 @ X18))),
% 0.47/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.72  thf('33', plain,
% 0.47/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.72      inference('sup+', [status(thm)], ['31', '32'])).
% 0.47/0.72  thf(t2_boole, axiom,
% 0.47/0.72    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.72  thf('34', plain,
% 0.47/0.72      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.47/0.72  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.72      inference('demod', [status(thm)], ['33', '34'])).
% 0.47/0.72  thf('36', plain,
% 0.47/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.47/0.72           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.47/0.72      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.47/0.72  thf('37', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]:
% 0.47/0.72         ((k1_xboole_0)
% 0.47/0.72           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.47/0.72      inference('sup+', [status(thm)], ['35', '36'])).
% 0.47/0.72  thf('38', plain,
% 0.47/0.72      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.47/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.72  thf('39', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         ((k1_xboole_0) = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.47/0.72      inference('demod', [status(thm)], ['30', '37', '38'])).
% 0.47/0.72  thf('40', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         ((k1_xboole_0) = (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.47/0.72      inference('sup+', [status(thm)], ['5', '39'])).
% 0.47/0.72  thf('41', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         ((k1_xboole_0) = (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.47/0.72      inference('sup+', [status(thm)], ['4', '40'])).
% 0.47/0.72  thf('42', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.47/0.72      inference('sup+', [status(thm)], ['3', '41'])).
% 0.47/0.72  thf('43', plain,
% 0.47/0.72      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.47/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.72  thf('44', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.47/0.72      inference('demod', [status(thm)], ['42', '43'])).
% 0.47/0.72  thf('45', plain,
% 0.47/0.72      (![X4 : $i, X6 : $i]:
% 0.47/0.72         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.47/0.72      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.47/0.72  thf('46', plain,
% 0.47/0.72      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.47/0.72      inference('sup-', [status(thm)], ['44', '45'])).
% 0.47/0.72  thf('47', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.47/0.72      inference('simplify', [status(thm)], ['46'])).
% 0.47/0.72  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 0.47/0.72  
% 0.47/0.72  % SZS output end Refutation
% 0.47/0.72  
% 0.47/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
