%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N9PMETZVBp

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:35 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 193 expanded)
%              Number of leaves         :   20 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  419 (1385 expanded)
%              Number of equality atoms :   42 ( 136 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','14'])).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','22'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('25',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('41',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t82_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) )).

thf('45',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t82_xboole_1])).

thf('46',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_C ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('48',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['23','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N9PMETZVBp
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:16:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 288 iterations in 0.114s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.56  thf(t106_xboole_1, conjecture,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.39/0.56       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.56        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.39/0.56          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.39/0.56  thf('0', plain,
% 0.39/0.56      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('1', plain,
% 0.39/0.56      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.56      inference('split', [status(esa)], ['0'])).
% 0.39/0.56  thf(t36_xboole_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.56  thf('2', plain,
% 0.39/0.56      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.39/0.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.56  thf(l32_xboole_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.56  thf('3', plain,
% 0.39/0.56      (![X3 : $i, X5 : $i]:
% 0.39/0.56         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.39/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.56  thf('4', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.57  thf('5', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t28_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (![X10 : $i, X11 : $i]:
% 0.39/0.57         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.39/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.57  thf(t49_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.39/0.57       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.39/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.39/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ sk_A @ 
% 0.39/0.57           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.39/0.57           = (k4_xboole_0 @ sk_A @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('sup+', [status(thm)], ['4', '9'])).
% 0.39/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.57  thf(t2_boole, axiom,
% 0.39/0.57    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t2_boole])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf('15', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['10', '11', '14'])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i]:
% 0.39/0.57         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.57  thf('18', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.39/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('20', plain, (((r1_tarski @ sk_A @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_tarski @ sk_A @ sk_B))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('22', plain, (~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.39/0.57      inference('sat_resolution*', [status(thm)], ['20', '21'])).
% 0.39/0.57  thf('23', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.39/0.57      inference('simpl_trail', [status(thm)], ['1', '22'])).
% 0.39/0.57  thf(t17_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.39/0.57      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X3 : $i, X5 : $i]:
% 0.39/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.39/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.39/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.39/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.39/0.57  thf(t100_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X6 @ X7)
% 0.39/0.57           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.39/0.57           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['28', '29'])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t2_boole])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X6 @ X7)
% 0.39/0.57           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['31', '32'])).
% 0.39/0.57  thf(t3_boole, axiom,
% 0.39/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.57  thf('34', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.57  thf('35', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['33', '34'])).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['30', '35'])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['30', '35'])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ sk_A @ 
% 0.39/0.57           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.39/0.57           = (k4_xboole_0 @ sk_A @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.39/0.57           = (k4_xboole_0 @ sk_A @ 
% 0.39/0.57              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.57      inference('sup+', [status(thm)], ['37', '38'])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((sk_A)
% 0.39/0.57           = (k4_xboole_0 @ sk_A @ 
% 0.39/0.57              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 0.39/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.39/0.57  thf('42', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.39/0.57      inference('sup+', [status(thm)], ['36', '41'])).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['30', '35'])).
% 0.39/0.57  thf('44', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.39/0.57      inference('sup+', [status(thm)], ['42', '43'])).
% 0.39/0.57  thf(t82_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ))).
% 0.39/0.57  thf('45', plain,
% 0.39/0.57      (![X19 : $i, X20 : $i]:
% 0.39/0.57         (r1_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X20 @ X19))),
% 0.39/0.57      inference('cnf', [status(esa)], [t82_xboole_1])).
% 0.39/0.57  thf('46', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_C)),
% 0.39/0.57      inference('sup+', [status(thm)], ['44', '45'])).
% 0.39/0.57  thf('47', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.39/0.57      inference('sup+', [status(thm)], ['36', '41'])).
% 0.39/0.57  thf('48', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.39/0.57  thf('49', plain, ($false), inference('demod', [status(thm)], ['23', '48'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
