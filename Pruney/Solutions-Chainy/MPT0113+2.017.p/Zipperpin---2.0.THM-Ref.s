%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZlIkU5AHcK

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:31 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   68 (  98 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  426 ( 675 expanded)
%              Number of equality atoms :   39 (  52 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('33',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('37',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','40'])).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['28','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['13','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZlIkU5AHcK
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.70/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.90  % Solved by: fo/fo7.sh
% 0.70/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.90  % done 969 iterations in 0.439s
% 0.70/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.90  % SZS output start Refutation
% 0.70/0.90  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.70/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.70/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.90  thf(t106_xboole_1, conjecture,
% 0.70/0.90    (![A:$i,B:$i,C:$i]:
% 0.70/0.90     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.70/0.90       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.70/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.90    (~( ![A:$i,B:$i,C:$i]:
% 0.70/0.90        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.70/0.90          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.70/0.90    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.70/0.90  thf('0', plain,
% 0.70/0.90      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('1', plain,
% 0.70/0.90      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.70/0.90      inference('split', [status(esa)], ['0'])).
% 0.70/0.90  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf(t28_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.70/0.90  thf('3', plain,
% 0.70/0.90      (![X10 : $i, X11 : $i]:
% 0.70/0.90         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.70/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.70/0.90  thf('4', plain,
% 0.70/0.90      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.70/0.90      inference('sup-', [status(thm)], ['2', '3'])).
% 0.70/0.90  thf(t49_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i,C:$i]:
% 0.70/0.90     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.70/0.90       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.70/0.90  thf('5', plain,
% 0.70/0.90      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.70/0.90           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.70/0.90      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.70/0.90  thf(t79_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.70/0.90  thf('6', plain,
% 0.70/0.90      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 0.70/0.90      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.70/0.90  thf('7', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 0.70/0.90      inference('sup+', [status(thm)], ['5', '6'])).
% 0.70/0.90  thf('8', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.70/0.90      inference('sup+', [status(thm)], ['4', '7'])).
% 0.70/0.90  thf('9', plain,
% 0.70/0.90      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.70/0.90      inference('split', [status(esa)], ['0'])).
% 0.70/0.90  thf('10', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.70/0.90      inference('sup-', [status(thm)], ['8', '9'])).
% 0.70/0.90  thf('11', plain,
% 0.70/0.90      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.70/0.90      inference('split', [status(esa)], ['0'])).
% 0.70/0.90  thf('12', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.70/0.90      inference('sat_resolution*', [status(thm)], ['10', '11'])).
% 0.70/0.90  thf('13', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.70/0.90      inference('simpl_trail', [status(thm)], ['1', '12'])).
% 0.70/0.90  thf(t36_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.70/0.90  thf('14', plain,
% 0.70/0.90      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.70/0.90      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.70/0.90  thf('15', plain,
% 0.70/0.90      (![X10 : $i, X11 : $i]:
% 0.70/0.90         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.70/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.70/0.90  thf('16', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.70/0.90           = (k4_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('sup-', [status(thm)], ['14', '15'])).
% 0.70/0.90  thf(commutativity_k3_xboole_0, axiom,
% 0.70/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.70/0.90  thf('17', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.90  thf('18', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.70/0.90           = (k4_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('demod', [status(thm)], ['16', '17'])).
% 0.70/0.90  thf('19', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.90  thf('20', plain,
% 0.70/0.90      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.70/0.90      inference('sup-', [status(thm)], ['2', '3'])).
% 0.70/0.90  thf(t16_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i,C:$i]:
% 0.70/0.90     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.70/0.90       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.70/0.90  thf('21', plain,
% 0.70/0.90      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 0.70/0.90           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.70/0.90  thf('22', plain,
% 0.70/0.90      (![X0 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ sk_A @ X0)
% 0.70/0.90           = (k3_xboole_0 @ sk_A @ 
% 0.70/0.90              (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['20', '21'])).
% 0.70/0.90  thf('23', plain,
% 0.70/0.90      (![X0 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ sk_A @ X0)
% 0.70/0.90           = (k3_xboole_0 @ sk_A @ 
% 0.70/0.90              (k3_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 0.70/0.90      inference('sup+', [status(thm)], ['19', '22'])).
% 0.70/0.90  thf('24', plain,
% 0.70/0.90      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.70/0.90         = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['18', '23'])).
% 0.70/0.90  thf('25', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.90  thf('26', plain,
% 0.70/0.90      (((k3_xboole_0 @ sk_B @ sk_A)
% 0.70/0.90         = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.70/0.90      inference('demod', [status(thm)], ['24', '25'])).
% 0.70/0.90  thf('27', plain,
% 0.70/0.90      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.70/0.90      inference('sup-', [status(thm)], ['2', '3'])).
% 0.70/0.90  thf('28', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.70/0.90      inference('sup+', [status(thm)], ['26', '27'])).
% 0.70/0.90  thf('29', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.70/0.90           = (k4_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('demod', [status(thm)], ['16', '17'])).
% 0.70/0.90  thf(t100_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.70/0.90  thf('30', plain,
% 0.70/0.90      (![X5 : $i, X6 : $i]:
% 0.70/0.90         ((k4_xboole_0 @ X5 @ X6)
% 0.70/0.90           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.90  thf('31', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.70/0.90           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['29', '30'])).
% 0.70/0.90  thf('32', plain,
% 0.70/0.90      (![X5 : $i, X6 : $i]:
% 0.70/0.90         ((k4_xboole_0 @ X5 @ X6)
% 0.70/0.90           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.90  thf(t92_xboole_1, axiom,
% 0.70/0.90    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.70/0.90  thf('33', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.70/0.90      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.70/0.90  thf(t91_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i,C:$i]:
% 0.70/0.90     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.70/0.90       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.70/0.90  thf('34', plain,
% 0.70/0.90      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.70/0.90         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.70/0.90           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.70/0.90  thf('35', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.70/0.90           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['33', '34'])).
% 0.70/0.90  thf(commutativity_k5_xboole_0, axiom,
% 0.70/0.90    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.70/0.90  thf('36', plain,
% 0.70/0.90      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.70/0.90  thf(t5_boole, axiom,
% 0.70/0.90    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.90  thf('37', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.70/0.90      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.90  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.90      inference('sup+', [status(thm)], ['36', '37'])).
% 0.70/0.90  thf('39', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.70/0.90      inference('demod', [status(thm)], ['35', '38'])).
% 0.70/0.90  thf('40', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ X1 @ X0)
% 0.70/0.90           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['32', '39'])).
% 0.70/0.90  thf('41', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ X1 @ X0)
% 0.70/0.90           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['31', '40'])).
% 0.70/0.90  thf('42', plain,
% 0.70/0.90      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.70/0.90      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.70/0.90  thf('43', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.70/0.90      inference('sup+', [status(thm)], ['41', '42'])).
% 0.70/0.90  thf('44', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.70/0.90      inference('sup+', [status(thm)], ['28', '43'])).
% 0.70/0.90  thf('45', plain, ($false), inference('demod', [status(thm)], ['13', '44'])).
% 0.70/0.90  
% 0.70/0.90  % SZS output end Refutation
% 0.70/0.90  
% 0.70/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
