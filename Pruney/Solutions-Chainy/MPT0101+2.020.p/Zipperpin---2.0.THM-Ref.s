%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w3OKQ0Y9mA

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:57 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  272 ( 301 expanded)
%              Number of equality atoms :   25 (  28 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t94_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w3OKQ0Y9mA
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.13/1.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.13/1.32  % Solved by: fo/fo7.sh
% 1.13/1.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.32  % done 520 iterations in 0.879s
% 1.13/1.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.13/1.32  % SZS output start Refutation
% 1.13/1.32  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.13/1.32  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.13/1.32  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.13/1.32  thf(sk_B_type, type, sk_B: $i).
% 1.13/1.32  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.13/1.32  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.13/1.32  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.32  thf(t94_xboole_1, conjecture,
% 1.13/1.32    (![A:$i,B:$i]:
% 1.13/1.32     ( ( k2_xboole_0 @ A @ B ) =
% 1.13/1.32       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.13/1.32  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.32    (~( ![A:$i,B:$i]:
% 1.13/1.32        ( ( k2_xboole_0 @ A @ B ) =
% 1.13/1.32          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 1.13/1.32    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 1.13/1.32  thf('0', plain,
% 1.13/1.32      (((k2_xboole_0 @ sk_A @ sk_B)
% 1.13/1.32         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 1.13/1.32             (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf(d6_xboole_0, axiom,
% 1.13/1.32    (![A:$i,B:$i]:
% 1.13/1.32     ( ( k5_xboole_0 @ A @ B ) =
% 1.13/1.32       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.13/1.32  thf('1', plain,
% 1.13/1.32      (![X2 : $i, X3 : $i]:
% 1.13/1.32         ((k5_xboole_0 @ X2 @ X3)
% 1.13/1.32           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 1.13/1.32      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.13/1.32  thf(commutativity_k2_xboole_0, axiom,
% 1.13/1.32    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.13/1.32  thf('2', plain,
% 1.13/1.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.13/1.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.13/1.32  thf('3', plain,
% 1.13/1.32      (![X0 : $i, X1 : $i]:
% 1.13/1.32         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 1.13/1.32           = (k5_xboole_0 @ X1 @ X0))),
% 1.13/1.32      inference('sup+', [status(thm)], ['1', '2'])).
% 1.13/1.32  thf('4', plain,
% 1.13/1.32      (![X2 : $i, X3 : $i]:
% 1.13/1.32         ((k5_xboole_0 @ X2 @ X3)
% 1.13/1.32           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 1.13/1.32      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.13/1.32  thf('5', plain,
% 1.13/1.32      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 1.13/1.32      inference('sup+', [status(thm)], ['3', '4'])).
% 1.13/1.32  thf('6', plain,
% 1.13/1.32      (((k2_xboole_0 @ sk_A @ sk_B)
% 1.13/1.32         != (k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 1.13/1.32             (k5_xboole_0 @ sk_A @ sk_B)))),
% 1.13/1.32      inference('demod', [status(thm)], ['0', '5'])).
% 1.13/1.32  thf(l97_xboole_1, axiom,
% 1.13/1.32    (![A:$i,B:$i]:
% 1.13/1.32     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 1.13/1.32  thf('7', plain,
% 1.13/1.32      (![X4 : $i, X5 : $i]:
% 1.13/1.32         (r1_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ (k5_xboole_0 @ X4 @ X5))),
% 1.13/1.32      inference('cnf', [status(esa)], [l97_xboole_1])).
% 1.13/1.32  thf(t83_xboole_1, axiom,
% 1.13/1.32    (![A:$i,B:$i]:
% 1.13/1.32     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.13/1.32  thf('8', plain,
% 1.13/1.32      (![X13 : $i, X14 : $i]:
% 1.13/1.33         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 1.13/1.33      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.13/1.33  thf('9', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]:
% 1.13/1.33         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.13/1.33           = (k3_xboole_0 @ X1 @ X0))),
% 1.13/1.33      inference('sup-', [status(thm)], ['7', '8'])).
% 1.13/1.33  thf('10', plain,
% 1.13/1.33      (![X2 : $i, X3 : $i]:
% 1.13/1.33         ((k5_xboole_0 @ X2 @ X3)
% 1.13/1.33           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 1.13/1.33      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.13/1.33  thf('11', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]:
% 1.13/1.33         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.13/1.33           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 1.13/1.33              (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 1.13/1.33      inference('sup+', [status(thm)], ['9', '10'])).
% 1.13/1.33  thf(t39_xboole_1, axiom,
% 1.13/1.33    (![A:$i,B:$i]:
% 1.13/1.33     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.13/1.33  thf('12', plain,
% 1.13/1.33      (![X6 : $i, X7 : $i]:
% 1.13/1.33         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 1.13/1.33           = (k2_xboole_0 @ X6 @ X7))),
% 1.13/1.33      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.13/1.33  thf('13', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]:
% 1.13/1.33         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.13/1.33           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 1.13/1.33      inference('demod', [status(thm)], ['11', '12'])).
% 1.13/1.33  thf(t93_xboole_1, axiom,
% 1.13/1.33    (![A:$i,B:$i]:
% 1.13/1.33     ( ( k2_xboole_0 @ A @ B ) =
% 1.13/1.33       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.13/1.33  thf('14', plain,
% 1.13/1.33      (![X16 : $i, X17 : $i]:
% 1.13/1.33         ((k2_xboole_0 @ X16 @ X17)
% 1.13/1.33           = (k2_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 1.13/1.33              (k3_xboole_0 @ X16 @ X17)))),
% 1.13/1.33      inference('cnf', [status(esa)], [t93_xboole_1])).
% 1.13/1.33  thf('15', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.13/1.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.13/1.33  thf('16', plain,
% 1.13/1.33      (![X16 : $i, X17 : $i]:
% 1.13/1.33         ((k2_xboole_0 @ X16 @ X17)
% 1.13/1.33           = (k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 1.13/1.33              (k5_xboole_0 @ X16 @ X17)))),
% 1.13/1.33      inference('demod', [status(thm)], ['14', '15'])).
% 1.13/1.33  thf('17', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]:
% 1.13/1.33         ((k2_xboole_0 @ X1 @ X0)
% 1.13/1.33           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 1.13/1.33      inference('sup+', [status(thm)], ['13', '16'])).
% 1.13/1.33  thf('18', plain,
% 1.13/1.33      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 1.13/1.33      inference('demod', [status(thm)], ['6', '17'])).
% 1.13/1.33  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 1.13/1.33  
% 1.13/1.33  % SZS output end Refutation
% 1.13/1.33  
% 1.13/1.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
