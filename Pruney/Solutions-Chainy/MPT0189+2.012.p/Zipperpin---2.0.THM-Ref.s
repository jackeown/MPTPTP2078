%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2UeJzfxFbM

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:08 EST 2020

% Result     : Theorem 2.35s
% Output     : Refutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  321 ( 367 expanded)
%              Number of equality atoms :   28 (  32 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t108_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ A @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ B @ A @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t108_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X74: $i,X75: $i] :
      ( ( k1_enumset1 @ X74 @ X74 @ X75 )
      = ( k2_tarski @ X74 @ X75 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X7 @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X74: $i,X75: $i] :
      ( ( k1_enumset1 @ X74 @ X74 @ X75 )
      = ( k2_tarski @ X74 @ X75 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X7 @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('9',plain,(
    ! [X79: $i,X80: $i,X81: $i,X82: $i] :
      ( ( k3_enumset1 @ X79 @ X79 @ X80 @ X81 @ X82 )
      = ( k2_enumset1 @ X79 @ X80 @ X81 @ X82 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X79: $i,X80: $i,X81: $i,X82: $i] :
      ( ( k3_enumset1 @ X79 @ X79 @ X80 @ X81 @ X82 )
      = ( k2_enumset1 @ X79 @ X80 @ X81 @ X82 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X18 @ X16 @ X17 )
      = ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X18 @ X16 @ X17 )
      = ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X14 @ X13 )
      = ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','15','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2UeJzfxFbM
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:31:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.35/2.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.35/2.57  % Solved by: fo/fo7.sh
% 2.35/2.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.35/2.57  % done 3774 iterations in 2.106s
% 2.35/2.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.35/2.57  % SZS output start Refutation
% 2.35/2.57  thf(sk_A_type, type, sk_A: $i).
% 2.35/2.57  thf(sk_C_type, type, sk_C: $i).
% 2.35/2.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.35/2.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.35/2.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.35/2.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.35/2.57  thf(sk_B_type, type, sk_B: $i).
% 2.35/2.57  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 2.35/2.57  thf(sk_D_type, type, sk_D: $i).
% 2.35/2.57  thf(t108_enumset1, conjecture,
% 2.35/2.57    (![A:$i,B:$i,C:$i,D:$i]:
% 2.35/2.57     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 2.35/2.57  thf(zf_stmt_0, negated_conjecture,
% 2.35/2.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.35/2.57        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 2.35/2.57    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 2.35/2.57  thf('0', plain,
% 2.35/2.57      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 2.35/2.57         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 2.35/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.57  thf(t70_enumset1, axiom,
% 2.35/2.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.35/2.57  thf('1', plain,
% 2.35/2.57      (![X74 : $i, X75 : $i]:
% 2.35/2.57         ((k1_enumset1 @ X74 @ X74 @ X75) = (k2_tarski @ X74 @ X75))),
% 2.35/2.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.35/2.57  thf(l57_enumset1, axiom,
% 2.35/2.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.35/2.57     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 2.35/2.57       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 2.35/2.57  thf('2', plain,
% 2.35/2.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 2.35/2.57         ((k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10)
% 2.35/2.57           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X7 @ X8) @ 
% 2.35/2.57              (k2_tarski @ X9 @ X10)))),
% 2.35/2.57      inference('cnf', [status(esa)], [l57_enumset1])).
% 2.35/2.57  thf(commutativity_k2_xboole_0, axiom,
% 2.35/2.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.35/2.57  thf('3', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.35/2.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.35/2.57  thf('4', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.35/2.57         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_enumset1 @ X4 @ X3 @ X2))
% 2.35/2.57           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 2.35/2.57      inference('sup+', [status(thm)], ['2', '3'])).
% 2.35/2.57  thf('5', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.35/2.57         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 2.35/2.57           = (k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2))),
% 2.35/2.57      inference('sup+', [status(thm)], ['1', '4'])).
% 2.35/2.57  thf('6', plain,
% 2.35/2.57      (![X74 : $i, X75 : $i]:
% 2.35/2.57         ((k1_enumset1 @ X74 @ X74 @ X75) = (k2_tarski @ X74 @ X75))),
% 2.35/2.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.35/2.57  thf('7', plain,
% 2.35/2.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 2.35/2.57         ((k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10)
% 2.35/2.57           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X7 @ X8) @ 
% 2.35/2.57              (k2_tarski @ X9 @ X10)))),
% 2.35/2.57      inference('cnf', [status(esa)], [l57_enumset1])).
% 2.35/2.57  thf('8', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.35/2.57         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 2.35/2.57           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 2.35/2.57      inference('sup+', [status(thm)], ['6', '7'])).
% 2.35/2.57  thf(t72_enumset1, axiom,
% 2.35/2.57    (![A:$i,B:$i,C:$i,D:$i]:
% 2.35/2.57     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 2.35/2.57  thf('9', plain,
% 2.35/2.57      (![X79 : $i, X80 : $i, X81 : $i, X82 : $i]:
% 2.35/2.57         ((k3_enumset1 @ X79 @ X79 @ X80 @ X81 @ X82)
% 2.35/2.57           = (k2_enumset1 @ X79 @ X80 @ X81 @ X82))),
% 2.35/2.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.35/2.57  thf('10', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.35/2.57         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 2.35/2.57           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.35/2.57      inference('sup+', [status(thm)], ['8', '9'])).
% 2.35/2.57  thf('11', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.35/2.57         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 2.35/2.57           = (k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2))),
% 2.35/2.57      inference('demod', [status(thm)], ['5', '10'])).
% 2.35/2.57  thf('12', plain,
% 2.35/2.57      (![X79 : $i, X80 : $i, X81 : $i, X82 : $i]:
% 2.35/2.57         ((k3_enumset1 @ X79 @ X79 @ X80 @ X81 @ X82)
% 2.35/2.57           = (k2_enumset1 @ X79 @ X80 @ X81 @ X82))),
% 2.35/2.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.35/2.57  thf(t105_enumset1, axiom,
% 2.35/2.57    (![A:$i,B:$i,C:$i,D:$i]:
% 2.35/2.57     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 2.35/2.57  thf('13', plain,
% 2.35/2.57      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 2.35/2.57         ((k2_enumset1 @ X15 @ X18 @ X16 @ X17)
% 2.35/2.57           = (k2_enumset1 @ X15 @ X16 @ X17 @ X18))),
% 2.35/2.57      inference('cnf', [status(esa)], [t105_enumset1])).
% 2.35/2.57  thf('14', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.35/2.57         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 2.35/2.57           = (k2_enumset1 @ X3 @ X1 @ X0 @ X2))),
% 2.35/2.57      inference('sup+', [status(thm)], ['12', '13'])).
% 2.35/2.57  thf('15', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.35/2.57         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X3 @ X2 @ X0))),
% 2.35/2.57      inference('sup+', [status(thm)], ['11', '14'])).
% 2.35/2.57  thf('16', plain,
% 2.35/2.57      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 2.35/2.57         ((k2_enumset1 @ X15 @ X18 @ X16 @ X17)
% 2.35/2.57           = (k2_enumset1 @ X15 @ X16 @ X17 @ X18))),
% 2.35/2.57      inference('cnf', [status(esa)], [t105_enumset1])).
% 2.35/2.57  thf(t103_enumset1, axiom,
% 2.35/2.57    (![A:$i,B:$i,C:$i,D:$i]:
% 2.35/2.57     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 2.35/2.57  thf('17', plain,
% 2.35/2.57      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 2.35/2.57         ((k2_enumset1 @ X11 @ X12 @ X14 @ X13)
% 2.35/2.57           = (k2_enumset1 @ X11 @ X12 @ X13 @ X14))),
% 2.35/2.57      inference('cnf', [status(esa)], [t103_enumset1])).
% 2.35/2.57  thf('18', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.35/2.57         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.35/2.57      inference('sup+', [status(thm)], ['16', '17'])).
% 2.35/2.57  thf('19', plain,
% 2.35/2.57      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 2.35/2.57         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 2.35/2.57      inference('demod', [status(thm)], ['0', '15', '18'])).
% 2.35/2.57  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 2.35/2.57  
% 2.35/2.57  % SZS output end Refutation
% 2.35/2.57  
% 2.35/2.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
