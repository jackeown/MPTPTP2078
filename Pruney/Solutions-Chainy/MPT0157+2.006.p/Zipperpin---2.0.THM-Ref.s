%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gWEceKwq8R

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :  170 ( 170 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t73_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) ),
    inference('cnf.neg',[status(esa)],[t73_enumset1])).

thf('0',plain,(
    ( k4_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X15 @ X15 @ X16 @ X17 )
      = ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t54_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    $false ),
    inference(simplify,[status(thm)],['6'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gWEceKwq8R
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:39:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 16 iterations in 0.022s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.49  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(t73_enumset1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.49     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.21/0.49       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.49        ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.21/0.49          ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t73_enumset1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (((k4_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.49         != (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t71_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X15 @ X15 @ X16 @ X17)
% 0.21/0.49           = (k1_enumset1 @ X15 @ X16 @ X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.49  thf(t54_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.49     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.49       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         ((k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.21/0.49           = (k2_xboole_0 @ (k2_enumset1 @ X7 @ X8 @ X9 @ X10) @ 
% 0.21/0.49              (k2_tarski @ X11 @ X12)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t54_enumset1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.49         ((k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 0.21/0.49           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.21/0.49              (k2_tarski @ X4 @ X3)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf(l57_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.49     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.21/0.49       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.21/0.49           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 0.21/0.49              (k2_tarski @ X5 @ X6)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.49         ((k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 0.21/0.49           = (k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.49         != (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '5'])).
% 0.21/0.49  thf('7', plain, ($false), inference('simplify', [status(thm)], ['6'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
