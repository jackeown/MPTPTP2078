%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xjGKP3zEv0

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:51 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :  229 ( 229 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(t92_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t92_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X13 @ X13 @ X14 @ X15 )
      = ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t58_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X7 @ X8 ) @ ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) @ ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t53_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t83_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_enumset1 @ X21 @ X21 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','5','8'])).

thf('10',plain,(
    $false ),
    inference(simplify,[status(thm)],['9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xjGKP3zEv0
% 0.14/0.37  % Computer   : n024.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 18:06:06 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.24/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.49  % Solved by: fo/fo7.sh
% 0.24/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.49  % done 10 iterations in 0.011s
% 0.24/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.49  % SZS output start Refutation
% 0.24/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.24/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.49  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.24/0.49  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.24/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.24/0.49  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.24/0.49  thf(t92_enumset1, conjecture,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.24/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.49    (~( ![A:$i,B:$i]:
% 0.24/0.49        ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.24/0.49    inference('cnf.neg', [status(esa)], [t92_enumset1])).
% 0.24/0.49  thf('0', plain,
% 0.24/0.49      (((k5_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B)
% 0.24/0.49         != (k2_tarski @ sk_A @ sk_B))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(t71_enumset1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.24/0.49  thf('1', plain,
% 0.24/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.24/0.49         ((k2_enumset1 @ X13 @ X13 @ X14 @ X15)
% 0.24/0.49           = (k1_enumset1 @ X13 @ X14 @ X15))),
% 0.24/0.49      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.24/0.49  thf(t58_enumset1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.24/0.49     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.24/0.49       ( k2_xboole_0 @
% 0.24/0.49         ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ))).
% 0.24/0.49  thf('2', plain,
% 0.24/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.24/0.49         ((k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.24/0.49           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X7 @ X8) @ 
% 0.24/0.49              (k2_enumset1 @ X9 @ X10 @ X11 @ X12)))),
% 0.24/0.49      inference('cnf', [status(esa)], [t58_enumset1])).
% 0.24/0.49  thf('3', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.49         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.24/0.49           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.24/0.49              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.24/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.24/0.49  thf(t53_enumset1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.24/0.49     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.24/0.49       ( k2_xboole_0 @
% 0.24/0.49         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.24/0.49  thf('4', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.49         ((k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5)
% 0.24/0.49           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X1 @ X2) @ 
% 0.24/0.49              (k1_enumset1 @ X3 @ X4 @ X5)))),
% 0.24/0.49      inference('cnf', [status(esa)], [t53_enumset1])).
% 0.24/0.49  thf('5', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.49         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.24/0.49           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.24/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.24/0.49  thf(t73_enumset1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.24/0.49     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.24/0.49       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.24/0.49  thf('6', plain,
% 0.24/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.24/0.49         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.24/0.49           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.24/0.49      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.24/0.49  thf(t83_enumset1, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( k3_enumset1 @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.24/0.49  thf('7', plain,
% 0.24/0.49      (![X21 : $i, X22 : $i]:
% 0.24/0.49         ((k3_enumset1 @ X21 @ X21 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.24/0.49      inference('cnf', [status(esa)], [t83_enumset1])).
% 0.24/0.49  thf('8', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         ((k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.24/0.49      inference('sup+', [status(thm)], ['6', '7'])).
% 0.24/0.49  thf('9', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.24/0.49      inference('demod', [status(thm)], ['0', '5', '8'])).
% 0.24/0.49  thf('10', plain, ($false), inference('simplify', [status(thm)], ['9'])).
% 0.24/0.49  
% 0.24/0.49  % SZS output end Refutation
% 0.24/0.49  
% 0.24/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
