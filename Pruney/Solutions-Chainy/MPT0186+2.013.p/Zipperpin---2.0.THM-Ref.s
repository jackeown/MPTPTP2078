%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X8b7sBmNtx

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  253 ( 290 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t104_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ C @ B @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t104_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X12 @ X12 @ X13 @ X14 )
      = ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) @ ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X0 @ X1 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X12 @ X12 @ X13 @ X14 )
      = ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) @ ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X8b7sBmNtx
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 40 iterations in 0.031s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.49  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(t104_enumset1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t104_enumset1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.49         != (k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t103_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.20/0.49  thf(t71_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.49         ((k2_enumset1 @ X12 @ X12 @ X13 @ X14)
% 0.20/0.49           = (k1_enumset1 @ X12 @ X13 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(t50_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.49     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.49       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.49         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 0.20/0.49           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X5 @ X6 @ X7) @ 
% 0.20/0.49              (k1_tarski @ X8)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((k3_enumset1 @ X2 @ X2 @ X0 @ X1 @ X3)
% 0.20/0.49           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf(t72_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.49         ((k3_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18)
% 0.20/0.49           = (k2_enumset1 @ X15 @ X16 @ X17 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((k2_enumset1 @ X2 @ X0 @ X1 @ X3)
% 0.20/0.49           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.49         ((k2_enumset1 @ X12 @ X12 @ X13 @ X14)
% 0.20/0.49           = (k1_enumset1 @ X12 @ X13 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.49         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 0.20/0.49           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X5 @ X6 @ X7) @ 
% 0.20/0.49              (k1_tarski @ X8)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.20/0.49           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.49         ((k3_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18)
% 0.20/0.49           = (k2_enumset1 @ X15 @ X16 @ X17 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 0.20/0.49           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.20/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['7', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.49         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '13'])).
% 0.20/0.49  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
