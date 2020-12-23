%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7JJ402iH7L

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:09 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   29 (  36 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  223 ( 311 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X14 @ X12 @ X13 )
      = ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( k2_enumset1 @ X55 @ X55 @ X56 @ X57 )
      = ( k1_enumset1 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X19 @ X20 @ X21 @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('5',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k3_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 )
      = ( k2_enumset1 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X1 @ X0 @ X2 @ X3 ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t104_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X17 @ X16 @ X18 )
      = ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('11',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','9','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7JJ402iH7L
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:02:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 316 iterations in 0.207s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.67  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.46/0.67  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.46/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.67  thf(t108_enumset1, conjecture,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 0.46/0.67  thf('0', plain,
% 0.46/0.67      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.46/0.67         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(t100_enumset1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.67         ((k1_enumset1 @ X14 @ X12 @ X13) = (k1_enumset1 @ X12 @ X13 @ X14))),
% 0.46/0.67      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.46/0.67  thf(t71_enumset1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.46/0.67  thf('2', plain,
% 0.46/0.67      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.46/0.67         ((k2_enumset1 @ X55 @ X55 @ X56 @ X57)
% 0.46/0.67           = (k1_enumset1 @ X55 @ X56 @ X57))),
% 0.46/0.67      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.46/0.67  thf(t50_enumset1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.46/0.67     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.46/0.67       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.46/0.67  thf('3', plain,
% 0.46/0.67      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.67         ((k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.46/0.67           = (k2_xboole_0 @ (k2_enumset1 @ X19 @ X20 @ X21 @ X22) @ 
% 0.46/0.67              (k1_tarski @ X23)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.46/0.67           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf(t72_enumset1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 0.46/0.67         ((k3_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61)
% 0.46/0.67           = (k2_enumset1 @ X58 @ X59 @ X60 @ X61))),
% 0.46/0.67      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.46/0.67           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['4', '5'])).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.46/0.67           = (k2_enumset1 @ X1 @ X0 @ X2 @ X3))),
% 0.46/0.67      inference('sup+', [status(thm)], ['1', '6'])).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.46/0.67           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['4', '5'])).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X3 @ X2 @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['7', '8'])).
% 0.46/0.67  thf(t104_enumset1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.67         ((k2_enumset1 @ X15 @ X17 @ X16 @ X18)
% 0.46/0.67           = (k2_enumset1 @ X15 @ X16 @ X17 @ X18))),
% 0.46/0.67      inference('cnf', [status(esa)], [t104_enumset1])).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.46/0.67         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.46/0.67      inference('demod', [status(thm)], ['0', '9', '10'])).
% 0.46/0.67  thf('12', plain, ($false), inference('simplify', [status(thm)], ['11'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
