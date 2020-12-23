%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hOE7vnKA3K

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:32 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  260 ( 273 expanded)
%              Number of equality atoms :   20 (  21 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t72_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k3_enumset1 @ A @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ B @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t72_enumset1])).

thf('0',plain,(
    ( k3_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k2_enumset1 @ X63 @ X63 @ X64 @ X65 )
      = ( k1_enumset1 @ X63 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hOE7vnKA3K
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:12:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.74/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/0.91  % Solved by: fo/fo7.sh
% 0.74/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.91  % done 637 iterations in 0.455s
% 0.74/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/0.91  % SZS output start Refutation
% 0.74/0.91  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.74/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.74/0.91  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.74/0.91  thf(sk_D_type, type, sk_D: $i).
% 0.74/0.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.74/0.91  thf(sk_C_type, type, sk_C: $i).
% 0.74/0.91  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.74/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.91  thf(t72_enumset1, conjecture,
% 0.74/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.91     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.74/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.91    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.91        ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ) )),
% 0.74/0.91    inference('cnf.neg', [status(esa)], [t72_enumset1])).
% 0.74/0.91  thf('0', plain,
% 0.74/0.91      (((k3_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.74/0.91         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.74/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.91  thf(t71_enumset1, axiom,
% 0.74/0.91    (![A:$i,B:$i,C:$i]:
% 0.74/0.91     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.74/0.91  thf('1', plain,
% 0.74/0.91      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.74/0.91         ((k2_enumset1 @ X63 @ X63 @ X64 @ X65)
% 0.74/0.91           = (k1_enumset1 @ X63 @ X64 @ X65))),
% 0.74/0.91      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.74/0.91  thf(t46_enumset1, axiom,
% 0.74/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.91     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.74/0.91       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.74/0.91  thf('2', plain,
% 0.74/0.91      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.74/0.91         ((k2_enumset1 @ X15 @ X16 @ X17 @ X18)
% 0.74/0.91           = (k2_xboole_0 @ (k1_enumset1 @ X15 @ X16 @ X17) @ (k1_tarski @ X18)))),
% 0.74/0.91      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.74/0.91  thf('3', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.91         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 0.74/0.91           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 0.74/0.91              (k1_tarski @ X3)))),
% 0.74/0.91      inference('sup+', [status(thm)], ['1', '2'])).
% 0.74/0.91  thf('4', plain,
% 0.74/0.91      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.74/0.91         ((k2_enumset1 @ X15 @ X16 @ X17 @ X18)
% 0.74/0.91           = (k2_xboole_0 @ (k1_enumset1 @ X15 @ X16 @ X17) @ (k1_tarski @ X18)))),
% 0.74/0.91      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.74/0.91  thf(t44_enumset1, axiom,
% 0.74/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.91     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.74/0.91       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.74/0.91  thf('5', plain,
% 0.74/0.91      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.74/0.91         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 0.74/0.91           = (k2_xboole_0 @ (k1_tarski @ X11) @ (k1_enumset1 @ X12 @ X13 @ X14)))),
% 0.74/0.91      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.74/0.91  thf(t4_xboole_1, axiom,
% 0.74/0.91    (![A:$i,B:$i,C:$i]:
% 0.74/0.91     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.74/0.91       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.74/0.91  thf('6', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.91         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.74/0.91           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.74/0.91      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.74/0.91  thf('7', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.74/0.91         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.74/0.91           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.74/0.91              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 0.74/0.91      inference('sup+', [status(thm)], ['5', '6'])).
% 0.74/0.91  thf('8', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.74/0.91         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.74/0.91           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.74/0.91              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.74/0.91      inference('sup+', [status(thm)], ['4', '7'])).
% 0.74/0.91  thf(t47_enumset1, axiom,
% 0.74/0.91    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.74/0.91     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.74/0.91       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.74/0.91  thf('9', plain,
% 0.74/0.91      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.74/0.91         ((k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.74/0.91           = (k2_xboole_0 @ (k1_tarski @ X19) @ 
% 0.74/0.91              (k2_enumset1 @ X20 @ X21 @ X22 @ X23)))),
% 0.74/0.91      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.74/0.91  thf('10', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.74/0.91         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.74/0.91           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.74/0.91      inference('demod', [status(thm)], ['8', '9'])).
% 0.74/0.91  thf('11', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.91         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 0.74/0.91           = (k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3))),
% 0.74/0.91      inference('demod', [status(thm)], ['3', '10'])).
% 0.74/0.91  thf('12', plain,
% 0.74/0.91      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.74/0.91         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.74/0.91      inference('demod', [status(thm)], ['0', '11'])).
% 0.74/0.91  thf('13', plain, ($false), inference('simplify', [status(thm)], ['12'])).
% 0.74/0.91  
% 0.74/0.91  % SZS output end Refutation
% 0.74/0.91  
% 0.74/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
