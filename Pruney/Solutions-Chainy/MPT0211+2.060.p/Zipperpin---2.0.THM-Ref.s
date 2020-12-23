%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zWHLwVpkRV

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:37 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  242 ( 260 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t137_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t137_enumset1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X8 @ X6 @ X7 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X8 @ X6 @ X7 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('3',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('5',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X8 @ X6 @ X7 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k2_tarski @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X28 @ X30 @ X29 )
      = ( k1_enumset1 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('14',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['5','12','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zWHLwVpkRV
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.55/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.75  % Solved by: fo/fo7.sh
% 0.55/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.75  % done 524 iterations in 0.306s
% 0.55/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.75  % SZS output start Refutation
% 0.55/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.55/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.75  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.55/0.75  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.55/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.55/0.75  thf(t137_enumset1, conjecture,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.55/0.75       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.55/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.75    (~( ![A:$i,B:$i,C:$i]:
% 0.55/0.75        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.55/0.75          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.55/0.75    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.55/0.75  thf('0', plain,
% 0.55/0.75      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.55/0.75         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(t100_enumset1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 0.55/0.75  thf('1', plain,
% 0.55/0.75      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.55/0.75         ((k1_enumset1 @ X8 @ X6 @ X7) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.55/0.75      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.55/0.75  thf('2', plain,
% 0.55/0.75      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.55/0.75         ((k1_enumset1 @ X8 @ X6 @ X7) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.55/0.75      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.55/0.75  thf('3', plain,
% 0.55/0.75      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.55/0.75         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.55/0.75  thf(l53_enumset1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.75     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.55/0.75       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.55/0.75  thf('4', plain,
% 0.55/0.75      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.55/0.75         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.55/0.75           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.55/0.75      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.55/0.75  thf('5', plain,
% 0.55/0.75      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.55/0.75         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['3', '4'])).
% 0.55/0.75  thf('6', plain,
% 0.55/0.75      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.55/0.75         ((k1_enumset1 @ X8 @ X6 @ X7) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.55/0.75      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.55/0.75  thf(t70_enumset1, axiom,
% 0.55/0.75    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.55/0.75  thf('7', plain,
% 0.55/0.75      (![X23 : $i, X24 : $i]:
% 0.55/0.75         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.55/0.75      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.55/0.75  thf('8', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.55/0.75      inference('sup+', [status(thm)], ['6', '7'])).
% 0.55/0.75  thf(t44_enumset1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.75     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.55/0.75       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.55/0.75  thf('9', plain,
% 0.55/0.75      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.55/0.75         ((k2_enumset1 @ X18 @ X19 @ X20 @ X21)
% 0.55/0.75           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_enumset1 @ X19 @ X20 @ X21)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.55/0.75  thf('10', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.75         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1)
% 0.55/0.75           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.55/0.75      inference('sup+', [status(thm)], ['8', '9'])).
% 0.55/0.75  thf(t42_enumset1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.55/0.75       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.55/0.75  thf('11', plain,
% 0.55/0.75      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.55/0.75         ((k1_enumset1 @ X12 @ X13 @ X14)
% 0.55/0.75           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k2_tarski @ X13 @ X14)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.55/0.75  thf('12', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.75         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.55/0.75      inference('demod', [status(thm)], ['10', '11'])).
% 0.55/0.75  thf(t98_enumset1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.55/0.75  thf('13', plain,
% 0.55/0.75      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.75         ((k1_enumset1 @ X28 @ X30 @ X29) = (k1_enumset1 @ X28 @ X29 @ X30))),
% 0.55/0.75      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.55/0.75  thf('14', plain,
% 0.55/0.75      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 0.55/0.75         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['5', '12', '13'])).
% 0.55/0.75  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.55/0.75  
% 0.55/0.75  % SZS output end Refutation
% 0.55/0.75  
% 0.55/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
