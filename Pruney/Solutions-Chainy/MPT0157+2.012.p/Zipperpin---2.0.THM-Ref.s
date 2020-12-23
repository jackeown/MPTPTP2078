%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.unyt9H1IGL

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 (  43 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  398 ( 406 expanded)
%              Number of equality atoms :   28 (  29 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t64_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k6_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X13 @ X14 @ X15 ) @ ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t64_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X1 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k2_enumset1 @ X32 @ X32 @ X33 @ X34 )
      = ( k1_enumset1 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('7',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k3_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_enumset1 @ X35 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t66_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k6_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 ) @ ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X6 @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X4 @ X4 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['0','16'])).

thf('18',plain,(
    $false ),
    inference(simplify,[status(thm)],['17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.unyt9H1IGL
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:00 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 117 iterations in 0.073s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.52  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.19/0.52                                           $i > $i).
% 0.19/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.19/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.52  thf(t73_enumset1, conjecture,
% 0.19/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.52     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.19/0.52       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.52        ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.19/0.52          ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t73_enumset1])).
% 0.19/0.52  thf('0', plain,
% 0.19/0.52      (((k4_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.52         != (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t70_enumset1, axiom,
% 0.19/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.52  thf('1', plain,
% 0.19/0.52      (![X30 : $i, X31 : $i]:
% 0.19/0.52         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 0.19/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.52  thf(t64_enumset1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.19/0.52     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.19/0.52       ( k2_xboole_0 @
% 0.19/0.52         ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ))).
% 0.19/0.52  thf('2', plain,
% 0.19/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, 
% 0.19/0.52         X20 : $i]:
% 0.19/0.52         ((k6_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.19/0.52           = (k2_xboole_0 @ (k1_enumset1 @ X13 @ X14 @ X15) @ 
% 0.19/0.52              (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t64_enumset1])).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.52         ((k6_enumset1 @ X1 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2)
% 0.19/0.52           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 0.19/0.52              (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2)))),
% 0.19/0.52      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.52  thf(t71_enumset1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.19/0.52         ((k2_enumset1 @ X32 @ X32 @ X33 @ X34)
% 0.19/0.52           = (k1_enumset1 @ X32 @ X33 @ X34))),
% 0.19/0.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.19/0.52  thf('5', plain,
% 0.19/0.52      (![X30 : $i, X31 : $i]:
% 0.19/0.52         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 0.19/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.19/0.52      inference('sup+', [status(thm)], ['4', '5'])).
% 0.19/0.52  thf(t72_enumset1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.52     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.19/0.52         ((k3_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38)
% 0.19/0.52           = (k2_enumset1 @ X35 @ X36 @ X37 @ X38))),
% 0.19/0.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.19/0.52  thf(t66_enumset1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.19/0.52     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.19/0.52       ( k2_xboole_0 @
% 0.19/0.52         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 0.19/0.52  thf('8', plain,
% 0.19/0.52      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, 
% 0.19/0.52         X28 : $i]:
% 0.19/0.52         ((k6_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 0.19/0.52           = (k2_xboole_0 @ (k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25) @ 
% 0.19/0.52              (k1_enumset1 @ X26 @ X27 @ X28)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t66_enumset1])).
% 0.19/0.52  thf('9', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.52         ((k6_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4)
% 0.19/0.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.19/0.52              (k1_enumset1 @ X6 @ X5 @ X4)))),
% 0.19/0.52      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.52  thf('10', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.52         ((k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 0.19/0.52           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 0.19/0.52              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 0.19/0.52      inference('sup+', [status(thm)], ['6', '9'])).
% 0.19/0.52  thf(t48_enumset1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.52     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.19/0.52       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.19/0.52  thf('11', plain,
% 0.19/0.52      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.52         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.19/0.52           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ 
% 0.19/0.52              (k1_enumset1 @ X4 @ X5 @ X6)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.19/0.52  thf('12', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.52         ((k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 0.19/0.52           = (k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2))),
% 0.19/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.52  thf('13', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.52         ((k2_xboole_0 @ (k2_tarski @ X4 @ X4) @ 
% 0.19/0.52           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.19/0.52           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.19/0.52      inference('sup+', [status(thm)], ['3', '12'])).
% 0.19/0.52  thf(t69_enumset1, axiom,
% 0.19/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 0.19/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.52  thf(t51_enumset1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.52     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.19/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.19/0.52  thf('15', plain,
% 0.19/0.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.52         ((k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.19/0.52           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.19/0.52              (k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.52         ((k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.19/0.52           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.19/0.52      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.19/0.52         != (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.19/0.52      inference('demod', [status(thm)], ['0', '16'])).
% 0.19/0.52  thf('18', plain, ($false), inference('simplify', [status(thm)], ['17'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
