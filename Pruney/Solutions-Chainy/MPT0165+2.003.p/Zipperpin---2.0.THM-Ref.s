%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.55eonl4o65

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:42 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :  237 ( 237 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t81_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F )
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) ),
    inference('cnf.neg',[status(esa)],[t81_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X17 @ X17 @ X18 @ X19 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k6_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) @ ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t58_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k5_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) @ ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k5_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k4_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('7',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['0','5','6'])).

thf('8',plain,(
    $false ),
    inference(simplify,[status(thm)],['7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.55eonl4o65
% 0.14/0.37  % Computer   : n014.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 11:44:07 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 35 iterations in 0.023s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.24/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.51  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.24/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.24/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.24/0.51  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.24/0.51  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.24/0.51                                           $i > $i).
% 0.24/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.24/0.51  thf(t81_enumset1, conjecture,
% 0.24/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.24/0.51     ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F ) =
% 0.24/0.51       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.24/0.51        ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F ) =
% 0.24/0.51          ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t81_enumset1])).
% 0.24/0.51  thf('0', plain,
% 0.24/0.51      (((k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.24/0.51         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(t71_enumset1, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.24/0.51  thf('1', plain,
% 0.24/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.24/0.51         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 0.24/0.51           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 0.24/0.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.24/0.51  thf(l75_enumset1, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.24/0.51     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.24/0.51       ( k2_xboole_0 @
% 0.24/0.51         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.24/0.51  thf('2', plain,
% 0.24/0.51      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.51         ((k6_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 0.24/0.51           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X3 @ X4 @ X5) @ 
% 0.24/0.51              (k2_enumset1 @ X6 @ X7 @ X8 @ X9)))),
% 0.24/0.51      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.24/0.51  thf('3', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.24/0.51         ((k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.24/0.51           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.24/0.51              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 0.24/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.24/0.51  thf(t58_enumset1, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.24/0.51     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.24/0.51       ( k2_xboole_0 @
% 0.24/0.51         ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ))).
% 0.24/0.51  thf('4', plain,
% 0.24/0.51      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.51         ((k5_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.24/0.51           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ 
% 0.24/0.51              (k2_enumset1 @ X13 @ X14 @ X15 @ X16)))),
% 0.24/0.51      inference('cnf', [status(esa)], [t58_enumset1])).
% 0.24/0.51  thf('5', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.24/0.51         ((k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.24/0.51           = (k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3))),
% 0.24/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.24/0.51  thf(t74_enumset1, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.24/0.51     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.24/0.51       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.24/0.51         ((k5_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34)
% 0.24/0.51           = (k4_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34))),
% 0.24/0.51      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.24/0.51  thf('7', plain,
% 0.24/0.51      (((k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.24/0.51         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.24/0.51      inference('demod', [status(thm)], ['0', '5', '6'])).
% 0.24/0.51  thf('8', plain, ($false), inference('simplify', [status(thm)], ['7'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
