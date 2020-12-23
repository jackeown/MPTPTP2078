%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.coH0hvcdCc

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:36 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :  190 ( 190 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(t74_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) ),
    inference('cnf.neg',[status(esa)],[t74_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(l68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) @ ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l68_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) @ ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    $false ),
    inference(simplify,[status(thm)],['6'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.coH0hvcdCc
% 0.16/0.36  % Computer   : n003.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 16:39:27 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.48  % Solved by: fo/fo7.sh
% 0.23/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.48  % done 5 iterations in 0.009s
% 0.23/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.48  % SZS output start Refutation
% 0.23/0.48  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.23/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.48  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.23/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.23/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.23/0.48  thf(sk_F_type, type, sk_F: $i).
% 0.23/0.48  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.23/0.48  thf(t74_enumset1, conjecture,
% 0.23/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.23/0.48     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.23/0.48       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.23/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.48    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.23/0.48        ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.23/0.48          ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )),
% 0.23/0.48    inference('cnf.neg', [status(esa)], [t74_enumset1])).
% 0.23/0.48  thf('0', plain,
% 0.23/0.48      (((k5_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.23/0.48         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(t71_enumset1, axiom,
% 0.23/0.48    (![A:$i,B:$i,C:$i]:
% 0.23/0.48     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.23/0.48  thf('1', plain,
% 0.23/0.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.48         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 0.23/0.48           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.23/0.48      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.23/0.48  thf(l68_enumset1, axiom,
% 0.23/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.23/0.48     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.23/0.48       ( k2_xboole_0 @
% 0.23/0.48         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ))).
% 0.23/0.48  thf('2', plain,
% 0.23/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.23/0.48         ((k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.23/0.48           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X7 @ X8 @ X9) @ 
% 0.23/0.48              (k1_enumset1 @ X10 @ X11 @ X12)))),
% 0.23/0.48      inference('cnf', [status(esa)], [l68_enumset1])).
% 0.23/0.48  thf('3', plain,
% 0.23/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.48         ((k5_enumset1 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 0.23/0.48           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.23/0.48              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 0.23/0.48      inference('sup+', [status(thm)], ['1', '2'])).
% 0.23/0.48  thf(l62_enumset1, axiom,
% 0.23/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.23/0.48     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.23/0.48       ( k2_xboole_0 @
% 0.23/0.48         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.23/0.48  thf('4', plain,
% 0.23/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.48         ((k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5)
% 0.23/0.48           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X1 @ X2) @ 
% 0.23/0.48              (k1_enumset1 @ X3 @ X4 @ X5)))),
% 0.23/0.48      inference('cnf', [status(esa)], [l62_enumset1])).
% 0.23/0.48  thf('5', plain,
% 0.23/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.48         ((k5_enumset1 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 0.23/0.48           = (k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3))),
% 0.23/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.23/0.48  thf('6', plain,
% 0.23/0.48      (((k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.23/0.48         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.23/0.48      inference('demod', [status(thm)], ['0', '5'])).
% 0.23/0.48  thf('7', plain, ($false), inference('simplify', [status(thm)], ['6'])).
% 0.23/0.48  
% 0.23/0.48  % SZS output end Refutation
% 0.23/0.48  
% 0.23/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
