%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O98kF5vG18

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:39 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :  210 ( 210 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t75_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
        ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
        = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) ),
    inference('cnf.neg',[status(esa)],[t75_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k5_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X22 @ X23 @ X24 ) @ ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    $false ),
    inference(simplify,[status(thm)],['6'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O98kF5vG18
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:20:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 13 iterations in 0.016s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.19/0.46                                           $i > $i).
% 0.19/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(sk_G_type, type, sk_G: $i).
% 0.19/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.46  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.46  thf(sk_F_type, type, sk_F: $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.46  thf(t75_enumset1, conjecture,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.19/0.46     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.19/0.46       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.19/0.46        ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.19/0.46          ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t75_enumset1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (((k6_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.19/0.46         != (k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t71_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.19/0.46         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 0.19/0.46           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 0.19/0.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.19/0.46  thf(l75_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.19/0.46     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.19/0.46       ( k2_xboole_0 @
% 0.19/0.46         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.19/0.47         X14 : $i]:
% 0.19/0.47         ((k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.19/0.47           = (k2_xboole_0 @ (k2_enumset1 @ X7 @ X8 @ X9 @ X10) @ 
% 0.19/0.47              (k2_enumset1 @ X11 @ X12 @ X13 @ X14)))),
% 0.19/0.47      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.47         ((k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.19/0.47           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.19/0.47              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 0.19/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.47  thf(t58_enumset1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.19/0.47     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.19/0.47       ( k2_xboole_0 @
% 0.19/0.47         ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ))).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.47         ((k5_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 0.19/0.47           = (k2_xboole_0 @ (k1_enumset1 @ X22 @ X23 @ X24) @ 
% 0.19/0.47              (k2_enumset1 @ X25 @ X26 @ X27 @ X28)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t58_enumset1])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.47         ((k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.19/0.47           = (k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3))),
% 0.19/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.19/0.47         != (k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G))),
% 0.19/0.47      inference('demod', [status(thm)], ['0', '5'])).
% 0.19/0.47  thf('7', plain, ($false), inference('simplify', [status(thm)], ['6'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
