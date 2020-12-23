%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H7mb7g3ttz

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:14 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   38 (  40 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  337 ( 357 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t64_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) @ ( k3_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k4_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k1_tarski @ X33 ) @ ( k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k2_tarski @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(t63_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('12',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i,X64: $i,X65: $i,X66: $i,X67: $i] :
      ( ( k6_enumset1 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67 )
      = ( k2_xboole_0 @ ( k2_tarski @ X60 @ X61 ) @ ( k4_enumset1 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[t63_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H7mb7g3ttz
% 0.14/0.38  % Computer   : n025.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 10:05:36 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 0.25/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.57  % Solved by: fo/fo7.sh
% 0.25/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.57  % done 85 iterations in 0.080s
% 0.25/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.57  % SZS output start Refutation
% 0.25/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.25/0.57  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.25/0.57                                           $i > $i).
% 0.25/0.57  thf(sk_F_type, type, sk_F: $i).
% 0.25/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.25/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.25/0.57  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.25/0.57  thf(sk_G_type, type, sk_G: $i).
% 0.25/0.57  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.25/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.25/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.25/0.57  thf(sk_H_type, type, sk_H: $i).
% 0.25/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.57  thf(t64_enumset1, conjecture,
% 0.25/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.25/0.57     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.25/0.57       ( k2_xboole_0 @
% 0.25/0.57         ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ))).
% 0.25/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.57    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.25/0.57        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.25/0.57          ( k2_xboole_0 @
% 0.25/0.57            ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ) )),
% 0.25/0.57    inference('cnf.neg', [status(esa)], [t64_enumset1])).
% 0.25/0.57  thf('0', plain,
% 0.25/0.57      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.25/0.57         != (k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_C) @ 
% 0.25/0.57             (k3_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf(t51_enumset1, axiom,
% 0.25/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.25/0.57     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.25/0.57       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.25/0.57  thf('1', plain,
% 0.25/0.57      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.25/0.57         ((k4_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38)
% 0.25/0.57           = (k2_xboole_0 @ (k1_tarski @ X33) @ 
% 0.25/0.57              (k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38)))),
% 0.25/0.57      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.25/0.57  thf(t41_enumset1, axiom,
% 0.25/0.57    (![A:$i,B:$i]:
% 0.25/0.57     ( ( k2_tarski @ A @ B ) =
% 0.25/0.57       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.25/0.57  thf('2', plain,
% 0.25/0.57      (![X10 : $i, X11 : $i]:
% 0.25/0.57         ((k2_tarski @ X10 @ X11)
% 0.25/0.57           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X11)))),
% 0.25/0.57      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.25/0.57  thf('3', plain,
% 0.25/0.57      (![X10 : $i, X11 : $i]:
% 0.25/0.57         ((k2_tarski @ X10 @ X11)
% 0.25/0.57           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X11)))),
% 0.25/0.57      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.25/0.57  thf(t4_xboole_1, axiom,
% 0.25/0.57    (![A:$i,B:$i,C:$i]:
% 0.25/0.57     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.25/0.57       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.25/0.57  thf('4', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.57         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.25/0.57           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.25/0.57      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.25/0.57  thf('5', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.57         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.25/0.57           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.25/0.57              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.25/0.57      inference('sup+', [status(thm)], ['3', '4'])).
% 0.25/0.57  thf('6', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.57         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.25/0.57           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.25/0.57      inference('sup+', [status(thm)], ['2', '5'])).
% 0.25/0.57  thf(t42_enumset1, axiom,
% 0.25/0.57    (![A:$i,B:$i,C:$i]:
% 0.25/0.57     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.25/0.57       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.25/0.57  thf('7', plain,
% 0.25/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.25/0.57         ((k1_enumset1 @ X12 @ X13 @ X14)
% 0.25/0.57           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k2_tarski @ X13 @ X14)))),
% 0.25/0.57      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.25/0.57  thf('8', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.57         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.25/0.57           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.25/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.25/0.57  thf('9', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.57         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.25/0.57           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.25/0.57      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.25/0.57  thf('10', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.57         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.25/0.57           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.25/0.57              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.25/0.57      inference('sup+', [status(thm)], ['8', '9'])).
% 0.25/0.57  thf('11', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.25/0.57         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.25/0.57           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.25/0.57           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.25/0.57              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.25/0.57      inference('sup+', [status(thm)], ['1', '10'])).
% 0.25/0.57  thf(t63_enumset1, axiom,
% 0.25/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.25/0.57     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.25/0.57       ( k2_xboole_0 @
% 0.25/0.57         ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.25/0.57  thf('12', plain,
% 0.25/0.57      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i, 
% 0.25/0.57         X67 : $i]:
% 0.25/0.57         ((k6_enumset1 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67)
% 0.25/0.57           = (k2_xboole_0 @ (k2_tarski @ X60 @ X61) @ 
% 0.25/0.57              (k4_enumset1 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67)))),
% 0.25/0.57      inference('cnf', [status(esa)], [t63_enumset1])).
% 0.25/0.57  thf('13', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.25/0.57         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.25/0.57           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.25/0.57           = (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.25/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.25/0.57  thf('14', plain,
% 0.25/0.57      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.25/0.57         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.25/0.57             sk_H))),
% 0.25/0.57      inference('demod', [status(thm)], ['0', '13'])).
% 0.25/0.57  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.25/0.57  
% 0.25/0.57  % SZS output end Refutation
% 0.25/0.57  
% 0.43/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
