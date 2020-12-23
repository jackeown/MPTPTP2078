%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5punTj9UEz

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:02 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   45 (  67 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  441 ( 770 expanded)
%              Number of equality atoms :   32 (  54 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t103_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ B @ D @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t103_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k6_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 )
      = ( k5_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k5_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k4_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k4_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k6_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 ) @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X6 @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X14 @ X14 @ X15 @ X16 )
      = ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X0 @ X1 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5punTj9UEz
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:32:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 245 iterations in 0.127s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.38/0.57                                           $i > $i).
% 0.38/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.57  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.38/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.38/0.57  thf(t103_enumset1, conjecture,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t103_enumset1])).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.57         != (k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(commutativity_k2_tarski, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.38/0.57  thf(t75_enumset1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.38/0.57     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.38/0.57       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.38/0.57         ((k6_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38)
% 0.38/0.57           = (k5_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38))),
% 0.38/0.57      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.38/0.57  thf(t74_enumset1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.57     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.38/0.57       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.57         ((k5_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.38/0.57           = (k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31))),
% 0.38/0.57      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.57         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.38/0.57           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.57  thf(t73_enumset1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.38/0.57     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.38/0.57       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.57         ((k4_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.38/0.57           = (k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25))),
% 0.38/0.57      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.57         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.38/0.57           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.57         ((k4_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.38/0.57           = (k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25))),
% 0.38/0.57      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.38/0.57  thf(t67_enumset1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.38/0.57     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.38/0.57       ( k2_xboole_0 @
% 0.38/0.57         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, 
% 0.38/0.57         X11 : $i]:
% 0.38/0.57         ((k6_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.38/0.57           = (k2_xboole_0 @ (k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9) @ 
% 0.38/0.57              (k2_tarski @ X10 @ X11)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t67_enumset1])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.57         ((k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5)
% 0.38/0.57           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.38/0.57              (k2_tarski @ X6 @ X5)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.57         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.38/0.57           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2) @ 
% 0.38/0.57              (k2_tarski @ X1 @ X0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['6', '9'])).
% 0.38/0.57  thf(t72_enumset1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.57         ((k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20)
% 0.38/0.57           = (k2_enumset1 @ X17 @ X18 @ X19 @ X20))),
% 0.38/0.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.38/0.57  thf(t71_enumset1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.57         ((k2_enumset1 @ X14 @ X14 @ X15 @ X16)
% 0.38/0.57           = (k1_enumset1 @ X14 @ X15 @ X16))),
% 0.38/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.57         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.38/0.57           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 0.38/0.57              (k2_tarski @ X1 @ X0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['10', '13'])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.57         ((k3_enumset1 @ X4 @ X3 @ X2 @ X0 @ X1)
% 0.38/0.57           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 0.38/0.57              (k2_tarski @ X1 @ X0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['1', '14'])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.57         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.38/0.57           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 0.38/0.57              (k2_tarski @ X1 @ X0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['10', '13'])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.57         ((k3_enumset1 @ X4 @ X3 @ X2 @ X0 @ X1)
% 0.38/0.57           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.57         ((k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20)
% 0.38/0.57           = (k2_enumset1 @ X17 @ X18 @ X19 @ X20))),
% 0.38/0.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.57         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.38/0.57           = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.57         ((k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20)
% 0.38/0.57           = (k2_enumset1 @ X17 @ X18 @ X19 @ X20))),
% 0.38/0.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.57         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.57         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.38/0.57      inference('demod', [status(thm)], ['0', '21'])).
% 0.38/0.57  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
