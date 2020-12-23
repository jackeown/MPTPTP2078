%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZUtvWyL4dH

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:02 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  419 ( 504 expanded)
%              Number of equality atoms :   30 (  36 expanded)
%              Maximal formula depth    :   16 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k5_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k4_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k5_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k5_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k5_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 @ X5 )
      = ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k4_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZUtvWyL4dH
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:49:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.51/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.70  % Solved by: fo/fo7.sh
% 0.51/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.70  % done 437 iterations in 0.238s
% 0.51/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.70  % SZS output start Refutation
% 0.51/0.70  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.51/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.51/0.70  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.51/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.70  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.51/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.70  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.51/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.70  thf(t103_enumset1, conjecture,
% 0.51/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.70     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 0.51/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.70    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.70        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ) )),
% 0.51/0.70    inference('cnf.neg', [status(esa)], [t103_enumset1])).
% 0.51/0.70  thf('0', plain,
% 0.51/0.70      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.51/0.70         != (k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(t74_enumset1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.51/0.70     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.51/0.70       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.51/0.70  thf('1', plain,
% 0.51/0.70      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.51/0.70         ((k5_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.51/0.70           = (k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30))),
% 0.51/0.70      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.51/0.70  thf(t73_enumset1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.51/0.70     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.51/0.70       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.51/0.70  thf('2', plain,
% 0.51/0.70      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.51/0.70         ((k4_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.51/0.70           = (k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24))),
% 0.51/0.70      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.51/0.70  thf('3', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.51/0.70         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.51/0.70           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.51/0.70      inference('sup+', [status(thm)], ['1', '2'])).
% 0.51/0.70  thf(t72_enumset1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.70     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.51/0.70  thf('4', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.51/0.70         ((k3_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19)
% 0.51/0.70           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 0.51/0.70      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.51/0.70  thf('5', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.51/0.70         ((k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.51/0.70           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.51/0.70      inference('sup+', [status(thm)], ['3', '4'])).
% 0.51/0.70  thf('6', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.51/0.70         ((k3_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19)
% 0.51/0.70           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 0.51/0.70      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.51/0.70  thf(commutativity_k2_tarski, axiom,
% 0.51/0.70    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.51/0.70  thf('7', plain,
% 0.51/0.70      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.51/0.70      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.51/0.70  thf(t60_enumset1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.51/0.70     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.51/0.70       ( k2_xboole_0 @
% 0.51/0.70         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 0.51/0.70  thf('8', plain,
% 0.51/0.70      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.51/0.70         ((k5_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.51/0.70           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8) @ 
% 0.51/0.70              (k2_tarski @ X9 @ X10)))),
% 0.51/0.70      inference('cnf', [status(esa)], [t60_enumset1])).
% 0.51/0.70  thf('9', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.51/0.70         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X0 @ X1)
% 0.51/0.70           = (k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.51/0.70              (k2_tarski @ X1 @ X0)))),
% 0.51/0.70      inference('sup+', [status(thm)], ['7', '8'])).
% 0.51/0.70  thf('10', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.51/0.70         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 @ X5)
% 0.51/0.70           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.51/0.70              (k2_tarski @ X5 @ X4)))),
% 0.51/0.70      inference('sup+', [status(thm)], ['6', '9'])).
% 0.51/0.70  thf('11', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.51/0.70         ((k3_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19)
% 0.51/0.70           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 0.51/0.70      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.51/0.70  thf('12', plain,
% 0.51/0.70      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.51/0.70         ((k5_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.51/0.70           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8) @ 
% 0.51/0.70              (k2_tarski @ X9 @ X10)))),
% 0.51/0.70      inference('cnf', [status(esa)], [t60_enumset1])).
% 0.51/0.70  thf('13', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.51/0.70         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 0.51/0.70           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.51/0.70              (k2_tarski @ X5 @ X4)))),
% 0.51/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.51/0.70  thf('14', plain,
% 0.51/0.70      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.51/0.70         ((k5_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.51/0.70           = (k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30))),
% 0.51/0.70      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.51/0.70  thf('15', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.51/0.70         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.51/0.70           (k2_tarski @ X1 @ X0)) = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.51/0.70      inference('sup+', [status(thm)], ['13', '14'])).
% 0.51/0.70  thf('16', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.51/0.70         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 @ X5)
% 0.51/0.70           = (k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4))),
% 0.51/0.70      inference('demod', [status(thm)], ['10', '15'])).
% 0.51/0.70  thf('17', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.51/0.70         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.51/0.70           = (k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X0 @ X1))),
% 0.51/0.70      inference('sup+', [status(thm)], ['5', '16'])).
% 0.51/0.70  thf('18', plain,
% 0.51/0.70      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.51/0.70         ((k4_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.51/0.70           = (k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24))),
% 0.51/0.70      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.51/0.70  thf('19', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.51/0.70         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.51/0.70           = (k3_enumset1 @ X3 @ X3 @ X2 @ X0 @ X1))),
% 0.51/0.70      inference('demod', [status(thm)], ['17', '18'])).
% 0.51/0.70  thf('20', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.51/0.70         ((k3_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19)
% 0.51/0.70           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 0.51/0.70      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.51/0.70  thf('21', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.51/0.70         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 0.51/0.70      inference('sup+', [status(thm)], ['19', '20'])).
% 0.51/0.70  thf('22', plain,
% 0.51/0.70      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.51/0.70         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.51/0.70      inference('demod', [status(thm)], ['0', '21'])).
% 0.51/0.70  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.51/0.70  
% 0.51/0.70  % SZS output end Refutation
% 0.51/0.70  
% 0.51/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
