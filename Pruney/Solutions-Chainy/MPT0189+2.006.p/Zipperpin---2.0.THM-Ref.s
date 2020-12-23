%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QNAnpOniyu

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:07 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  236 ( 262 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X7 @ X10 @ X9 @ X8 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('7',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','5','6'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X19 @ X21 @ X20 )
      = ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QNAnpOniyu
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:42:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.55  % Solved by: fo/fo7.sh
% 0.19/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.55  % done 129 iterations in 0.104s
% 0.19/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.55  % SZS output start Refutation
% 0.19/0.55  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.55  thf(t108_enumset1, conjecture,
% 0.19/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 0.19/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 0.19/0.55    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 0.19/0.55  thf('0', plain,
% 0.19/0.55      (((k2_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)
% 0.19/0.55         != (k2_enumset1 @ sk_B @ sk_A @ sk_C_1 @ sk_D))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(t44_enumset1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.19/0.55       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.19/0.55  thf('1', plain,
% 0.19/0.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.55         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 0.19/0.55           = (k2_xboole_0 @ (k1_tarski @ X11) @ (k1_enumset1 @ X12 @ X13 @ X14)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.19/0.55  thf(commutativity_k2_xboole_0, axiom,
% 0.19/0.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.19/0.55  thf('2', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.55  thf('3', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.55         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.19/0.55           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.55  thf(t46_enumset1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.19/0.55       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.19/0.55  thf('4', plain,
% 0.19/0.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.55         ((k2_enumset1 @ X15 @ X16 @ X17 @ X18)
% 0.19/0.55           = (k2_xboole_0 @ (k1_enumset1 @ X15 @ X16 @ X17) @ (k1_tarski @ X18)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.19/0.55  thf('5', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.55         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.55  thf(t107_enumset1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.19/0.55  thf('6', plain,
% 0.19/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.55         ((k2_enumset1 @ X7 @ X10 @ X9 @ X8)
% 0.19/0.55           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 0.19/0.55      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.19/0.55  thf('7', plain,
% 0.19/0.55      (((k2_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)
% 0.19/0.55         != (k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C_1))),
% 0.19/0.55      inference('demod', [status(thm)], ['0', '5', '6'])).
% 0.19/0.55  thf(t98_enumset1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.19/0.55  thf('8', plain,
% 0.19/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.55         ((k1_enumset1 @ X19 @ X21 @ X20) = (k1_enumset1 @ X19 @ X20 @ X21))),
% 0.19/0.55      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.19/0.55  thf('9', plain,
% 0.19/0.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.55         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 0.19/0.55           = (k2_xboole_0 @ (k1_tarski @ X11) @ (k1_enumset1 @ X12 @ X13 @ X14)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.19/0.55  thf('10', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.55         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1)
% 0.19/0.55           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.19/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.19/0.55  thf('11', plain,
% 0.19/0.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.55         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 0.19/0.55           = (k2_xboole_0 @ (k1_tarski @ X11) @ (k1_enumset1 @ X12 @ X13 @ X14)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.19/0.55  thf('12', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.55         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['10', '11'])).
% 0.19/0.55  thf('13', plain,
% 0.19/0.55      (((k2_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)
% 0.19/0.55         != (k2_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D))),
% 0.19/0.55      inference('demod', [status(thm)], ['7', '12'])).
% 0.19/0.55  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.19/0.55  
% 0.19/0.55  % SZS output end Refutation
% 0.19/0.55  
% 0.19/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
