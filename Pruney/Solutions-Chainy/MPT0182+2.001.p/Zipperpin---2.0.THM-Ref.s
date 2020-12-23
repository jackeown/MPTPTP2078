%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u0bjCqtvJJ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:58 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   32 (  46 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  230 ( 387 expanded)
%              Number of equality atoms :   22 (  36 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t99_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_enumset1 @ A @ B @ C )
        = ( k1_enumset1 @ B @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t99_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_B @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_enumset1 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X42 @ X42 @ X43 @ X44 )
      = ( k1_enumset1 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X42 @ X42 @ X43 @ X44 )
      = ( k1_enumset1 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) @ ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u0bjCqtvJJ
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:14:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.40/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.57  % Solved by: fo/fo7.sh
% 0.40/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.57  % done 259 iterations in 0.115s
% 0.40/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.57  % SZS output start Refutation
% 0.40/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.57  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.40/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.40/0.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.40/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.57  thf(t99_enumset1, conjecture,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ))).
% 0.40/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.57        ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ) )),
% 0.40/0.57    inference('cnf.neg', [status(esa)], [t99_enumset1])).
% 0.40/0.57  thf('0', plain,
% 0.40/0.57      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.40/0.57         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(commutativity_k2_tarski, axiom,
% 0.40/0.57    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.40/0.57  thf('1', plain,
% 0.40/0.57      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.40/0.57      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.40/0.57  thf(t72_enumset1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.57     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.40/0.57  thf('2', plain,
% 0.40/0.57      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.40/0.57         ((k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48)
% 0.40/0.57           = (k2_enumset1 @ X45 @ X46 @ X47 @ X48))),
% 0.40/0.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.40/0.57  thf(t71_enumset1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.40/0.57  thf('3', plain,
% 0.40/0.57      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.40/0.57         ((k2_enumset1 @ X42 @ X42 @ X43 @ X44)
% 0.40/0.57           = (k1_enumset1 @ X42 @ X43 @ X44))),
% 0.40/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.40/0.57  thf('4', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.40/0.57  thf('5', plain,
% 0.40/0.57      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.40/0.57         ((k2_enumset1 @ X42 @ X42 @ X43 @ X44)
% 0.40/0.57           = (k1_enumset1 @ X42 @ X43 @ X44))),
% 0.40/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.40/0.57  thf(t50_enumset1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.40/0.57     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.40/0.57       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.40/0.57  thf('6', plain,
% 0.40/0.57      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.40/0.57         ((k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.40/0.57           = (k2_xboole_0 @ (k2_enumset1 @ X26 @ X27 @ X28 @ X29) @ 
% 0.40/0.57              (k1_tarski @ X30)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.40/0.57  thf('7', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.57         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.40/0.57           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.40/0.57      inference('sup+', [status(thm)], ['5', '6'])).
% 0.40/0.57  thf('8', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.40/0.57           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.40/0.57      inference('sup+', [status(thm)], ['4', '7'])).
% 0.40/0.57  thf(t70_enumset1, axiom,
% 0.40/0.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.40/0.57  thf('9', plain,
% 0.40/0.57      (![X40 : $i, X41 : $i]:
% 0.40/0.57         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.40/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.57  thf('10', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.40/0.57           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.40/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.57  thf('11', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((k1_enumset1 @ X0 @ X1 @ X2)
% 0.40/0.57           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.40/0.57      inference('sup+', [status(thm)], ['1', '10'])).
% 0.40/0.57  thf('12', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.40/0.57           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.40/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.57  thf('13', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.40/0.57  thf('14', plain,
% 0.40/0.57      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.40/0.57         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.40/0.57      inference('demod', [status(thm)], ['0', '13'])).
% 0.40/0.57  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.40/0.57  
% 0.40/0.57  % SZS output end Refutation
% 0.40/0.57  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
