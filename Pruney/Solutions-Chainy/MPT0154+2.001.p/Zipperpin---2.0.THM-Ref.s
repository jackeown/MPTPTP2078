%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2RettVjUVU

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:21 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  299 ( 372 expanded)
%              Number of equality atoms :   33 (  42 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t70_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_enumset1 @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t70_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k2_tarski @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

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
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k2_tarski @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X40 @ X41 @ X42 )
      = ( k2_xboole_0 @ ( k1_tarski @ X40 ) @ ( k2_tarski @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k2_tarski @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('14',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k2_enumset1 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X43 @ X44 @ X45 ) @ ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('19',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k2_tarski @ X34 @ X35 ) @ ( k2_tarski @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X40 @ X41 @ X42 )
      = ( k2_xboole_0 @ ( k1_tarski @ X40 ) @ ( k2_tarski @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ( k2_tarski @ sk_B @ sk_A )
 != ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2RettVjUVU
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:22:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 1.64/1.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.64/1.89  % Solved by: fo/fo7.sh
% 1.64/1.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.64/1.89  % done 2062 iterations in 1.419s
% 1.64/1.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.64/1.89  % SZS output start Refutation
% 1.64/1.89  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.64/1.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.64/1.89  thf(sk_A_type, type, sk_A: $i).
% 1.64/1.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.64/1.89  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.64/1.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.64/1.89  thf(sk_B_type, type, sk_B: $i).
% 1.64/1.89  thf(t70_enumset1, conjecture,
% 1.64/1.89    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.64/1.89  thf(zf_stmt_0, negated_conjecture,
% 1.64/1.89    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 1.64/1.89    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 1.64/1.89  thf('0', plain,
% 1.64/1.89      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf(t41_enumset1, axiom,
% 1.64/1.89    (![A:$i,B:$i]:
% 1.64/1.89     ( ( k2_tarski @ A @ B ) =
% 1.64/1.89       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 1.64/1.89  thf('1', plain,
% 1.64/1.89      (![X38 : $i, X39 : $i]:
% 1.64/1.89         ((k2_tarski @ X38 @ X39)
% 1.64/1.89           = (k2_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X39)))),
% 1.64/1.89      inference('cnf', [status(esa)], [t41_enumset1])).
% 1.64/1.89  thf(commutativity_k2_xboole_0, axiom,
% 1.64/1.89    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.64/1.89  thf('2', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.64/1.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.64/1.89  thf('3', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 1.64/1.89           = (k2_tarski @ X1 @ X0))),
% 1.64/1.89      inference('sup+', [status(thm)], ['1', '2'])).
% 1.64/1.89  thf('4', plain,
% 1.64/1.89      (![X38 : $i, X39 : $i]:
% 1.64/1.89         ((k2_tarski @ X38 @ X39)
% 1.64/1.89           = (k2_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X39)))),
% 1.64/1.89      inference('cnf', [status(esa)], [t41_enumset1])).
% 1.64/1.89  thf('5', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 1.64/1.89      inference('sup+', [status(thm)], ['3', '4'])).
% 1.64/1.89  thf('6', plain,
% 1.64/1.89      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_B @ sk_A))),
% 1.64/1.89      inference('demod', [status(thm)], ['0', '5'])).
% 1.64/1.89  thf(t69_enumset1, axiom,
% 1.64/1.89    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.64/1.89  thf('7', plain, (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 1.64/1.89      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.64/1.89  thf(t42_enumset1, axiom,
% 1.64/1.89    (![A:$i,B:$i,C:$i]:
% 1.64/1.89     ( ( k1_enumset1 @ A @ B @ C ) =
% 1.64/1.89       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 1.64/1.89  thf('8', plain,
% 1.64/1.89      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.64/1.89         ((k1_enumset1 @ X40 @ X41 @ X42)
% 1.64/1.89           = (k2_xboole_0 @ (k1_tarski @ X40) @ (k2_tarski @ X41 @ X42)))),
% 1.64/1.89      inference('cnf', [status(esa)], [t42_enumset1])).
% 1.64/1.89  thf('9', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         ((k1_enumset1 @ X1 @ X0 @ X0)
% 1.64/1.89           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 1.64/1.89      inference('sup+', [status(thm)], ['7', '8'])).
% 1.64/1.89  thf('10', plain,
% 1.64/1.89      (![X38 : $i, X39 : $i]:
% 1.64/1.89         ((k2_tarski @ X38 @ X39)
% 1.64/1.89           = (k2_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X39)))),
% 1.64/1.89      inference('cnf', [status(esa)], [t41_enumset1])).
% 1.64/1.89  thf('11', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.64/1.89      inference('demod', [status(thm)], ['9', '10'])).
% 1.64/1.89  thf('12', plain,
% 1.64/1.89      (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 1.64/1.89      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.64/1.89  thf('13', plain,
% 1.64/1.89      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.64/1.89      inference('sup+', [status(thm)], ['11', '12'])).
% 1.64/1.89  thf(t46_enumset1, axiom,
% 1.64/1.89    (![A:$i,B:$i,C:$i,D:$i]:
% 1.64/1.89     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 1.64/1.89       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 1.64/1.89  thf('14', plain,
% 1.64/1.89      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.64/1.89         ((k2_enumset1 @ X43 @ X44 @ X45 @ X46)
% 1.64/1.89           = (k2_xboole_0 @ (k1_enumset1 @ X43 @ X44 @ X45) @ (k1_tarski @ X46)))),
% 1.64/1.89      inference('cnf', [status(esa)], [t46_enumset1])).
% 1.64/1.89  thf('15', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 1.64/1.89           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.64/1.89      inference('sup+', [status(thm)], ['13', '14'])).
% 1.64/1.89  thf('16', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 1.64/1.89           = (k2_tarski @ X1 @ X0))),
% 1.64/1.89      inference('sup+', [status(thm)], ['1', '2'])).
% 1.64/1.89  thf('17', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 1.64/1.89      inference('demod', [status(thm)], ['15', '16'])).
% 1.64/1.89  thf('18', plain,
% 1.64/1.89      (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 1.64/1.89      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.64/1.89  thf(l53_enumset1, axiom,
% 1.64/1.89    (![A:$i,B:$i,C:$i,D:$i]:
% 1.64/1.89     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 1.64/1.89       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 1.64/1.89  thf('19', plain,
% 1.64/1.89      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.64/1.89         ((k2_enumset1 @ X34 @ X35 @ X36 @ X37)
% 1.64/1.89           = (k2_xboole_0 @ (k2_tarski @ X34 @ X35) @ (k2_tarski @ X36 @ X37)))),
% 1.64/1.89      inference('cnf', [status(esa)], [l53_enumset1])).
% 1.64/1.89  thf('20', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.89         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 1.64/1.89           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 1.64/1.89      inference('sup+', [status(thm)], ['18', '19'])).
% 1.64/1.89  thf('21', plain,
% 1.64/1.89      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.64/1.89         ((k1_enumset1 @ X40 @ X41 @ X42)
% 1.64/1.89           = (k2_xboole_0 @ (k1_tarski @ X40) @ (k2_tarski @ X41 @ X42)))),
% 1.64/1.89      inference('cnf', [status(esa)], [t42_enumset1])).
% 1.64/1.89  thf('22', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.89         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 1.64/1.89      inference('demod', [status(thm)], ['20', '21'])).
% 1.64/1.89  thf('23', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 1.64/1.89      inference('sup+', [status(thm)], ['17', '22'])).
% 1.64/1.89  thf('24', plain, (((k2_tarski @ sk_B @ sk_A) != (k2_tarski @ sk_B @ sk_A))),
% 1.64/1.89      inference('demod', [status(thm)], ['6', '23'])).
% 1.64/1.89  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 1.64/1.89  
% 1.64/1.89  % SZS output end Refutation
% 1.64/1.89  
% 1.74/1.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
