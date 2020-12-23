%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yrjTvRDOnn

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:00 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   40 (  42 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  318 ( 340 expanded)
%              Number of equality atoms :   29 (  31 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( k2_enumset1 @ X39 @ X39 @ X40 @ X41 )
      = ( k1_enumset1 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k3_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 )
      = ( k2_enumset1 @ X42 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 ) @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('7',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k4_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 @ X50 )
      = ( k3_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k3_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 )
      = ( k2_enumset1 @ X42 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','13'])).

thf('15',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( k2_enumset1 @ X39 @ X39 @ X40 @ X41 )
      = ( k1_enumset1 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('17',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( k1_enumset1 @ X64 @ X66 @ X65 )
      = ( k1_enumset1 @ X64 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('18',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','16','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yrjTvRDOnn
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 286 iterations in 0.197s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.69  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.45/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.69  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.69  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(t99_enumset1, conjecture,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.69        ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t99_enumset1])).
% 0.45/0.69  thf('0', plain,
% 0.45/0.69      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.45/0.69         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(t71_enumset1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.69  thf('1', plain,
% 0.45/0.69      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.45/0.69         ((k2_enumset1 @ X39 @ X39 @ X40 @ X41)
% 0.45/0.69           = (k1_enumset1 @ X39 @ X40 @ X41))),
% 0.45/0.69      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.69  thf(t70_enumset1, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.69  thf('2', plain,
% 0.45/0.69      (![X37 : $i, X38 : $i]:
% 0.45/0.69         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.45/0.69      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.69  thf('3', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['1', '2'])).
% 0.45/0.69  thf(t72_enumset1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.69     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.45/0.69  thf('4', plain,
% 0.45/0.69      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.45/0.69         ((k3_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45)
% 0.45/0.69           = (k2_enumset1 @ X42 @ X43 @ X44 @ X45))),
% 0.45/0.69      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.45/0.69  thf(t55_enumset1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.69     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.45/0.69       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.45/0.69  thf('5', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.69         ((k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.45/0.69           = (k2_xboole_0 @ (k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13) @ 
% 0.45/0.69              (k1_tarski @ X14)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.45/0.69  thf('6', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.69         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.45/0.69           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.45/0.69              (k1_tarski @ X4)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.69  thf(t73_enumset1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.69     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.45/0.69       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.45/0.69  thf('7', plain,
% 0.45/0.69      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.45/0.69         ((k4_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 @ X50)
% 0.45/0.69           = (k3_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50))),
% 0.45/0.69      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.45/0.69  thf('8', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.69         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.45/0.69           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.45/0.69              (k1_tarski @ X4)))),
% 0.45/0.69      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.69  thf('9', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.45/0.69           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['3', '8'])).
% 0.45/0.69  thf('10', plain,
% 0.45/0.69      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.45/0.69         ((k3_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45)
% 0.45/0.69           = (k2_enumset1 @ X42 @ X43 @ X44 @ X45))),
% 0.45/0.69      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.45/0.69  thf(t42_enumset1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.45/0.69       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.69         ((k1_enumset1 @ X6 @ X7 @ X8)
% 0.45/0.69           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k2_tarski @ X7 @ X8)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.45/0.69  thf(commutativity_k2_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.45/0.69  thf('12', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.69  thf('13', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 0.45/0.69           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['11', '12'])).
% 0.45/0.69  thf('14', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['9', '10', '13'])).
% 0.45/0.69  thf('15', plain,
% 0.45/0.69      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.45/0.69         ((k2_enumset1 @ X39 @ X39 @ X40 @ X41)
% 0.45/0.69           = (k1_enumset1 @ X39 @ X40 @ X41))),
% 0.45/0.69      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.69  thf('16', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.45/0.69      inference('sup+', [status(thm)], ['14', '15'])).
% 0.45/0.69  thf(t98_enumset1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.45/0.69  thf('17', plain,
% 0.45/0.69      (![X64 : $i, X65 : $i, X66 : $i]:
% 0.45/0.69         ((k1_enumset1 @ X64 @ X66 @ X65) = (k1_enumset1 @ X64 @ X65 @ X66))),
% 0.45/0.69      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.45/0.69  thf('18', plain,
% 0.45/0.69      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.45/0.69         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.45/0.69      inference('demod', [status(thm)], ['0', '16', '17'])).
% 0.45/0.70  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.45/0.70  
% 0.45/0.70  % SZS output end Refutation
% 0.45/0.70  
% 0.45/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
