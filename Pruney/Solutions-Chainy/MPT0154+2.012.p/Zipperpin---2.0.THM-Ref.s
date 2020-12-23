%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fUh0pH1Ain

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:23 EST 2020

% Result     : Theorem 0.63s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  243 ( 275 expanded)
%              Number of equality atoms :   26 (  30 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X48: $i] :
      ( ( k2_tarski @ X48 @ X48 )
      = ( k1_tarski @ X48 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k2_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_tarski @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X48: $i] :
      ( ( k2_tarski @ X48 @ X48 )
      = ( k1_tarski @ X48 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('8',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X39 @ X40 @ X41 ) @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_tarski @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X48: $i] :
      ( ( k2_tarski @ X48 @ X48 )
      = ( k1_tarski @ X48 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('13',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_xboole_0 @ ( k2_tarski @ X26 @ X27 ) @ ( k2_tarski @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k2_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fUh0pH1Ain
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 11:13:27 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.32  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.63/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.63/0.86  % Solved by: fo/fo7.sh
% 0.63/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.63/0.86  % done 1161 iterations in 0.462s
% 0.63/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.63/0.86  % SZS output start Refutation
% 0.63/0.86  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.63/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.63/0.86  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.63/0.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.63/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.63/0.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.63/0.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.63/0.86  thf(t70_enumset1, conjecture,
% 0.63/0.86    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.63/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.63/0.86    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.63/0.86    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.63/0.86  thf('0', plain,
% 0.63/0.86      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.63/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.86  thf(t69_enumset1, axiom,
% 0.63/0.86    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.63/0.86  thf('1', plain, (![X48 : $i]: ((k2_tarski @ X48 @ X48) = (k1_tarski @ X48))),
% 0.63/0.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.63/0.86  thf(t42_enumset1, axiom,
% 0.63/0.86    (![A:$i,B:$i,C:$i]:
% 0.63/0.86     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.63/0.86       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.63/0.86  thf('2', plain,
% 0.63/0.86      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.63/0.86         ((k1_enumset1 @ X32 @ X33 @ X34)
% 0.63/0.86           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k2_tarski @ X33 @ X34)))),
% 0.63/0.86      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.63/0.86  thf('3', plain,
% 0.63/0.86      (![X0 : $i, X1 : $i]:
% 0.63/0.86         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.63/0.86           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.63/0.86      inference('sup+', [status(thm)], ['1', '2'])).
% 0.63/0.86  thf(t41_enumset1, axiom,
% 0.63/0.86    (![A:$i,B:$i]:
% 0.63/0.86     ( ( k2_tarski @ A @ B ) =
% 0.63/0.86       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.63/0.86  thf('4', plain,
% 0.63/0.86      (![X30 : $i, X31 : $i]:
% 0.63/0.86         ((k2_tarski @ X30 @ X31)
% 0.63/0.86           = (k2_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X31)))),
% 0.63/0.86      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.63/0.86  thf('5', plain,
% 0.63/0.86      (![X0 : $i, X1 : $i]:
% 0.63/0.86         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.63/0.86      inference('demod', [status(thm)], ['3', '4'])).
% 0.63/0.86  thf('6', plain, (![X48 : $i]: ((k2_tarski @ X48 @ X48) = (k1_tarski @ X48))),
% 0.63/0.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.63/0.86  thf('7', plain,
% 0.63/0.86      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.63/0.86      inference('sup+', [status(thm)], ['5', '6'])).
% 0.63/0.86  thf(t46_enumset1, axiom,
% 0.63/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.63/0.86     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.63/0.86       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.63/0.86  thf('8', plain,
% 0.63/0.86      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.63/0.86         ((k2_enumset1 @ X39 @ X40 @ X41 @ X42)
% 0.63/0.86           = (k2_xboole_0 @ (k1_enumset1 @ X39 @ X40 @ X41) @ (k1_tarski @ X42)))),
% 0.63/0.86      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.63/0.86  thf('9', plain,
% 0.63/0.86      (![X0 : $i, X1 : $i]:
% 0.63/0.86         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.63/0.86           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.63/0.86      inference('sup+', [status(thm)], ['7', '8'])).
% 0.63/0.86  thf('10', plain,
% 0.63/0.86      (![X30 : $i, X31 : $i]:
% 0.63/0.86         ((k2_tarski @ X30 @ X31)
% 0.63/0.86           = (k2_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X31)))),
% 0.63/0.86      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.63/0.86  thf('11', plain,
% 0.63/0.86      (![X0 : $i, X1 : $i]:
% 0.63/0.86         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.63/0.86      inference('demod', [status(thm)], ['9', '10'])).
% 0.63/0.86  thf('12', plain,
% 0.63/0.86      (![X48 : $i]: ((k2_tarski @ X48 @ X48) = (k1_tarski @ X48))),
% 0.63/0.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.63/0.86  thf(l53_enumset1, axiom,
% 0.63/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.63/0.86     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.63/0.86       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.63/0.86  thf('13', plain,
% 0.63/0.86      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.63/0.86         ((k2_enumset1 @ X26 @ X27 @ X28 @ X29)
% 0.63/0.86           = (k2_xboole_0 @ (k2_tarski @ X26 @ X27) @ (k2_tarski @ X28 @ X29)))),
% 0.63/0.86      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.63/0.86  thf('14', plain,
% 0.63/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.86         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.63/0.86           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.63/0.86      inference('sup+', [status(thm)], ['12', '13'])).
% 0.63/0.86  thf('15', plain,
% 0.63/0.86      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.63/0.86         ((k1_enumset1 @ X32 @ X33 @ X34)
% 0.63/0.86           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k2_tarski @ X33 @ X34)))),
% 0.63/0.86      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.63/0.86  thf('16', plain,
% 0.63/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.86         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.63/0.86      inference('demod', [status(thm)], ['14', '15'])).
% 0.63/0.86  thf('17', plain,
% 0.63/0.86      (![X0 : $i, X1 : $i]:
% 0.63/0.86         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.63/0.86      inference('sup+', [status(thm)], ['11', '16'])).
% 0.63/0.86  thf('18', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.63/0.86      inference('demod', [status(thm)], ['0', '17'])).
% 0.63/0.86  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.63/0.86  
% 0.63/0.86  % SZS output end Refutation
% 0.63/0.86  
% 0.63/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
