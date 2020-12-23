%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KFBN3m1t6V

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:30 EST 2020

% Result     : Theorem 3.02s
% Output     : Refutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  242 ( 260 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t137_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t137_enumset1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X56 @ X54 @ X55 )
      = ( k1_enumset1 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('2',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X56 @ X54 @ X55 )
      = ( k1_enumset1 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('3',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_xboole_0 @ ( k2_tarski @ X45 @ X46 ) @ ( k2_tarski @ X47 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('5',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X56 @ X54 @ X55 )
      = ( k1_enumset1 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X118: $i,X119: $i] :
      ( ( k1_enumset1 @ X118 @ X118 @ X119 )
      = ( k2_tarski @ X118 @ X119 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('9',plain,(
    ! [X72: $i,X73: $i,X74: $i,X75: $i] :
      ( ( k2_enumset1 @ X72 @ X73 @ X74 @ X75 )
      = ( k2_xboole_0 @ ( k1_tarski @ X72 ) @ ( k1_enumset1 @ X73 @ X74 @ X75 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( k1_enumset1 @ X66 @ X67 @ X68 )
      = ( k2_xboole_0 @ ( k1_tarski @ X66 ) @ ( k2_tarski @ X67 @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('13',plain,(
    ! [X128: $i,X129: $i,X130: $i] :
      ( ( k1_enumset1 @ X128 @ X130 @ X129 )
      = ( k1_enumset1 @ X128 @ X129 @ X130 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('14',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['5','12','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KFBN3m1t6V
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:23:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.02/3.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.02/3.20  % Solved by: fo/fo7.sh
% 3.02/3.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.02/3.20  % done 2671 iterations in 2.750s
% 3.02/3.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.02/3.20  % SZS output start Refutation
% 3.02/3.20  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.02/3.20  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.02/3.20  thf(sk_A_type, type, sk_A: $i).
% 3.02/3.20  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.02/3.20  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.02/3.20  thf(sk_B_type, type, sk_B: $i).
% 3.02/3.20  thf(sk_C_type, type, sk_C: $i).
% 3.02/3.20  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.02/3.20  thf(t137_enumset1, conjecture,
% 3.02/3.20    (![A:$i,B:$i,C:$i]:
% 3.02/3.20     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 3.02/3.20       ( k1_enumset1 @ A @ B @ C ) ))).
% 3.02/3.20  thf(zf_stmt_0, negated_conjecture,
% 3.02/3.20    (~( ![A:$i,B:$i,C:$i]:
% 3.02/3.20        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 3.02/3.20          ( k1_enumset1 @ A @ B @ C ) ) )),
% 3.02/3.20    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 3.02/3.20  thf('0', plain,
% 3.02/3.20      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 3.02/3.20         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 3.02/3.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.20  thf(t100_enumset1, axiom,
% 3.02/3.20    (![A:$i,B:$i,C:$i]:
% 3.02/3.20     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 3.02/3.20  thf('1', plain,
% 3.02/3.20      (![X54 : $i, X55 : $i, X56 : $i]:
% 3.02/3.20         ((k1_enumset1 @ X56 @ X54 @ X55) = (k1_enumset1 @ X54 @ X55 @ X56))),
% 3.02/3.20      inference('cnf', [status(esa)], [t100_enumset1])).
% 3.02/3.20  thf('2', plain,
% 3.02/3.20      (![X54 : $i, X55 : $i, X56 : $i]:
% 3.02/3.20         ((k1_enumset1 @ X56 @ X54 @ X55) = (k1_enumset1 @ X54 @ X55 @ X56))),
% 3.02/3.20      inference('cnf', [status(esa)], [t100_enumset1])).
% 3.02/3.20  thf('3', plain,
% 3.02/3.20      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 3.02/3.20         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 3.02/3.20      inference('demod', [status(thm)], ['0', '1', '2'])).
% 3.02/3.20  thf(l53_enumset1, axiom,
% 3.02/3.20    (![A:$i,B:$i,C:$i,D:$i]:
% 3.02/3.20     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.02/3.20       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 3.02/3.20  thf('4', plain,
% 3.02/3.20      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 3.02/3.20         ((k2_enumset1 @ X45 @ X46 @ X47 @ X48)
% 3.02/3.20           = (k2_xboole_0 @ (k2_tarski @ X45 @ X46) @ (k2_tarski @ X47 @ X48)))),
% 3.02/3.20      inference('cnf', [status(esa)], [l53_enumset1])).
% 3.02/3.20  thf('5', plain,
% 3.02/3.20      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 3.02/3.20         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 3.02/3.20      inference('demod', [status(thm)], ['3', '4'])).
% 3.02/3.20  thf('6', plain,
% 3.02/3.20      (![X54 : $i, X55 : $i, X56 : $i]:
% 3.02/3.20         ((k1_enumset1 @ X56 @ X54 @ X55) = (k1_enumset1 @ X54 @ X55 @ X56))),
% 3.02/3.20      inference('cnf', [status(esa)], [t100_enumset1])).
% 3.02/3.20  thf(t70_enumset1, axiom,
% 3.02/3.20    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.02/3.20  thf('7', plain,
% 3.02/3.20      (![X118 : $i, X119 : $i]:
% 3.02/3.20         ((k1_enumset1 @ X118 @ X118 @ X119) = (k2_tarski @ X118 @ X119))),
% 3.02/3.20      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.02/3.20  thf('8', plain,
% 3.02/3.20      (![X0 : $i, X1 : $i]:
% 3.02/3.20         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 3.02/3.20      inference('sup+', [status(thm)], ['6', '7'])).
% 3.02/3.20  thf(t44_enumset1, axiom,
% 3.02/3.20    (![A:$i,B:$i,C:$i,D:$i]:
% 3.02/3.20     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.02/3.20       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 3.02/3.20  thf('9', plain,
% 3.02/3.20      (![X72 : $i, X73 : $i, X74 : $i, X75 : $i]:
% 3.02/3.20         ((k2_enumset1 @ X72 @ X73 @ X74 @ X75)
% 3.02/3.20           = (k2_xboole_0 @ (k1_tarski @ X72) @ (k1_enumset1 @ X73 @ X74 @ X75)))),
% 3.02/3.20      inference('cnf', [status(esa)], [t44_enumset1])).
% 3.02/3.20  thf('10', plain,
% 3.02/3.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.20         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1)
% 3.02/3.20           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 3.02/3.20      inference('sup+', [status(thm)], ['8', '9'])).
% 3.02/3.20  thf(t42_enumset1, axiom,
% 3.02/3.20    (![A:$i,B:$i,C:$i]:
% 3.02/3.20     ( ( k1_enumset1 @ A @ B @ C ) =
% 3.02/3.20       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 3.02/3.20  thf('11', plain,
% 3.02/3.20      (![X66 : $i, X67 : $i, X68 : $i]:
% 3.02/3.20         ((k1_enumset1 @ X66 @ X67 @ X68)
% 3.02/3.20           = (k2_xboole_0 @ (k1_tarski @ X66) @ (k2_tarski @ X67 @ X68)))),
% 3.02/3.20      inference('cnf', [status(esa)], [t42_enumset1])).
% 3.02/3.20  thf('12', plain,
% 3.02/3.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.20         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.02/3.20      inference('demod', [status(thm)], ['10', '11'])).
% 3.02/3.20  thf(t98_enumset1, axiom,
% 3.02/3.20    (![A:$i,B:$i,C:$i]:
% 3.02/3.20     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 3.02/3.20  thf('13', plain,
% 3.02/3.20      (![X128 : $i, X129 : $i, X130 : $i]:
% 3.02/3.20         ((k1_enumset1 @ X128 @ X130 @ X129)
% 3.02/3.20           = (k1_enumset1 @ X128 @ X129 @ X130))),
% 3.02/3.20      inference('cnf', [status(esa)], [t98_enumset1])).
% 3.02/3.20  thf('14', plain,
% 3.02/3.20      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 3.02/3.20         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 3.02/3.20      inference('demod', [status(thm)], ['5', '12', '13'])).
% 3.02/3.20  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 3.02/3.20  
% 3.02/3.20  % SZS output end Refutation
% 3.02/3.20  
% 3.02/3.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
