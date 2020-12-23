%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uh5zv9PUfN

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  44 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  251 ( 341 expanded)
%              Number of equality atoms :   26 (  36 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k2_tarski @ X23 @ X24 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k2_tarski @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k2_tarski @ X16 @ X17 ) @ ( k2_tarski @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k2_tarski @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('18',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uh5zv9PUfN
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:22:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 114 iterations in 0.073s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(t70_enumset1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t69_enumset1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.53  thf('1', plain, (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf(t42_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X22 @ X23 @ X24)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X22) @ (k2_tarski @ X23 @ X24)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf(t41_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k2_tarski @ A @ B ) =
% 0.20/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         ((k2_tarski @ X20 @ X21)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X21)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X22 @ X23 @ X24)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X22) @ (k2_tarski @ X23 @ X24)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X1 @ X0 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf(t44_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.53         ((k2_enumset1 @ X25 @ X26 @ X27 @ X28)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X25) @ (k1_enumset1 @ X26 @ X27 @ X28)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X0 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf(l53_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.53       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.53         ((k2_enumset1 @ X16 @ X17 @ X18 @ X19)
% 0.20/0.53           = (k2_xboole_0 @ (k2_tarski @ X16 @ X17) @ (k2_tarski @ X18 @ X19)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X22 @ X23 @ X24)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X22) @ (k2_tarski @ X23 @ X24)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k2_enumset1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['9', '16'])).
% 0.20/0.53  thf('18', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['0', '17'])).
% 0.20/0.53  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
