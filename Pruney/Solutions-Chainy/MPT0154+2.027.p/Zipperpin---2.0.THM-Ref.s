%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.efPrUcvwsP

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  243 ( 275 expanded)
%              Number of equality atoms :   26 (  30 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k2_tarski @ X9 @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k2_enumset1 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X27 @ X28 @ X29 ) @ ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.efPrUcvwsP
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:51:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 50 iterations in 0.044s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(t70_enumset1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t69_enumset1, axiom,
% 0.21/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.51  thf('1', plain, (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.21/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.51  thf(l53_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.51       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         ((k2_enumset1 @ X9 @ X10 @ X11 @ X12)
% 0.21/0.51           = (k2_xboole_0 @ (k2_tarski @ X9 @ X10) @ (k2_tarski @ X11 @ X12)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf(t42_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.51       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k2_tarski @ X21 @ X22)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('6', plain, (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.21/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k2_tarski @ X21 @ X22)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf(t41_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k2_tarski @ A @ B ) =
% 0.21/0.51       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k2_tarski @ X18 @ X19)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X19)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.21/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf(t46_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.51       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.51         ((k2_enumset1 @ X27 @ X28 @ X29 @ X30)
% 0.21/0.51           = (k2_xboole_0 @ (k1_enumset1 @ X27 @ X28 @ X29) @ (k1_tarski @ X30)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k2_tarski @ X18 @ X19)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X19)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k1_enumset1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['5', '16'])).
% 0.21/0.51  thf('18', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '17'])).
% 0.21/0.51  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
