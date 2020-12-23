%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0R6dgnC0nz

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:31 EST 2020

% Result     : Theorem 32.29s
% Output     : Refutation 32.29s
% Verified   : 
% Statistics : Number of formulae       :   54 (  85 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  455 ( 722 expanded)
%              Number of equality atoms :   45 (  76 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X12 @ X10 @ X11 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X12 @ X10 @ X11 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('3',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X12 @ X10 @ X11 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X23 @ X24 @ X25 ) @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k2_enumset1 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','32'])).

thf('34',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','18','33'])).

thf('35',plain,(
    $false ),
    inference(simplify,[status(thm)],['34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0R6dgnC0nz
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 32.29/32.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 32.29/32.50  % Solved by: fo/fo7.sh
% 32.29/32.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 32.29/32.50  % done 10288 iterations in 32.024s
% 32.29/32.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 32.29/32.50  % SZS output start Refutation
% 32.29/32.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 32.29/32.50  thf(sk_A_type, type, sk_A: $i).
% 32.29/32.50  thf(sk_B_type, type, sk_B: $i).
% 32.29/32.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 32.29/32.50  thf(sk_C_type, type, sk_C: $i).
% 32.29/32.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 32.29/32.50  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 32.29/32.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 32.29/32.50  thf(t137_enumset1, conjecture,
% 32.29/32.50    (![A:$i,B:$i,C:$i]:
% 32.29/32.50     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 32.29/32.50       ( k1_enumset1 @ A @ B @ C ) ))).
% 32.29/32.50  thf(zf_stmt_0, negated_conjecture,
% 32.29/32.50    (~( ![A:$i,B:$i,C:$i]:
% 32.29/32.50        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 32.29/32.50          ( k1_enumset1 @ A @ B @ C ) ) )),
% 32.29/32.50    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 32.29/32.50  thf('0', plain,
% 32.29/32.50      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 32.29/32.50         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 32.29/32.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.29/32.50  thf(t100_enumset1, axiom,
% 32.29/32.50    (![A:$i,B:$i,C:$i]:
% 32.29/32.50     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 32.29/32.50  thf('1', plain,
% 32.29/32.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 32.29/32.50         ((k1_enumset1 @ X12 @ X10 @ X11) = (k1_enumset1 @ X10 @ X11 @ X12))),
% 32.29/32.50      inference('cnf', [status(esa)], [t100_enumset1])).
% 32.29/32.50  thf('2', plain,
% 32.29/32.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 32.29/32.50         ((k1_enumset1 @ X12 @ X10 @ X11) = (k1_enumset1 @ X10 @ X11 @ X12))),
% 32.29/32.50      inference('cnf', [status(esa)], [t100_enumset1])).
% 32.29/32.50  thf('3', plain,
% 32.29/32.50      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 32.29/32.50         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 32.29/32.50      inference('demod', [status(thm)], ['0', '1', '2'])).
% 32.29/32.50  thf(t42_enumset1, axiom,
% 32.29/32.50    (![A:$i,B:$i,C:$i]:
% 32.29/32.50     ( ( k1_enumset1 @ A @ B @ C ) =
% 32.29/32.50       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 32.29/32.50  thf('4', plain,
% 32.29/32.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 32.29/32.50         ((k1_enumset1 @ X16 @ X17 @ X18)
% 32.29/32.50           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k2_tarski @ X17 @ X18)))),
% 32.29/32.50      inference('cnf', [status(esa)], [t42_enumset1])).
% 32.29/32.50  thf(t69_enumset1, axiom,
% 32.29/32.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 32.29/32.50  thf('5', plain, (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 32.29/32.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 32.29/32.50  thf('6', plain,
% 32.29/32.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 32.29/32.50         ((k1_enumset1 @ X16 @ X17 @ X18)
% 32.29/32.50           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k2_tarski @ X17 @ X18)))),
% 32.29/32.50      inference('cnf', [status(esa)], [t42_enumset1])).
% 32.29/32.50  thf('7', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i]:
% 32.29/32.50         ((k1_enumset1 @ X1 @ X0 @ X0)
% 32.29/32.50           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 32.29/32.50      inference('sup+', [status(thm)], ['5', '6'])).
% 32.29/32.50  thf('8', plain,
% 32.29/32.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 32.29/32.50         ((k1_enumset1 @ X12 @ X10 @ X11) = (k1_enumset1 @ X10 @ X11 @ X12))),
% 32.29/32.50      inference('cnf', [status(esa)], [t100_enumset1])).
% 32.29/32.50  thf(t70_enumset1, axiom,
% 32.29/32.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 32.29/32.50  thf('9', plain,
% 32.29/32.50      (![X28 : $i, X29 : $i]:
% 32.29/32.50         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 32.29/32.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 32.29/32.50  thf('10', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i]:
% 32.29/32.50         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 32.29/32.50      inference('sup+', [status(thm)], ['8', '9'])).
% 32.29/32.50  thf('11', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i]:
% 32.29/32.50         ((k2_tarski @ X0 @ X1)
% 32.29/32.50           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 32.29/32.50      inference('demod', [status(thm)], ['7', '10'])).
% 32.29/32.50  thf(t4_xboole_1, axiom,
% 32.29/32.50    (![A:$i,B:$i,C:$i]:
% 32.29/32.50     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 32.29/32.50       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 32.29/32.50  thf('12', plain,
% 32.29/32.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 32.29/32.50         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 32.29/32.50           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 32.29/32.50      inference('cnf', [status(esa)], [t4_xboole_1])).
% 32.29/32.50  thf('13', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.29/32.50         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 32.29/32.50           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 32.29/32.50              (k2_xboole_0 @ (k1_tarski @ X1) @ X2)))),
% 32.29/32.50      inference('sup+', [status(thm)], ['11', '12'])).
% 32.29/32.50  thf('14', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 32.29/32.50         ((k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X1 @ X0))
% 32.29/32.50           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 32.29/32.50      inference('sup+', [status(thm)], ['4', '13'])).
% 32.29/32.50  thf(t46_enumset1, axiom,
% 32.29/32.50    (![A:$i,B:$i,C:$i,D:$i]:
% 32.29/32.50     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 32.29/32.50       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 32.29/32.50  thf('15', plain,
% 32.29/32.50      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 32.29/32.50         ((k2_enumset1 @ X23 @ X24 @ X25 @ X26)
% 32.29/32.50           = (k2_xboole_0 @ (k1_enumset1 @ X23 @ X24 @ X25) @ (k1_tarski @ X26)))),
% 32.29/32.50      inference('cnf', [status(esa)], [t46_enumset1])).
% 32.29/32.50  thf(commutativity_k2_xboole_0, axiom,
% 32.29/32.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 32.29/32.50  thf('16', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.29/32.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.29/32.50  thf('17', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 32.29/32.50         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1))
% 32.29/32.50           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 32.29/32.50      inference('sup+', [status(thm)], ['15', '16'])).
% 32.29/32.50  thf('18', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 32.29/32.50         ((k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X1 @ X0))
% 32.29/32.50           = (k2_enumset1 @ X2 @ X1 @ X0 @ X3))),
% 32.29/32.50      inference('demod', [status(thm)], ['14', '17'])).
% 32.29/32.50  thf('19', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i]:
% 32.29/32.50         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 32.29/32.50      inference('sup+', [status(thm)], ['8', '9'])).
% 32.29/32.50  thf(t44_enumset1, axiom,
% 32.29/32.50    (![A:$i,B:$i,C:$i,D:$i]:
% 32.29/32.50     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 32.29/32.50       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 32.29/32.50  thf('20', plain,
% 32.29/32.50      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 32.29/32.50         ((k2_enumset1 @ X19 @ X20 @ X21 @ X22)
% 32.29/32.50           = (k2_xboole_0 @ (k1_tarski @ X19) @ (k1_enumset1 @ X20 @ X21 @ X22)))),
% 32.29/32.50      inference('cnf', [status(esa)], [t44_enumset1])).
% 32.29/32.50  thf('21', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.29/32.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.29/32.50  thf('22', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 32.29/32.50         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 32.29/32.50           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 32.29/32.50      inference('sup+', [status(thm)], ['20', '21'])).
% 32.29/32.50  thf('23', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.29/32.50         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 32.29/32.50           = (k2_enumset1 @ X2 @ X0 @ X1 @ X1))),
% 32.29/32.50      inference('sup+', [status(thm)], ['19', '22'])).
% 32.29/32.50  thf('24', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i]:
% 32.29/32.50         ((k2_tarski @ X0 @ X1)
% 32.29/32.50           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 32.29/32.50      inference('demod', [status(thm)], ['7', '10'])).
% 32.29/32.50  thf('25', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.29/32.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.29/32.50  thf('26', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i]:
% 32.29/32.50         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 32.29/32.50           = (k2_tarski @ X1 @ X0))),
% 32.29/32.50      inference('sup+', [status(thm)], ['24', '25'])).
% 32.29/32.50  thf('27', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i]:
% 32.29/32.50         ((k2_tarski @ X0 @ X1)
% 32.29/32.50           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 32.29/32.50      inference('demod', [status(thm)], ['7', '10'])).
% 32.29/32.50  thf('28', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 32.29/32.50      inference('sup+', [status(thm)], ['26', '27'])).
% 32.29/32.50  thf('29', plain,
% 32.29/32.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 32.29/32.50         ((k1_enumset1 @ X16 @ X17 @ X18)
% 32.29/32.50           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k2_tarski @ X17 @ X18)))),
% 32.29/32.50      inference('cnf', [status(esa)], [t42_enumset1])).
% 32.29/32.50  thf('30', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.29/32.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.29/32.50  thf('31', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.29/32.50         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 32.29/32.50           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 32.29/32.50      inference('sup+', [status(thm)], ['29', '30'])).
% 32.29/32.50  thf('32', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.29/32.50         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 32.29/32.50           = (k1_enumset1 @ X2 @ X0 @ X1))),
% 32.29/32.50      inference('sup+', [status(thm)], ['28', '31'])).
% 32.29/32.50  thf('33', plain,
% 32.29/32.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.29/32.50         ((k1_enumset1 @ X2 @ X0 @ X1) = (k2_enumset1 @ X2 @ X0 @ X1 @ X1))),
% 32.29/32.50      inference('demod', [status(thm)], ['23', '32'])).
% 32.29/32.50  thf('34', plain,
% 32.29/32.50      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 32.29/32.50         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 32.29/32.50      inference('demod', [status(thm)], ['3', '18', '33'])).
% 32.29/32.50  thf('35', plain, ($false), inference('simplify', [status(thm)], ['34'])).
% 32.29/32.50  
% 32.29/32.50  % SZS output end Refutation
% 32.29/32.50  
% 32.29/32.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
