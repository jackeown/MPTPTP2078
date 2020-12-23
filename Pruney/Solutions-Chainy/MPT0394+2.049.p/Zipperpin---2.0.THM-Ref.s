%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WOAC6fpTLS

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  65 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  348 ( 460 expanded)
%              Number of equality atoms :   49 (  66 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X14 @ X14 @ X15 @ X16 )
      = ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X12 @ X12 @ X13 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X12 @ X12 @ X13 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('8',plain,(
    ! [X28: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X26 @ X27 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X26 ) @ ( k1_setfam_1 @ X27 ) ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_enumset1 @ X0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22 != X21 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X21 ) )
       != ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('14',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X21 ) )
     != ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X24 ) @ ( k2_tarski @ X24 @ X25 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t22_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X21: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X21 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_enumset1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','20'])).

thf('22',plain,(
    ! [X28: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X21: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X21 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','25'])).

thf('27',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WOAC6fpTLS
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:40:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 183 iterations in 0.061s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(t12_setfam_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]:
% 0.21/0.52        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.52         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t71_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         ((k2_enumset1 @ X14 @ X14 @ X15 @ X16)
% 0.21/0.52           = (k1_enumset1 @ X14 @ X15 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.52  thf(t70_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         ((k1_enumset1 @ X12 @ X12 @ X13) = (k2_tarski @ X12 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf(t46_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.52       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.21/0.52           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ (k1_tarski @ X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         ((k1_enumset1 @ X12 @ X12 @ X13) = (k2_tarski @ X12 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.52  thf(t69_enumset1, axiom,
% 0.21/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.52  thf('6', plain, (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf(t11_setfam_1, axiom,
% 0.21/0.52    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.21/0.52  thf('8', plain, (![X28 : $i]: ((k1_setfam_1 @ (k1_tarski @ X28)) = (X28))),
% 0.21/0.52      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i]: ((k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ X0)) = (X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf(t10_setfam_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.21/0.52            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X26 : $i, X27 : $i]:
% 0.21/0.52         (((X26) = (k1_xboole_0))
% 0.21/0.52          | ((k1_setfam_1 @ (k2_xboole_0 @ X26 @ X27))
% 0.21/0.52              = (k3_xboole_0 @ (k1_setfam_1 @ X26) @ (k1_setfam_1 @ X27)))
% 0.21/0.52          | ((X27) = (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_enumset1 @ X0 @ X0 @ X0) @ X1))
% 0.21/0.52            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.21/0.52          | ((X1) = (k1_xboole_0))
% 0.21/0.52          | ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf(t20_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.52         ( k1_tarski @ A ) ) <=>
% 0.21/0.52       ( ( A ) != ( B ) ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X21 : $i, X22 : $i]:
% 0.21/0.52         (((X22) != (X21))
% 0.21/0.52          | ((k4_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X21))
% 0.21/0.52              != (k1_tarski @ X22)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X21 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X21))
% 0.21/0.52           != (k1_tarski @ X21))),
% 0.21/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.52  thf(t22_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.52       ( k1_xboole_0 ) ))).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ (k1_tarski @ X24) @ (k2_tarski @ X24 @ X25))
% 0.21/0.52           = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t22_zfmisc_1])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf('18', plain, (![X21 : $i]: ((k1_xboole_0) != (k1_tarski @ X21))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i]: ((k1_xboole_0) != (k1_enumset1 @ X0 @ X0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((X1) = (k1_xboole_0))
% 0.21/0.52          | ((k1_setfam_1 @ (k2_xboole_0 @ (k1_enumset1 @ X0 @ X0 @ X0) @ X1))
% 0.21/0.52              = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1))))),
% 0.21/0.52      inference('clc', [status(thm)], ['11', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k1_setfam_1 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 0.21/0.52            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.21/0.52          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['4', '20'])).
% 0.21/0.52  thf('22', plain, (![X28 : $i]: ((k1_setfam_1 @ (k1_tarski @ X28)) = (X28))),
% 0.21/0.52      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k1_setfam_1 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 0.21/0.52            = (k3_xboole_0 @ X1 @ X0))
% 0.21/0.52          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain, (![X21 : $i]: ((k1_xboole_0) != (k1_tarski @ X21))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '17'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 0.21/0.52           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.52      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['3', '25'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '26'])).
% 0.21/0.52  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
