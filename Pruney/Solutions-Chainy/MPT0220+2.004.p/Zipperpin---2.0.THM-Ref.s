%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WxqtiTvhWL

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:18 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   56 (  64 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  381 ( 450 expanded)
%              Number of equality atoms :   42 (  50 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t14_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t14_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X49: $i,X50: $i] :
      ( r1_tarski @ ( k1_tarski @ X49 ) @ ( k2_tarski @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X18: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X20 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ( X15 != X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X16: $i] :
      ( r1_tarski @ X16 @ X16 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X18: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X20 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ X14 )
      = X14 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('30',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','31'])).

thf('33',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WxqtiTvhWL
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:23:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.62/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.80  % Solved by: fo/fo7.sh
% 0.62/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.80  % done 446 iterations in 0.357s
% 0.62/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.80  % SZS output start Refutation
% 0.62/0.80  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.62/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.62/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.62/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.62/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.62/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.80  thf(t14_zfmisc_1, conjecture,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.62/0.80       ( k2_tarski @ A @ B ) ))).
% 0.62/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.80    (~( ![A:$i,B:$i]:
% 0.62/0.80        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.62/0.80          ( k2_tarski @ A @ B ) ) )),
% 0.62/0.80    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.62/0.80  thf('0', plain,
% 0.62/0.80      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.62/0.80         != (k2_tarski @ sk_A @ sk_B))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf(t12_zfmisc_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.62/0.80  thf('1', plain,
% 0.62/0.80      (![X49 : $i, X50 : $i]:
% 0.62/0.80         (r1_tarski @ (k1_tarski @ X49) @ (k2_tarski @ X49 @ X50))),
% 0.62/0.80      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.62/0.80  thf(l32_xboole_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.62/0.80  thf('2', plain,
% 0.62/0.80      (![X18 : $i, X20 : $i]:
% 0.62/0.80         (((k4_xboole_0 @ X18 @ X20) = (k1_xboole_0))
% 0.62/0.80          | ~ (r1_tarski @ X18 @ X20))),
% 0.62/0.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.62/0.80  thf('3', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.62/0.80           = (k1_xboole_0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['1', '2'])).
% 0.62/0.80  thf(t98_xboole_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.62/0.80  thf('4', plain,
% 0.62/0.80      (![X26 : $i, X27 : $i]:
% 0.62/0.80         ((k2_xboole_0 @ X26 @ X27)
% 0.62/0.80           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.62/0.80  thf('5', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.62/0.80           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['3', '4'])).
% 0.62/0.80  thf(d10_xboole_0, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.62/0.80  thf('6', plain,
% 0.62/0.80      (![X15 : $i, X16 : $i]: ((r1_tarski @ X15 @ X16) | ((X15) != (X16)))),
% 0.62/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.62/0.80  thf('7', plain, (![X16 : $i]: (r1_tarski @ X16 @ X16)),
% 0.62/0.80      inference('simplify', [status(thm)], ['6'])).
% 0.62/0.80  thf('8', plain,
% 0.62/0.80      (![X18 : $i, X20 : $i]:
% 0.62/0.80         (((k4_xboole_0 @ X18 @ X20) = (k1_xboole_0))
% 0.62/0.80          | ~ (r1_tarski @ X18 @ X20))),
% 0.62/0.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.62/0.80  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.62/0.80  thf('10', plain,
% 0.62/0.80      (![X26 : $i, X27 : $i]:
% 0.62/0.80         ((k2_xboole_0 @ X26 @ X27)
% 0.62/0.80           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.62/0.80  thf('11', plain,
% 0.62/0.80      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['9', '10'])).
% 0.62/0.80  thf(idempotence_k2_xboole_0, axiom,
% 0.62/0.80    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.62/0.80  thf('12', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ X14) = (X14))),
% 0.62/0.80      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.62/0.80  thf('13', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.62/0.80      inference('demod', [status(thm)], ['11', '12'])).
% 0.62/0.80  thf('14', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.62/0.80           = (k2_tarski @ X1 @ X0))),
% 0.62/0.80      inference('demod', [status(thm)], ['5', '13'])).
% 0.62/0.80  thf(commutativity_k3_xboole_0, axiom,
% 0.62/0.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.62/0.80  thf('15', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.62/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.62/0.80  thf(t100_xboole_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.62/0.80  thf('16', plain,
% 0.62/0.80      (![X21 : $i, X22 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X21 @ X22)
% 0.62/0.80           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.80  thf('17', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X0 @ X1)
% 0.62/0.80           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['15', '16'])).
% 0.62/0.80  thf('18', plain,
% 0.62/0.80      (![X21 : $i, X22 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X21 @ X22)
% 0.62/0.80           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.80  thf(commutativity_k5_xboole_0, axiom,
% 0.62/0.80    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.62/0.80  thf('19', plain,
% 0.62/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.62/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.80  thf(t91_xboole_1, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.62/0.80       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.62/0.80  thf('20', plain,
% 0.62/0.80      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.62/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.62/0.80           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.62/0.80  thf('21', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.62/0.80           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['19', '20'])).
% 0.62/0.80  thf('22', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.80         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.62/0.80           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X2)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['18', '21'])).
% 0.62/0.80  thf('23', plain,
% 0.62/0.80      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.62/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.62/0.80           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.62/0.80  thf('24', plain,
% 0.62/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.62/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.80  thf('25', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.80         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.62/0.80           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['23', '24'])).
% 0.62/0.80  thf('26', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.80         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.62/0.80           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.62/0.80      inference('demod', [status(thm)], ['22', '25'])).
% 0.62/0.80  thf('27', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)
% 0.62/0.80           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['17', '26'])).
% 0.62/0.80  thf('28', plain,
% 0.62/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.62/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.80  thf('29', plain,
% 0.62/0.80      (![X26 : $i, X27 : $i]:
% 0.62/0.80         ((k2_xboole_0 @ X26 @ X27)
% 0.62/0.80           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.62/0.80  thf('30', plain,
% 0.62/0.80      (![X26 : $i, X27 : $i]:
% 0.62/0.80         ((k2_xboole_0 @ X26 @ X27)
% 0.62/0.80           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.62/0.80  thf('31', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.80      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.62/0.80  thf('32', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.62/0.80           = (k2_tarski @ X1 @ X0))),
% 0.62/0.80      inference('demod', [status(thm)], ['14', '31'])).
% 0.62/0.80  thf('33', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.62/0.80      inference('demod', [status(thm)], ['0', '32'])).
% 0.62/0.80  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.62/0.80  
% 0.62/0.80  % SZS output end Refutation
% 0.62/0.80  
% 0.62/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
