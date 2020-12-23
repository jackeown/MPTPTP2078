%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JGR9rMSojv

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:19 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
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

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X48: $i,X49: $i] :
      ( r1_tarski @ ( k1_tarski @ X48 ) @ ( k2_tarski @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
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
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JGR9rMSojv
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:11:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.99/1.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.16  % Solved by: fo/fo7.sh
% 0.99/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.16  % done 431 iterations in 0.735s
% 0.99/1.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.16  % SZS output start Refutation
% 0.99/1.16  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.99/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.16  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.99/1.16  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.99/1.16  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.99/1.16  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.99/1.16  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.99/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.16  thf(t14_zfmisc_1, conjecture,
% 0.99/1.16    (![A:$i,B:$i]:
% 0.99/1.16     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.99/1.16       ( k2_tarski @ A @ B ) ))).
% 0.99/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.16    (~( ![A:$i,B:$i]:
% 0.99/1.16        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.99/1.16          ( k2_tarski @ A @ B ) ) )),
% 0.99/1.16    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.99/1.16  thf('0', plain,
% 0.99/1.16      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.99/1.16         != (k2_tarski @ sk_A @ sk_B))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf(t12_zfmisc_1, axiom,
% 0.99/1.16    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.99/1.16  thf('1', plain,
% 0.99/1.16      (![X48 : $i, X49 : $i]:
% 0.99/1.16         (r1_tarski @ (k1_tarski @ X48) @ (k2_tarski @ X48 @ X49))),
% 0.99/1.16      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.99/1.16  thf(l32_xboole_1, axiom,
% 0.99/1.16    (![A:$i,B:$i]:
% 0.99/1.16     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.99/1.16  thf('2', plain,
% 0.99/1.16      (![X8 : $i, X10 : $i]:
% 0.99/1.16         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.99/1.16      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.99/1.16  thf('3', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i]:
% 0.99/1.16         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.99/1.16           = (k1_xboole_0))),
% 0.99/1.16      inference('sup-', [status(thm)], ['1', '2'])).
% 0.99/1.16  thf(t98_xboole_1, axiom,
% 0.99/1.16    (![A:$i,B:$i]:
% 0.99/1.16     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.99/1.16  thf('4', plain,
% 0.99/1.16      (![X18 : $i, X19 : $i]:
% 0.99/1.16         ((k2_xboole_0 @ X18 @ X19)
% 0.99/1.16           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.99/1.16      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.99/1.16  thf('5', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i]:
% 0.99/1.16         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.99/1.16           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))),
% 0.99/1.16      inference('sup+', [status(thm)], ['3', '4'])).
% 0.99/1.16  thf(d10_xboole_0, axiom,
% 0.99/1.16    (![A:$i,B:$i]:
% 0.99/1.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.99/1.16  thf('6', plain,
% 0.99/1.16      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 0.99/1.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.16  thf('7', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.99/1.16      inference('simplify', [status(thm)], ['6'])).
% 0.99/1.16  thf('8', plain,
% 0.99/1.16      (![X8 : $i, X10 : $i]:
% 0.99/1.16         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.99/1.16      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.99/1.16  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.16      inference('sup-', [status(thm)], ['7', '8'])).
% 0.99/1.16  thf('10', plain,
% 0.99/1.16      (![X18 : $i, X19 : $i]:
% 0.99/1.16         ((k2_xboole_0 @ X18 @ X19)
% 0.99/1.16           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.99/1.16      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.99/1.16  thf('11', plain,
% 0.99/1.16      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.99/1.16      inference('sup+', [status(thm)], ['9', '10'])).
% 0.99/1.16  thf(idempotence_k2_xboole_0, axiom,
% 0.99/1.16    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.99/1.16  thf('12', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.99/1.16      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.99/1.16  thf('13', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.99/1.16      inference('demod', [status(thm)], ['11', '12'])).
% 0.99/1.16  thf('14', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i]:
% 0.99/1.16         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.99/1.16           = (k2_tarski @ X1 @ X0))),
% 0.99/1.16      inference('demod', [status(thm)], ['5', '13'])).
% 0.99/1.16  thf(commutativity_k3_xboole_0, axiom,
% 0.99/1.16    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.99/1.16  thf('15', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.16      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.16  thf(t100_xboole_1, axiom,
% 0.99/1.16    (![A:$i,B:$i]:
% 0.99/1.16     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.99/1.16  thf('16', plain,
% 0.99/1.16      (![X11 : $i, X12 : $i]:
% 0.99/1.16         ((k4_xboole_0 @ X11 @ X12)
% 0.99/1.16           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.99/1.16      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.99/1.16  thf('17', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i]:
% 0.99/1.16         ((k4_xboole_0 @ X0 @ X1)
% 0.99/1.16           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.99/1.16      inference('sup+', [status(thm)], ['15', '16'])).
% 0.99/1.16  thf('18', plain,
% 0.99/1.16      (![X11 : $i, X12 : $i]:
% 0.99/1.16         ((k4_xboole_0 @ X11 @ X12)
% 0.99/1.16           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.99/1.16      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.99/1.16  thf(commutativity_k5_xboole_0, axiom,
% 0.99/1.16    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.99/1.16  thf('19', plain,
% 0.99/1.16      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.99/1.16      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.99/1.16  thf(t91_xboole_1, axiom,
% 0.99/1.16    (![A:$i,B:$i,C:$i]:
% 0.99/1.16     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.99/1.16       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.99/1.16  thf('20', plain,
% 0.99/1.16      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.99/1.16         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.99/1.16           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.99/1.16      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.99/1.16  thf('21', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.16         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.99/1.16           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.99/1.16      inference('sup+', [status(thm)], ['19', '20'])).
% 0.99/1.16  thf('22', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.16         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.99/1.16           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X2)))),
% 0.99/1.16      inference('sup+', [status(thm)], ['18', '21'])).
% 0.99/1.16  thf('23', plain,
% 0.99/1.16      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.99/1.16         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.99/1.16           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.99/1.16      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.99/1.16  thf('24', plain,
% 0.99/1.16      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.99/1.16      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.99/1.16  thf('25', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.16         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.99/1.16           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.99/1.16      inference('sup+', [status(thm)], ['23', '24'])).
% 0.99/1.16  thf('26', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.16         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.99/1.16           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.99/1.16      inference('demod', [status(thm)], ['22', '25'])).
% 0.99/1.16  thf('27', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i]:
% 0.99/1.16         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)
% 0.99/1.16           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.99/1.16      inference('sup+', [status(thm)], ['17', '26'])).
% 0.99/1.16  thf('28', plain,
% 0.99/1.16      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.99/1.16      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.99/1.16  thf('29', plain,
% 0.99/1.16      (![X18 : $i, X19 : $i]:
% 0.99/1.16         ((k2_xboole_0 @ X18 @ X19)
% 0.99/1.16           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.99/1.16      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.99/1.16  thf('30', plain,
% 0.99/1.16      (![X18 : $i, X19 : $i]:
% 0.99/1.16         ((k2_xboole_0 @ X18 @ X19)
% 0.99/1.16           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.99/1.16      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.99/1.16  thf('31', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.16      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.99/1.16  thf('32', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i]:
% 0.99/1.16         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.99/1.16           = (k2_tarski @ X1 @ X0))),
% 0.99/1.16      inference('demod', [status(thm)], ['14', '31'])).
% 0.99/1.16  thf('33', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.99/1.16      inference('demod', [status(thm)], ['0', '32'])).
% 0.99/1.16  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.99/1.16  
% 0.99/1.16  % SZS output end Refutation
% 0.99/1.16  
% 0.99/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
