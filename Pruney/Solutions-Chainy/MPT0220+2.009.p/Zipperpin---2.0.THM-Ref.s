%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EFsptsR2d7

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:19 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
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

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X49: $i,X50: $i] :
      ( r1_tarski @ ( k1_tarski @ X49 ) @ ( k2_tarski @ X49 @ X50 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
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
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EFsptsR2d7
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:10:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.00/2.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.00/2.25  % Solved by: fo/fo7.sh
% 2.00/2.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.00/2.25  % done 558 iterations in 1.794s
% 2.00/2.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.00/2.25  % SZS output start Refutation
% 2.00/2.25  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.00/2.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.00/2.25  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.00/2.25  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.00/2.25  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.00/2.25  thf(sk_B_type, type, sk_B: $i).
% 2.00/2.25  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.00/2.25  thf(sk_A_type, type, sk_A: $i).
% 2.00/2.25  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.00/2.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.00/2.25  thf(t14_zfmisc_1, conjecture,
% 2.00/2.25    (![A:$i,B:$i]:
% 2.00/2.25     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 2.00/2.25       ( k2_tarski @ A @ B ) ))).
% 2.00/2.25  thf(zf_stmt_0, negated_conjecture,
% 2.00/2.25    (~( ![A:$i,B:$i]:
% 2.00/2.25        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 2.00/2.25          ( k2_tarski @ A @ B ) ) )),
% 2.00/2.25    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 2.00/2.25  thf('0', plain,
% 2.00/2.25      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 2.00/2.25         != (k2_tarski @ sk_A @ sk_B))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf(t12_zfmisc_1, axiom,
% 2.00/2.25    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 2.00/2.25  thf('1', plain,
% 2.00/2.25      (![X49 : $i, X50 : $i]:
% 2.00/2.25         (r1_tarski @ (k1_tarski @ X49) @ (k2_tarski @ X49 @ X50))),
% 2.00/2.25      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 2.00/2.25  thf(l32_xboole_1, axiom,
% 2.00/2.25    (![A:$i,B:$i]:
% 2.00/2.25     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.00/2.25  thf('2', plain,
% 2.00/2.25      (![X8 : $i, X10 : $i]:
% 2.00/2.25         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 2.00/2.25      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.00/2.25  thf('3', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i]:
% 2.00/2.25         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 2.00/2.25           = (k1_xboole_0))),
% 2.00/2.25      inference('sup-', [status(thm)], ['1', '2'])).
% 2.00/2.25  thf(t98_xboole_1, axiom,
% 2.00/2.25    (![A:$i,B:$i]:
% 2.00/2.25     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.00/2.25  thf('4', plain,
% 2.00/2.25      (![X19 : $i, X20 : $i]:
% 2.00/2.25         ((k2_xboole_0 @ X19 @ X20)
% 2.00/2.25           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 2.00/2.25      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.00/2.25  thf('5', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i]:
% 2.00/2.25         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 2.00/2.25           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))),
% 2.00/2.25      inference('sup+', [status(thm)], ['3', '4'])).
% 2.00/2.25  thf(d10_xboole_0, axiom,
% 2.00/2.25    (![A:$i,B:$i]:
% 2.00/2.25     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.00/2.25  thf('6', plain,
% 2.00/2.25      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 2.00/2.25      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.00/2.25  thf('7', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 2.00/2.25      inference('simplify', [status(thm)], ['6'])).
% 2.00/2.25  thf('8', plain,
% 2.00/2.25      (![X8 : $i, X10 : $i]:
% 2.00/2.25         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 2.00/2.25      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.00/2.25  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.00/2.25      inference('sup-', [status(thm)], ['7', '8'])).
% 2.00/2.25  thf('10', plain,
% 2.00/2.25      (![X19 : $i, X20 : $i]:
% 2.00/2.25         ((k2_xboole_0 @ X19 @ X20)
% 2.00/2.25           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 2.00/2.25      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.00/2.25  thf('11', plain,
% 2.00/2.25      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.00/2.25      inference('sup+', [status(thm)], ['9', '10'])).
% 2.00/2.25  thf(idempotence_k2_xboole_0, axiom,
% 2.00/2.25    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 2.00/2.25  thf('12', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 2.00/2.25      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.00/2.25  thf('13', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.00/2.25      inference('demod', [status(thm)], ['11', '12'])).
% 2.00/2.25  thf('14', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i]:
% 2.00/2.25         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 2.00/2.25           = (k2_tarski @ X1 @ X0))),
% 2.00/2.25      inference('demod', [status(thm)], ['5', '13'])).
% 2.00/2.25  thf(commutativity_k3_xboole_0, axiom,
% 2.00/2.25    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.00/2.25  thf('15', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.00/2.25      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.00/2.25  thf(t100_xboole_1, axiom,
% 2.00/2.25    (![A:$i,B:$i]:
% 2.00/2.25     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.00/2.25  thf('16', plain,
% 2.00/2.25      (![X11 : $i, X12 : $i]:
% 2.00/2.25         ((k4_xboole_0 @ X11 @ X12)
% 2.00/2.25           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.00/2.25      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.00/2.25  thf('17', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i]:
% 2.00/2.25         ((k4_xboole_0 @ X0 @ X1)
% 2.00/2.25           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.00/2.25      inference('sup+', [status(thm)], ['15', '16'])).
% 2.00/2.25  thf('18', plain,
% 2.00/2.25      (![X11 : $i, X12 : $i]:
% 2.00/2.25         ((k4_xboole_0 @ X11 @ X12)
% 2.00/2.25           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.00/2.25      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.00/2.25  thf(commutativity_k5_xboole_0, axiom,
% 2.00/2.25    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 2.00/2.25  thf('19', plain,
% 2.00/2.25      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 2.00/2.25      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.00/2.25  thf(t91_xboole_1, axiom,
% 2.00/2.25    (![A:$i,B:$i,C:$i]:
% 2.00/2.25     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 2.00/2.25       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 2.00/2.25  thf('20', plain,
% 2.00/2.25      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.00/2.25         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 2.00/2.25           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 2.00/2.25      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.00/2.25  thf('21', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.00/2.25         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 2.00/2.25           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 2.00/2.25      inference('sup+', [status(thm)], ['19', '20'])).
% 2.00/2.25  thf('22', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.00/2.25         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 2.00/2.25           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X2)))),
% 2.00/2.25      inference('sup+', [status(thm)], ['18', '21'])).
% 2.00/2.25  thf('23', plain,
% 2.00/2.25      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.00/2.25         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 2.00/2.25           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 2.00/2.25      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.00/2.25  thf('24', plain,
% 2.00/2.25      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 2.00/2.25      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.00/2.25  thf('25', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.00/2.25         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 2.00/2.25           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.00/2.25      inference('sup+', [status(thm)], ['23', '24'])).
% 2.00/2.25  thf('26', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.00/2.25         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 2.00/2.25           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 2.00/2.25      inference('demod', [status(thm)], ['22', '25'])).
% 2.00/2.25  thf('27', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i]:
% 2.00/2.25         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)
% 2.00/2.25           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.00/2.25      inference('sup+', [status(thm)], ['17', '26'])).
% 2.00/2.25  thf('28', plain,
% 2.00/2.25      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 2.00/2.25      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.00/2.25  thf('29', plain,
% 2.00/2.25      (![X19 : $i, X20 : $i]:
% 2.00/2.25         ((k2_xboole_0 @ X19 @ X20)
% 2.00/2.25           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 2.00/2.25      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.00/2.25  thf('30', plain,
% 2.00/2.25      (![X19 : $i, X20 : $i]:
% 2.00/2.25         ((k2_xboole_0 @ X19 @ X20)
% 2.00/2.25           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 2.00/2.25      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.00/2.25  thf('31', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.00/2.25      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 2.00/2.25  thf('32', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i]:
% 2.00/2.25         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 2.00/2.25           = (k2_tarski @ X1 @ X0))),
% 2.00/2.25      inference('demod', [status(thm)], ['14', '31'])).
% 2.00/2.25  thf('33', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 2.00/2.25      inference('demod', [status(thm)], ['0', '32'])).
% 2.00/2.25  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 2.00/2.25  
% 2.00/2.25  % SZS output end Refutation
% 2.00/2.25  
% 2.00/2.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
