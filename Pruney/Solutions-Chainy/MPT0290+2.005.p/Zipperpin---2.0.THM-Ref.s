%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.24znHXnXGI

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:53 EST 2020

% Result     : Theorem 3.21s
% Output     : Refutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  62 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  317 ( 419 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t97_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('17',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X17 ) @ ( k3_tarski @ X18 ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X17 ) @ ( k3_tarski @ X18 ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_tarski @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_tarski @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_tarski @ X1 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.24znHXnXGI
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:11:05 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 3.21/3.39  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.21/3.39  % Solved by: fo/fo7.sh
% 3.21/3.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.21/3.39  % done 4728 iterations in 2.924s
% 3.21/3.39  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.21/3.39  % SZS output start Refutation
% 3.21/3.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.21/3.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.21/3.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.21/3.39  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.21/3.39  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.21/3.39  thf(sk_B_type, type, sk_B: $i).
% 3.21/3.39  thf(sk_A_type, type, sk_A: $i).
% 3.21/3.39  thf(t97_zfmisc_1, conjecture,
% 3.21/3.39    (![A:$i,B:$i]:
% 3.21/3.39     ( r1_tarski @
% 3.21/3.39       ( k3_tarski @ ( k3_xboole_0 @ A @ B ) ) @ 
% 3.21/3.39       ( k3_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 3.21/3.39  thf(zf_stmt_0, negated_conjecture,
% 3.21/3.39    (~( ![A:$i,B:$i]:
% 3.21/3.39        ( r1_tarski @
% 3.21/3.39          ( k3_tarski @ ( k3_xboole_0 @ A @ B ) ) @ 
% 3.21/3.39          ( k3_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )),
% 3.21/3.39    inference('cnf.neg', [status(esa)], [t97_zfmisc_1])).
% 3.21/3.39  thf('0', plain,
% 3.21/3.39      (~ (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 3.21/3.39          (k3_xboole_0 @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B)))),
% 3.21/3.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.39  thf(d10_xboole_0, axiom,
% 3.21/3.39    (![A:$i,B:$i]:
% 3.21/3.39     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.21/3.39  thf('1', plain,
% 3.21/3.39      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 3.21/3.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.21/3.39  thf('2', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 3.21/3.39      inference('simplify', [status(thm)], ['1'])).
% 3.21/3.39  thf(l32_xboole_1, axiom,
% 3.21/3.39    (![A:$i,B:$i]:
% 3.21/3.39     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.21/3.39  thf('3', plain,
% 3.21/3.39      (![X4 : $i, X6 : $i]:
% 3.21/3.39         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 3.21/3.39      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.21/3.39  thf('4', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.21/3.39      inference('sup-', [status(thm)], ['2', '3'])).
% 3.21/3.39  thf(t49_xboole_1, axiom,
% 3.21/3.39    (![A:$i,B:$i,C:$i]:
% 3.21/3.39     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 3.21/3.39       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 3.21/3.39  thf('5', plain,
% 3.21/3.39      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.21/3.39         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 3.21/3.39           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 3.21/3.39      inference('cnf', [status(esa)], [t49_xboole_1])).
% 3.21/3.39  thf('6', plain,
% 3.21/3.39      (![X4 : $i, X5 : $i]:
% 3.21/3.39         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 3.21/3.39      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.21/3.39  thf('7', plain,
% 3.21/3.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.39         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 3.21/3.39          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 3.21/3.39      inference('sup-', [status(thm)], ['5', '6'])).
% 3.21/3.39  thf('8', plain,
% 3.21/3.39      (![X0 : $i, X1 : $i]:
% 3.21/3.39         (((k3_xboole_0 @ X1 @ k1_xboole_0) != (k1_xboole_0))
% 3.21/3.39          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 3.21/3.39      inference('sup-', [status(thm)], ['4', '7'])).
% 3.21/3.39  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.21/3.39      inference('sup-', [status(thm)], ['2', '3'])).
% 3.21/3.39  thf(t48_xboole_1, axiom,
% 3.21/3.39    (![A:$i,B:$i]:
% 3.21/3.39     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.21/3.39  thf('10', plain,
% 3.21/3.39      (![X12 : $i, X13 : $i]:
% 3.21/3.39         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 3.21/3.39           = (k3_xboole_0 @ X12 @ X13))),
% 3.21/3.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.21/3.39  thf('11', plain,
% 3.21/3.39      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 3.21/3.39      inference('sup+', [status(thm)], ['9', '10'])).
% 3.21/3.39  thf(idempotence_k3_xboole_0, axiom,
% 3.21/3.39    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 3.21/3.39  thf('12', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 3.21/3.39      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 3.21/3.39  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.21/3.39      inference('demod', [status(thm)], ['11', '12'])).
% 3.21/3.39  thf('14', plain,
% 3.21/3.39      (![X12 : $i, X13 : $i]:
% 3.21/3.39         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 3.21/3.39           = (k3_xboole_0 @ X12 @ X13))),
% 3.21/3.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.21/3.39  thf('15', plain,
% 3.21/3.39      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.21/3.39      inference('sup+', [status(thm)], ['13', '14'])).
% 3.21/3.39  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.21/3.39      inference('sup-', [status(thm)], ['2', '3'])).
% 3.21/3.39  thf('17', plain,
% 3.21/3.39      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.21/3.39      inference('demod', [status(thm)], ['15', '16'])).
% 3.21/3.39  thf('18', plain,
% 3.21/3.39      (![X0 : $i, X1 : $i]:
% 3.21/3.39         (((k1_xboole_0) != (k1_xboole_0))
% 3.21/3.39          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 3.21/3.39      inference('demod', [status(thm)], ['8', '17'])).
% 3.21/3.39  thf('19', plain,
% 3.21/3.39      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 3.21/3.39      inference('simplify', [status(thm)], ['18'])).
% 3.21/3.39  thf(t95_zfmisc_1, axiom,
% 3.21/3.39    (![A:$i,B:$i]:
% 3.21/3.39     ( ( r1_tarski @ A @ B ) =>
% 3.21/3.39       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 3.21/3.39  thf('20', plain,
% 3.21/3.39      (![X17 : $i, X18 : $i]:
% 3.21/3.39         ((r1_tarski @ (k3_tarski @ X17) @ (k3_tarski @ X18))
% 3.21/3.39          | ~ (r1_tarski @ X17 @ X18))),
% 3.21/3.39      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 3.21/3.39  thf('21', plain,
% 3.21/3.39      (![X0 : $i, X1 : $i]:
% 3.21/3.39         (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X1 @ X0)) @ (k3_tarski @ X0))),
% 3.21/3.39      inference('sup-', [status(thm)], ['19', '20'])).
% 3.21/3.39  thf('22', plain,
% 3.21/3.39      (![X12 : $i, X13 : $i]:
% 3.21/3.39         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 3.21/3.39           = (k3_xboole_0 @ X12 @ X13))),
% 3.21/3.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.21/3.39  thf(t36_xboole_1, axiom,
% 3.21/3.39    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.21/3.39  thf('23', plain,
% 3.21/3.39      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 3.21/3.39      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.21/3.39  thf('24', plain,
% 3.21/3.39      (![X17 : $i, X18 : $i]:
% 3.21/3.39         ((r1_tarski @ (k3_tarski @ X17) @ (k3_tarski @ X18))
% 3.21/3.39          | ~ (r1_tarski @ X17 @ X18))),
% 3.21/3.39      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 3.21/3.39  thf('25', plain,
% 3.21/3.39      (![X0 : $i, X1 : $i]:
% 3.21/3.39         (r1_tarski @ (k3_tarski @ (k4_xboole_0 @ X0 @ X1)) @ (k3_tarski @ X0))),
% 3.21/3.39      inference('sup-', [status(thm)], ['23', '24'])).
% 3.21/3.39  thf('26', plain,
% 3.21/3.39      (![X0 : $i, X1 : $i]:
% 3.21/3.39         (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X1 @ X0)) @ (k3_tarski @ X1))),
% 3.21/3.39      inference('sup+', [status(thm)], ['22', '25'])).
% 3.21/3.39  thf(t19_xboole_1, axiom,
% 3.21/3.39    (![A:$i,B:$i,C:$i]:
% 3.21/3.39     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 3.21/3.39       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 3.21/3.39  thf('27', plain,
% 3.21/3.39      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.21/3.39         (~ (r1_tarski @ X7 @ X8)
% 3.21/3.39          | ~ (r1_tarski @ X7 @ X9)
% 3.21/3.39          | (r1_tarski @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 3.21/3.39      inference('cnf', [status(esa)], [t19_xboole_1])).
% 3.21/3.39  thf('28', plain,
% 3.21/3.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.39         ((r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X0 @ X1)) @ 
% 3.21/3.39           (k3_xboole_0 @ (k3_tarski @ X0) @ X2))
% 3.21/3.39          | ~ (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 3.21/3.39      inference('sup-', [status(thm)], ['26', '27'])).
% 3.21/3.39  thf('29', plain,
% 3.21/3.39      (![X0 : $i, X1 : $i]:
% 3.21/3.39         (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.21/3.39          (k3_xboole_0 @ (k3_tarski @ X1) @ (k3_tarski @ X0)))),
% 3.21/3.39      inference('sup-', [status(thm)], ['21', '28'])).
% 3.21/3.39  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 3.21/3.39  
% 3.21/3.39  % SZS output end Refutation
% 3.21/3.39  
% 3.21/3.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
