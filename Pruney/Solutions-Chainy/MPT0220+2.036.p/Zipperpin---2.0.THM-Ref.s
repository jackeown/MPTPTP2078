%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZAKf2qOZAA

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:23 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   57 (  66 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  391 ( 466 expanded)
%              Number of equality atoms :   44 (  53 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X44: $i,X45: $i] :
      ( r1_tarski @ ( k1_tarski @ X44 ) @ ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','32'])).

thf('34',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','33'])).

thf('35',plain,(
    $false ),
    inference(simplify,[status(thm)],['34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZAKf2qOZAA
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.66/0.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.84  % Solved by: fo/fo7.sh
% 0.66/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.84  % done 238 iterations in 0.383s
% 0.66/0.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.84  % SZS output start Refutation
% 0.66/0.84  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.66/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.84  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.66/0.84  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.66/0.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.66/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.66/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.84  thf(t14_zfmisc_1, conjecture,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.66/0.84       ( k2_tarski @ A @ B ) ))).
% 0.66/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.84    (~( ![A:$i,B:$i]:
% 0.66/0.84        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.66/0.84          ( k2_tarski @ A @ B ) ) )),
% 0.66/0.84    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.66/0.84  thf('0', plain,
% 0.66/0.84      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.66/0.84         != (k2_tarski @ sk_A @ sk_B))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf(t12_zfmisc_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.66/0.84  thf('1', plain,
% 0.66/0.84      (![X44 : $i, X45 : $i]:
% 0.66/0.84         (r1_tarski @ (k1_tarski @ X44) @ (k2_tarski @ X44 @ X45))),
% 0.66/0.84      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.66/0.84  thf(l32_xboole_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.66/0.84  thf('2', plain,
% 0.66/0.84      (![X4 : $i, X6 : $i]:
% 0.66/0.84         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.66/0.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.66/0.84  thf('3', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.66/0.84           = (k1_xboole_0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['1', '2'])).
% 0.66/0.84  thf(t98_xboole_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.66/0.84  thf('4', plain,
% 0.66/0.84      (![X14 : $i, X15 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ X14 @ X15)
% 0.66/0.84           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.66/0.84  thf('5', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.66/0.84           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['3', '4'])).
% 0.66/0.84  thf(commutativity_k5_xboole_0, axiom,
% 0.66/0.84    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.66/0.84  thf('6', plain,
% 0.66/0.84      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.84  thf('7', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.66/0.84           = (k5_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0)))),
% 0.66/0.84      inference('demod', [status(thm)], ['5', '6'])).
% 0.66/0.84  thf(t4_boole, axiom,
% 0.66/0.84    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.66/0.84  thf('8', plain,
% 0.66/0.84      (![X10 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.66/0.84      inference('cnf', [status(esa)], [t4_boole])).
% 0.66/0.84  thf('9', plain,
% 0.66/0.84      (![X14 : $i, X15 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ X14 @ X15)
% 0.66/0.84           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.66/0.84  thf('10', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['8', '9'])).
% 0.66/0.84  thf(t1_boole, axiom,
% 0.66/0.84    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.66/0.84  thf('11', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.66/0.84      inference('cnf', [status(esa)], [t1_boole])).
% 0.66/0.84  thf('12', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.66/0.84      inference('demod', [status(thm)], ['10', '11'])).
% 0.66/0.84  thf('13', plain,
% 0.66/0.84      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.84  thf('14', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['12', '13'])).
% 0.66/0.84  thf('15', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.66/0.84           = (k2_tarski @ X1 @ X0))),
% 0.66/0.84      inference('demod', [status(thm)], ['7', '14'])).
% 0.66/0.84  thf(commutativity_k3_xboole_0, axiom,
% 0.66/0.84    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.66/0.84  thf('16', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.84  thf(t100_xboole_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.66/0.84  thf('17', plain,
% 0.66/0.84      (![X7 : $i, X8 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X7 @ X8)
% 0.66/0.84           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.84  thf('18', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X0 @ X1)
% 0.66/0.84           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['16', '17'])).
% 0.66/0.84  thf('19', plain,
% 0.66/0.84      (![X7 : $i, X8 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X7 @ X8)
% 0.66/0.84           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.84  thf('20', plain,
% 0.66/0.84      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.84  thf(t91_xboole_1, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i]:
% 0.66/0.84     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.66/0.84       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.66/0.84  thf('21', plain,
% 0.66/0.84      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.66/0.84         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.66/0.84           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.84  thf('22', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.66/0.84           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['20', '21'])).
% 0.66/0.84  thf('23', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.66/0.84           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X2)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['19', '22'])).
% 0.66/0.84  thf('24', plain,
% 0.66/0.84      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.66/0.84         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.66/0.84           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.84  thf('25', plain,
% 0.66/0.84      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.84  thf('26', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.66/0.84           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['24', '25'])).
% 0.66/0.84  thf('27', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.66/0.84           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.66/0.84      inference('demod', [status(thm)], ['23', '26'])).
% 0.66/0.84  thf('28', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)
% 0.66/0.84           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['18', '27'])).
% 0.66/0.84  thf('29', plain,
% 0.66/0.84      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.84  thf('30', plain,
% 0.66/0.84      (![X14 : $i, X15 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ X14 @ X15)
% 0.66/0.84           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.66/0.84  thf('31', plain,
% 0.66/0.84      (![X14 : $i, X15 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ X14 @ X15)
% 0.66/0.84           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.66/0.84  thf('32', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.66/0.84  thf('33', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.66/0.84           = (k2_tarski @ X1 @ X0))),
% 0.66/0.84      inference('demod', [status(thm)], ['15', '32'])).
% 0.66/0.84  thf('34', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.66/0.84      inference('demod', [status(thm)], ['0', '33'])).
% 0.66/0.84  thf('35', plain, ($false), inference('simplify', [status(thm)], ['34'])).
% 0.66/0.84  
% 0.66/0.84  % SZS output end Refutation
% 0.66/0.84  
% 0.66/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
