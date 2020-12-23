%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BM1ureRnjO

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  84 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  379 ( 582 expanded)
%              Number of equality atoms :   42 (  66 expanded)
%              Maximal formula depth    :    8 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t19_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t19_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ ( k1_tarski @ X22 ) @ ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['22','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','37'])).

thf('39',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BM1ureRnjO
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 277 iterations in 0.113s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.57  thf(t19_zfmisc_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.57       ( k1_tarski @ A ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i]:
% 0.21/0.57        ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.57          ( k1_tarski @ A ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t19_zfmisc_1])).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.57         != (k1_tarski @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t12_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i]:
% 0.21/0.57         (r1_tarski @ (k1_tarski @ X22) @ (k2_tarski @ X22 @ X23))),
% 0.21/0.57      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.21/0.57  thf(l32_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X5 : $i, X7 : $i]:
% 0.21/0.57         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.21/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.21/0.57           = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf(t48_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.21/0.57           = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0)
% 0.21/0.57           = (k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.57  thf(d10_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.57  thf('7', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.21/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X5 : $i, X7 : $i]:
% 0.21/0.57         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.21/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.57  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.21/0.57           = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf(t47_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X8 : $i, X9 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.21/0.57           = (k4_xboole_0 @ X8 @ X9))),
% 0.21/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X5 : $i, X6 : $i]:
% 0.21/0.57         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.21/0.57          | (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.57          | (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.57  thf('18', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (![X0 : $i]: (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['12', '18'])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X2 : $i, X4 : $i]:
% 0.21/0.57         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.57          | ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ X0) @ X0)
% 0.21/0.57          | ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['11', '21'])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X8 : $i, X9 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.21/0.57           = (k4_xboole_0 @ X8 @ X9))),
% 0.21/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.21/0.57           = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.21/0.57           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.21/0.57           = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.57           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (![X8 : $i, X9 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.21/0.57           = (k4_xboole_0 @ X8 @ X9))),
% 0.21/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.57           = (k4_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.21/0.57      inference('sup+', [status(thm)], ['27', '30'])).
% 0.21/0.57  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.21/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (![X5 : $i, X6 : $i]:
% 0.21/0.57         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.57          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.21/0.57      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.57  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['22', '36'])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k1_tarski @ X1)
% 0.21/0.57           = (k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['5', '37'])).
% 0.21/0.57  thf('39', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '38'])).
% 0.21/0.57  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
