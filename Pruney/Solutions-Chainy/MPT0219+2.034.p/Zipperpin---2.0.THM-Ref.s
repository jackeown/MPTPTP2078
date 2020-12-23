%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c1T80XfhCM

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:08 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   52 (  64 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   17
%              Number of atoms          :  323 ( 416 expanded)
%              Number of equality atoms :   39 (  51 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('23',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('27',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32 = X31 )
      | ~ ( r1_tarski @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('28',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c1T80XfhCM
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.67/0.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.87  % Solved by: fo/fo7.sh
% 0.67/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.87  % done 1428 iterations in 0.392s
% 0.67/0.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.87  % SZS output start Refutation
% 0.67/0.87  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.67/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.87  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.67/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.87  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.67/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.87  thf(t13_zfmisc_1, conjecture,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.67/0.87         ( k1_tarski @ A ) ) =>
% 0.67/0.87       ( ( A ) = ( B ) ) ))).
% 0.67/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.87    (~( ![A:$i,B:$i]:
% 0.67/0.87        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.67/0.87            ( k1_tarski @ A ) ) =>
% 0.67/0.87          ( ( A ) = ( B ) ) ) )),
% 0.67/0.87    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.67/0.87  thf('0', plain,
% 0.67/0.87      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.67/0.87         = (k1_tarski @ sk_A))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf(t79_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.67/0.87  thf('1', plain,
% 0.67/0.87      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 0.67/0.87      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.67/0.87  thf(d7_xboole_0, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.67/0.87       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.67/0.87  thf('2', plain,
% 0.67/0.87      (![X4 : $i, X5 : $i]:
% 0.67/0.87         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.67/0.87      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.67/0.87  thf('3', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.67/0.87  thf(commutativity_k3_xboole_0, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.67/0.87  thf('4', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.67/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.67/0.87  thf('5', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.67/0.87      inference('demod', [status(thm)], ['3', '4'])).
% 0.67/0.87  thf('6', plain,
% 0.67/0.87      (![X4 : $i, X6 : $i]:
% 0.67/0.87         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.67/0.87      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.67/0.87  thf('7', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (((k1_xboole_0) != (k1_xboole_0))
% 0.67/0.87          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['5', '6'])).
% 0.67/0.87  thf('8', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.67/0.87      inference('simplify', [status(thm)], ['7'])).
% 0.67/0.87  thf(t83_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.67/0.87  thf('9', plain,
% 0.67/0.87      (![X16 : $i, X17 : $i]:
% 0.67/0.87         (((k4_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_xboole_0 @ X16 @ X17))),
% 0.67/0.87      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.67/0.87  thf('10', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['8', '9'])).
% 0.67/0.87  thf(t98_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.67/0.87  thf('11', plain,
% 0.67/0.87      (![X19 : $i, X20 : $i]:
% 0.67/0.87         ((k2_xboole_0 @ X19 @ X20)
% 0.67/0.87           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.67/0.87  thf('12', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.67/0.87           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.67/0.87      inference('sup+', [status(thm)], ['10', '11'])).
% 0.67/0.87  thf(commutativity_k5_xboole_0, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.67/0.87  thf('13', plain,
% 0.67/0.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.67/0.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.67/0.87  thf('14', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.67/0.87           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.87      inference('demod', [status(thm)], ['12', '13'])).
% 0.67/0.87  thf('15', plain,
% 0.67/0.87      (![X19 : $i, X20 : $i]:
% 0.67/0.87         ((k2_xboole_0 @ X19 @ X20)
% 0.67/0.87           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.67/0.87  thf('16', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((k2_xboole_0 @ X0 @ X1)
% 0.67/0.87           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.67/0.87      inference('sup+', [status(thm)], ['14', '15'])).
% 0.67/0.87  thf(t21_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.67/0.87  thf('17', plain,
% 0.67/0.87      (![X12 : $i, X13 : $i]:
% 0.67/0.87         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 0.67/0.87      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.67/0.87  thf('18', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 0.67/0.87           = (k4_xboole_0 @ X0 @ X1))),
% 0.67/0.87      inference('sup+', [status(thm)], ['16', '17'])).
% 0.67/0.87  thf('19', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.67/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.67/0.87  thf('20', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.67/0.87           = (k4_xboole_0 @ X0 @ X1))),
% 0.67/0.87      inference('demod', [status(thm)], ['18', '19'])).
% 0.67/0.87  thf('21', plain,
% 0.67/0.87      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.67/0.87         (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 0.67/0.87         = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.67/0.87      inference('sup+', [status(thm)], ['0', '20'])).
% 0.67/0.87  thf('22', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.67/0.87      inference('demod', [status(thm)], ['3', '4'])).
% 0.67/0.87  thf('23', plain,
% 0.67/0.87      (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.67/0.87      inference('demod', [status(thm)], ['21', '22'])).
% 0.67/0.87  thf(l32_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.87  thf('24', plain,
% 0.67/0.87      (![X7 : $i, X8 : $i]:
% 0.67/0.87         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 0.67/0.87      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.67/0.87  thf('25', plain,
% 0.67/0.87      ((((k1_xboole_0) != (k1_xboole_0))
% 0.67/0.87        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['23', '24'])).
% 0.67/0.87  thf('26', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 0.67/0.87      inference('simplify', [status(thm)], ['25'])).
% 0.67/0.87  thf(t6_zfmisc_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.67/0.87       ( ( A ) = ( B ) ) ))).
% 0.67/0.87  thf('27', plain,
% 0.67/0.87      (![X31 : $i, X32 : $i]:
% 0.67/0.87         (((X32) = (X31))
% 0.67/0.87          | ~ (r1_tarski @ (k1_tarski @ X32) @ (k1_tarski @ X31)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.67/0.87  thf('28', plain, (((sk_B) = (sk_A))),
% 0.67/0.87      inference('sup-', [status(thm)], ['26', '27'])).
% 0.67/0.87  thf('29', plain, (((sk_A) != (sk_B))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('30', plain, ($false),
% 0.67/0.87      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.67/0.87  
% 0.67/0.87  % SZS output end Refutation
% 0.67/0.87  
% 0.67/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
