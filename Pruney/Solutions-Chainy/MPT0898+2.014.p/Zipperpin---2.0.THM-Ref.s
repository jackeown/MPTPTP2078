%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xrbKTvQhCP

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 132 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  410 (1597 expanded)
%              Number of equality atoms :   82 ( 280 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(t58_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
        = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
          = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_mcart_1])).

thf('0',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
       != k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('2',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t53_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X11 @ X12 @ X13 ) @ X14 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X11 @ X12 @ X13 ) @ X14 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t134_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ( X0 = X3 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = sk_B )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference(eq_res,[status(thm)],['12'])).

thf('14',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
       != k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('17',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['17'])).

thf('20',plain,
    ( ( sk_B = sk_A )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != sk_A ) ),
    inference(demod,[status(thm)],['3','18','19'])).

thf('21',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
 != sk_A ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ( X15 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X19 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('24',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X16 @ X17 @ X19 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['17'])).

thf('26',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['17'])).

thf('27',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ X16 @ X17 @ X19 )
      = sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xrbKTvQhCP
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:26:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 99 iterations in 0.066s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(t58_mcart_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.20/0.50       ( ( A ) = ( B ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.20/0.50          ( ( A ) = ( B ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.50         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t55_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.20/0.50       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.50         (((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18) != (k1_xboole_0))
% 0.20/0.50          | ((X18) = (k1_xboole_0))
% 0.20/0.50          | ((X17) = (k1_xboole_0))
% 0.20/0.50          | ((X16) = (k1_xboole_0))
% 0.20/0.50          | ((X15) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      ((((sk_B) = (k1_xboole_0))
% 0.20/0.50        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.50  thf(t53_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.20/0.50       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         ((k4_zfmisc_1 @ X11 @ X12 @ X13 @ X14)
% 0.20/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13) @ 
% 0.20/0.50              X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.20/0.50  thf(d3_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.50       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.20/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         ((k4_zfmisc_1 @ X11 @ X12 @ X13 @ X14)
% 0.20/0.50           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X11 @ X12 @ X13) @ X14))),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.50         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         ((k4_zfmisc_1 @ X11 @ X12 @ X13 @ X14)
% 0.20/0.50           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X11 @ X12 @ X13) @ X14))),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf(t134_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.20/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.50         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (((X0) = (k1_xboole_0))
% 0.20/0.50          | ((X1) = (k1_xboole_0))
% 0.20/0.50          | ((k2_zfmisc_1 @ X1 @ X0) != (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.50          | ((X0) = (X3)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         (((k2_zfmisc_1 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.50          | ((X4) = (X0))
% 0.20/0.50          | ((X5) = (k1_xboole_0))
% 0.20/0.50          | ((X4) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k2_zfmisc_1 @ X1 @ X0) != (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | ((X1) = (k1_xboole_0))
% 0.20/0.50          | ((X0) = (sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.50            != (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.20/0.50          | ((X0) = (sk_B))
% 0.20/0.50          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 0.20/0.50          | ((X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      ((((sk_A) = (k1_xboole_0))
% 0.20/0.50        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (sk_B)))),
% 0.20/0.50      inference('eq_res', [status(thm)], ['12'])).
% 0.20/0.50  thf('14', plain, (((sk_A) != (sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((((sk_A) = (k1_xboole_0))
% 0.20/0.50        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf(t35_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.20/0.50       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         (((k3_zfmisc_1 @ X7 @ X8 @ X9) != (k1_xboole_0))
% 0.20/0.50          | ((X9) = (k1_xboole_0))
% 0.20/0.50          | ((X8) = (k1_xboole_0))
% 0.20/0.50          | ((X7) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.50  thf('19', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((((sk_B) = (sk_A))
% 0.20/0.50        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '18', '19'])).
% 0.20/0.50  thf('21', plain, (((sk_A) != (sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain, (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 0.20/0.50         (((X15) != (k1_xboole_0))
% 0.20/0.50          | ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X19) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.20/0.50         ((k4_zfmisc_1 @ k1_xboole_0 @ X16 @ X17 @ X19) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.50  thf('25', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.50  thf('26', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.20/0.50         ((k4_zfmisc_1 @ sk_A @ X16 @ X17 @ X19) = (sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.50  thf('28', plain, (((sk_A) != (sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['22', '27'])).
% 0.20/0.50  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
