%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PsURvzgmtI

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 108 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  457 (1284 expanded)
%              Number of equality atoms :   77 ( 177 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 ) ) ),
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

thf('4',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t37_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
       != ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4 ) )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 )
      | ( X0 = X4 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4 ) )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( X0 = X4 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_B = X0 )
      | ( ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_B = X0 )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_B = sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('20',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','21'])).

thf('23',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['23','27'])).

thf('29',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PsURvzgmtI
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 24 iterations in 0.023s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(t58_mcart_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.20/0.48       ( ( A ) = ( B ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.20/0.48          ( ( A ) = ( B ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.48         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t55_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.20/0.48       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.48         (((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16) != (k1_xboole_0))
% 0.20/0.48          | ((X16) = (k1_xboole_0))
% 0.20/0.48          | ((X15) = (k1_xboole_0))
% 0.20/0.48          | ((X14) = (k1_xboole_0))
% 0.20/0.48          | ((X13) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      ((((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.48         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d3_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.48       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.20/0.48           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.20/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(d4_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.20/0.48       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.20/0.48           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.48           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.48           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf(t37_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.48     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.20/0.48       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.48         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         (((k3_zfmisc_1 @ X7 @ X8 @ X9) = (k1_xboole_0))
% 0.20/0.48          | ((k3_zfmisc_1 @ X7 @ X8 @ X9) != (k3_zfmisc_1 @ X10 @ X11 @ X12))
% 0.20/0.48          | ((X9) = (X12)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.48          | ((X4) = (X0))
% 0.20/0.48          | ((k3_zfmisc_1 @ X6 @ X5 @ X4) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.48            != (k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4))
% 0.20/0.48          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.48          | ((X0) = (X4)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.48           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.48            != (k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4))
% 0.20/0.48          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.48          | ((X0) = (X4)))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.48            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.48          | ((sk_B) = (X0))
% 0.20/0.48          | ((k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.48         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.48            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.48          | ((sk_B) = (X0))
% 0.20/0.48          | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (sk_A)))),
% 0.20/0.48      inference('eq_res', [status(thm)], ['18'])).
% 0.20/0.48  thf('20', plain, (((sk_A) != (sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((((sk_B) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '21'])).
% 0.20/0.48  thf('23', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.48         (((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16) != (k1_xboole_0))
% 0.20/0.48          | ((X16) = (k1_xboole_0))
% 0.20/0.48          | ((X15) = (k1_xboole_0))
% 0.20/0.48          | ((X14) = (k1_xboole_0))
% 0.20/0.48          | ((X13) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.48  thf('28', plain, (((sk_A) = (sk_B))),
% 0.20/0.48      inference('sup+', [status(thm)], ['23', '27'])).
% 0.20/0.48  thf('29', plain, (((sk_A) != (sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
