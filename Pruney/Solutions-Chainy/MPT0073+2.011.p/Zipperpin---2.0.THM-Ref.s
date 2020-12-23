%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yzOAPxyQQX

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 235 expanded)
%              Number of leaves         :   18 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  342 (1895 expanded)
%              Number of equality atoms :   25 ( 246 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t66_xboole_1,conjecture,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( ( A != k1_xboole_0 )
            & ( r1_xboole_0 @ A @ A ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ A )
            & ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_xboole_1])).

thf('0',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('5',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_A )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ k1_xboole_0 )
   <= ( ~ ( r1_xboole_0 @ sk_A @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r1_xboole_0 @ sk_A @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    r1_xboole_0 @ sk_A @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','10','11'])).

thf('13',plain,(
    r1_xboole_0 @ sk_A @ sk_A ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ~ ( r2_hidden @ C @ A )
            & ( r2_hidden @ C @ B ) )
        & ~ ( ~ ( r2_hidden @ C @ B )
            & ( r2_hidden @ C @ A ) )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( r2_hidden @ C @ A )
        & ~ ( r2_hidden @ C @ B ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( r2_hidden @ C @ B )
        & ~ ( r2_hidden @ C @ A ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ A @ B )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( zip_tseitin_0 @ X11 @ X10 @ X9 )
      | ( zip_tseitin_1 @ X11 @ X10 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ X0 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( zip_tseitin_0 @ ( sk_B @ X0 ) @ X0 @ X0 )
      | ( zip_tseitin_1 @ ( sk_B @ X0 ) @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( zip_tseitin_1 @ ( sk_B @ sk_A ) @ sk_A @ sk_A )
    | ( zip_tseitin_0 @ ( sk_B @ sk_A ) @ sk_A @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('21',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','10'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( zip_tseitin_1 @ ( sk_B @ sk_A ) @ sk_A @ sk_A )
    | ( zip_tseitin_0 @ ( sk_B @ sk_A ) @ sk_A @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( zip_tseitin_1 @ X6 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ sk_A ) @ sk_A @ sk_A )
    | ~ ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( zip_tseitin_1 @ ( sk_B @ sk_A ) @ sk_A @ sk_A )
    | ( zip_tseitin_0 @ ( sk_B @ sk_A ) @ sk_A @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['19','22'])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( zip_tseitin_1 @ X6 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('28',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ sk_A ) @ sk_A @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('30',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    zip_tseitin_0 @ ( sk_B @ sk_A ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('33',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yzOAPxyQQX
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 31 iterations in 0.015s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.47  thf(t66_xboole_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.21/0.47       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.21/0.47          ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t66_xboole_1])).
% 0.21/0.47  thf('0', plain, (((r1_xboole_0 @ sk_A @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (((r1_xboole_0 @ sk_A @ sk_A)) <= (((r1_xboole_0 @ sk_A @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      ((((sk_A) != (k1_xboole_0)) | ~ (r1_xboole_0 @ sk_A @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (~ (((sk_A) = (k1_xboole_0))) | ~ ((r1_xboole_0 @ sk_A @ sk_A))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.47  thf('4', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.47  thf('5', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      ((~ (r1_xboole_0 @ sk_A @ sk_A)) <= (~ ((r1_xboole_0 @ sk_A @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      ((~ (r1_xboole_0 @ sk_A @ k1_xboole_0))
% 0.21/0.47         <= (~ ((r1_xboole_0 @ sk_A @ sk_A)) & (((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.47         <= (~ ((r1_xboole_0 @ sk_A @ sk_A)) & (((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (((r1_xboole_0 @ sk_A @ sk_A)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (((r1_xboole_0 @ sk_A @ sk_A)) | (((sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('12', plain, (((r1_xboole_0 @ sk_A @ sk_A))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['3', '10', '11'])).
% 0.21/0.47  thf('13', plain, ((r1_xboole_0 @ sk_A @ sk_A)),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['1', '12'])).
% 0.21/0.47  thf(t7_xboole_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X12 : $i]:
% 0.21/0.47         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.47  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.47  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.47  thf(t5_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ~( ( ~( ( ~( r2_hidden @ C @ A ) ) & ( r2_hidden @ C @ B ) ) ) & 
% 0.21/0.47          ( ~( ( ~( r2_hidden @ C @ B ) ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.47          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ B ) ) ))).
% 0.21/0.47  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.47  thf(zf_stmt_2, axiom,
% 0.21/0.47    (![C:$i,B:$i,A:$i]:
% 0.21/0.47     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.47       ( ( r2_hidden @ C @ A ) & ( ~( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.21/0.47  thf(zf_stmt_4, axiom,
% 0.21/0.47    (![C:$i,B:$i,A:$i]:
% 0.21/0.47     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.21/0.47       ( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_5, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ~( ( r1_xboole_0 @ A @ B ) & 
% 0.21/0.47          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & 
% 0.21/0.47          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.47          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.47         (~ (r1_xboole_0 @ X9 @ X10)
% 0.21/0.47          | (zip_tseitin_0 @ X11 @ X10 @ X9)
% 0.21/0.47          | (zip_tseitin_1 @ X11 @ X10 @ X9)
% 0.21/0.47          | ~ (r2_hidden @ X11 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.47          | (zip_tseitin_1 @ X1 @ X0 @ X0)
% 0.21/0.47          | (zip_tseitin_0 @ X1 @ X0 @ X0)
% 0.21/0.47          | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((X0) = (k1_xboole_0))
% 0.21/0.47          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.21/0.47          | (zip_tseitin_0 @ (sk_B @ X0) @ X0 @ X0)
% 0.21/0.47          | (zip_tseitin_1 @ (sk_B @ X0) @ X0 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (((zip_tseitin_1 @ (sk_B @ sk_A) @ sk_A @ sk_A)
% 0.21/0.47        | (zip_tseitin_0 @ (sk_B @ sk_A) @ sk_A @ sk_A)
% 0.21/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('21', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['3', '10'])).
% 0.21/0.47  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (((zip_tseitin_1 @ (sk_B @ sk_A) @ sk_A @ sk_A)
% 0.21/0.47        | (zip_tseitin_0 @ (sk_B @ sk_A) @ sk_A @ sk_A))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['19', '22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X6 @ X8) | ~ (zip_tseitin_1 @ X6 @ X8 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (((zip_tseitin_0 @ (sk_B @ sk_A) @ sk_A @ sk_A)
% 0.21/0.47        | ~ (r2_hidden @ (sk_B @ sk_A) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (((zip_tseitin_1 @ (sk_B @ sk_A) @ sk_A @ sk_A)
% 0.21/0.47        | (zip_tseitin_0 @ (sk_B @ sk_A) @ sk_A @ sk_A))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['19', '22'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         ((r2_hidden @ X6 @ X7) | ~ (zip_tseitin_1 @ X6 @ X8 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (((zip_tseitin_0 @ (sk_B @ sk_A) @ sk_A @ sk_A)
% 0.21/0.47        | (r2_hidden @ (sk_B @ sk_A) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.47         ((r2_hidden @ X3 @ X4) | ~ (zip_tseitin_0 @ X3 @ X4 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.47  thf('30', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_A)),
% 0.21/0.47      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.47  thf('31', plain, ((zip_tseitin_0 @ (sk_B @ sk_A) @ sk_A @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['25', '30'])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X3 @ X5) | ~ (zip_tseitin_0 @ X3 @ X4 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.47  thf('33', plain, (~ (r2_hidden @ (sk_B @ sk_A) @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('34', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_A)),
% 0.21/0.47      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.47  thf('35', plain, ($false), inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
