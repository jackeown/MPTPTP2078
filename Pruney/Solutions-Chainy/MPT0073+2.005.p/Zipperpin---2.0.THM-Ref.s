%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vV35GyXz3K

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:39 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 117 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  327 ( 894 expanded)
%              Number of equality atoms :   29 ( 123 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( r1_xboole_0 @ X16 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('6',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_A )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('8',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ k1_xboole_0 )
   <= ( ~ ( r1_xboole_0 @ sk_A @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('10',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r1_xboole_0 @ sk_A @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('13',plain,(
    r1_xboole_0 @ sk_A @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','11','12'])).

thf('14',plain,(
    r1_xboole_0 @ sk_A @ sk_A ),
    inference(simpl_trail,[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

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

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ X13 )
      | ( zip_tseitin_0 @ X14 @ X13 @ X12 )
      | ( zip_tseitin_1 @ X14 @ X13 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_1 @ ( sk_B @ X0 ) @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_B @ X0 ) @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ sk_A ) @ sk_A @ sk_A )
    | ( zip_tseitin_1 @ ( sk_B @ sk_A ) @ sk_A @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('23',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','11'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ sk_A ) @ sk_A @ sk_A )
    | ( zip_tseitin_1 @ ( sk_B @ sk_A ) @ sk_A @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( zip_tseitin_1 @ X9 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('27',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ sk_A ) @ sk_A @ sk_A )
    | ~ ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('29',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','29'])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['22','23'])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vV35GyXz3K
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 39 iterations in 0.028s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.19/0.47  thf(t7_xboole_0, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (![X15 : $i]:
% 0.19/0.47         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X15) @ X15))),
% 0.19/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.47  thf(t66_xboole_1, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.19/0.47       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.19/0.47          ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t66_xboole_1])).
% 0.19/0.47  thf('1', plain, (((r1_xboole_0 @ sk_A @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (((r1_xboole_0 @ sk_A @ sk_A)) <= (((r1_xboole_0 @ sk_A @ sk_A)))),
% 0.19/0.47      inference('split', [status(esa)], ['1'])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      ((((sk_A) != (k1_xboole_0)) | ~ (r1_xboole_0 @ sk_A @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (~ (((sk_A) = (k1_xboole_0))) | ~ ((r1_xboole_0 @ sk_A @ sk_A))),
% 0.19/0.47      inference('split', [status(esa)], ['3'])).
% 0.19/0.47  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.47  thf('5', plain, (![X16 : $i]: (r1_xboole_0 @ X16 @ k1_xboole_0)),
% 0.19/0.47      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.47  thf('6', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('split', [status(esa)], ['1'])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      ((~ (r1_xboole_0 @ sk_A @ sk_A)) <= (~ ((r1_xboole_0 @ sk_A @ sk_A)))),
% 0.19/0.47      inference('split', [status(esa)], ['3'])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      ((~ (r1_xboole_0 @ sk_A @ k1_xboole_0))
% 0.19/0.47         <= (~ ((r1_xboole_0 @ sk_A @ sk_A)) & (((sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf('9', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('split', [status(esa)], ['1'])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      ((~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.19/0.47         <= (~ ((r1_xboole_0 @ sk_A @ sk_A)) & (((sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (((r1_xboole_0 @ sk_A @ sk_A)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['5', '10'])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (((r1_xboole_0 @ sk_A @ sk_A)) | (((sk_A) = (k1_xboole_0)))),
% 0.19/0.47      inference('split', [status(esa)], ['1'])).
% 0.19/0.47  thf('13', plain, (((r1_xboole_0 @ sk_A @ sk_A))),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 0.19/0.47  thf('14', plain, ((r1_xboole_0 @ sk_A @ sk_A)),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['2', '13'])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X15 : $i]:
% 0.19/0.47         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X15) @ X15))),
% 0.19/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.47  thf(d3_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.19/0.47       ( ![D:$i]:
% 0.19/0.47         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.47           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.47          | (r2_hidden @ X0 @ X2)
% 0.19/0.47          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.19/0.47         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.48      inference('simplify', [status(thm)], ['16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0))
% 0.19/0.48          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '17'])).
% 0.19/0.48  thf(t5_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ~( ( ~( ( ~( r2_hidden @ C @ A ) ) & ( r2_hidden @ C @ B ) ) ) & 
% 0.19/0.48          ( ~( ( ~( r2_hidden @ C @ B ) ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.48          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ B ) ) ))).
% 0.19/0.48  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.19/0.48  thf(zf_stmt_2, axiom,
% 0.19/0.48    (![C:$i,B:$i,A:$i]:
% 0.19/0.48     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.19/0.48       ( ( r2_hidden @ C @ A ) & ( ~( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.19/0.48  thf(zf_stmt_4, axiom,
% 0.19/0.48    (![C:$i,B:$i,A:$i]:
% 0.19/0.48     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.19/0.48       ( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_5, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ~( ( r1_xboole_0 @ A @ B ) & 
% 0.19/0.48          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & 
% 0.19/0.48          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.19/0.48          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.48         (~ (r1_xboole_0 @ X12 @ X13)
% 0.19/0.48          | (zip_tseitin_0 @ X14 @ X13 @ X12)
% 0.19/0.48          | (zip_tseitin_1 @ X14 @ X13 @ X12)
% 0.19/0.48          | ~ (r2_hidden @ X14 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0))
% 0.19/0.48          | (zip_tseitin_1 @ (sk_B @ X0) @ X0 @ X1)
% 0.19/0.48          | (zip_tseitin_0 @ (sk_B @ X0) @ X0 @ X1)
% 0.19/0.48          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (((zip_tseitin_0 @ (sk_B @ sk_A) @ sk_A @ sk_A)
% 0.19/0.48        | (zip_tseitin_1 @ (sk_B @ sk_A) @ sk_A @ sk_A)
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['14', '20'])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['3'])).
% 0.19/0.48  thf('23', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['4', '11'])).
% 0.19/0.48  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (((zip_tseitin_0 @ (sk_B @ sk_A) @ sk_A @ sk_A)
% 0.19/0.48        | (zip_tseitin_1 @ (sk_B @ sk_A) @ sk_A @ sk_A))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['21', '24'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X9 @ X11) | ~ (zip_tseitin_1 @ X9 @ X11 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (((zip_tseitin_0 @ (sk_B @ sk_A) @ sk_A @ sk_A)
% 0.19/0.48        | ~ (r2_hidden @ (sk_B @ sk_A) @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X6 @ X8) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.19/0.48  thf('29', plain, (~ (r2_hidden @ (sk_B @ sk_A) @ sk_A)),
% 0.19/0.48      inference('clc', [status(thm)], ['27', '28'])).
% 0.19/0.48  thf('30', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '29'])).
% 0.19/0.48  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('32', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
