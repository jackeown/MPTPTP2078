%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FE5p8AUCxU

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  64 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  303 ( 550 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t25_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_setfam_1 @ C @ ( k2_tarski @ A @ B ) )
     => ! [D: $i] :
          ~ ( ( r2_hidden @ D @ C )
            & ~ ( r1_tarski @ D @ A )
            & ~ ( r1_tarski @ D @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_setfam_1 @ C @ ( k2_tarski @ A @ B ) )
       => ! [D: $i] :
            ~ ( ( r2_hidden @ D @ C )
              & ~ ( r1_tarski @ D @ A )
              & ~ ( r1_tarski @ D @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_D_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_setfam_1 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( sk_D @ X14 @ X15 ) )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ~ ( r1_setfam_1 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r1_setfam_1 @ sk_C_1 @ X0 )
      | ( r1_tarski @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_setfam_1 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ ( sk_D @ X14 @ X15 ) @ X15 )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ~ ( r1_setfam_1 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X12 @ X12 @ X13 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ~ ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_B @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,
    ( ( ( sk_D @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_A )
    | ( ( sk_D @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_A )
    | ( ( sk_D @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,
    ( ( ( sk_D @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_B )
    | ( ( sk_D @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_A ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r1_tarski @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('20',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_B )
    | ( ( sk_D @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( r1_tarski @ sk_D_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_D @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = sk_A ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_D_1 @ sk_A ),
    inference(demod,[status(thm)],['5','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FE5p8AUCxU
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 46 iterations in 0.027s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(t25_setfam_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r1_setfam_1 @ C @ ( k2_tarski @ A @ B ) ) =>
% 0.21/0.50       ( ![D:$i]:
% 0.21/0.50         ( ~( ( r2_hidden @ D @ C ) & ( ~( r1_tarski @ D @ A ) ) & 
% 0.21/0.50              ( ~( r1_tarski @ D @ B ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( r1_setfam_1 @ C @ ( k2_tarski @ A @ B ) ) =>
% 0.21/0.50          ( ![D:$i]:
% 0.21/0.50            ( ~( ( r2_hidden @ D @ C ) & ( ~( r1_tarski @ D @ A ) ) & 
% 0.21/0.50                 ( ~( r1_tarski @ D @ B ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t25_setfam_1])).
% 0.21/0.50  thf('0', plain, (~ (r1_tarski @ sk_D_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, ((r1_setfam_1 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('2', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d2_setfam_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.50              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         ((r1_tarski @ X14 @ (sk_D @ X14 @ X15))
% 0.21/0.50          | ~ (r2_hidden @ X14 @ X16)
% 0.21/0.50          | ~ (r1_setfam_1 @ X16 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r1_setfam_1 @ sk_C_1 @ X0)
% 0.21/0.50          | (r1_tarski @ sk_D_1 @ (sk_D @ sk_D_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      ((r1_tarski @ sk_D_1 @ (sk_D @ sk_D_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.50  thf(d1_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.50       ( ![E:$i]:
% 0.21/0.50         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.50           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_1, axiom,
% 0.21/0.50    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.50     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.50       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.21/0.50          | ((X1) = (X2))
% 0.21/0.50          | ((X1) = (X3))
% 0.21/0.50          | ((X1) = (X4)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.50  thf('7', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain, ((r1_setfam_1 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_D @ X14 @ X15) @ X15)
% 0.21/0.50          | ~ (r2_hidden @ X14 @ X16)
% 0.21/0.50          | ~ (r1_setfam_1 @ X16 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.21/0.50          | (r2_hidden @ (sk_D @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.21/0.50             (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      ((r2_hidden @ (sk_D @ sk_D_1 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.21/0.50        (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.50  thf(t70_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i]:
% 0.21/0.50         ((k1_enumset1 @ X12 @ X12 @ X13) = (k2_tarski @ X12 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.50  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.50  thf(zf_stmt_3, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.50       ( ![E:$i]:
% 0.21/0.50         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.50          | ~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.21/0.50          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.50         (~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.21/0.50          | ~ (r2_hidden @ X10 @ (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.50          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (~ (zip_tseitin_0 @ (sk_D @ sk_D_1 @ (k2_tarski @ sk_A @ sk_B)) @ sk_B @ 
% 0.21/0.50          sk_A @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      ((((sk_D @ sk_D_1 @ (k2_tarski @ sk_A @ sk_B)) = (sk_A))
% 0.21/0.50        | ((sk_D @ sk_D_1 @ (k2_tarski @ sk_A @ sk_B)) = (sk_A))
% 0.21/0.50        | ((sk_D @ sk_D_1 @ (k2_tarski @ sk_A @ sk_B)) = (sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((((sk_D @ sk_D_1 @ (k2_tarski @ sk_A @ sk_B)) = (sk_B))
% 0.21/0.50        | ((sk_D @ sk_D_1 @ (k2_tarski @ sk_A @ sk_B)) = (sk_A)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((r1_tarski @ sk_D_1 @ (sk_D @ sk_D_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (((r1_tarski @ sk_D_1 @ sk_B)
% 0.21/0.50        | ((sk_D @ sk_D_1 @ (k2_tarski @ sk_A @ sk_B)) = (sk_A)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('21', plain, (~ (r1_tarski @ sk_D_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('22', plain, (((sk_D @ sk_D_1 @ (k2_tarski @ sk_A @ sk_B)) = (sk_A))),
% 0.21/0.50      inference('clc', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain, ((r1_tarski @ sk_D_1 @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['5', '22'])).
% 0.21/0.50  thf('24', plain, ($false), inference('demod', [status(thm)], ['0', '23'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
