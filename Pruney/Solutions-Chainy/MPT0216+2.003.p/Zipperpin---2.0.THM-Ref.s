%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F2QsrODdNs

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:58 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   39 (  51 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  235 ( 360 expanded)
%              Number of equality atoms :   30 (  49 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t9_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ B @ C ) )
     => ( B = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k1_tarski @ A )
          = ( k2_tarski @ B @ C ) )
       => ( B = C ) ) ),
    inference('cnf.neg',[status(esa)],[t9_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X9 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X2 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X2 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    r2_hidden @ sk_C_1 @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('20',plain,(
    sk_C_1 = sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F2QsrODdNs
% 0.14/0.36  % Computer   : n013.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:06:25 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.47  % Solved by: fo/fo7.sh
% 0.23/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.47  % done 104 iterations in 0.033s
% 0.23/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.47  % SZS output start Refutation
% 0.23/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.23/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.23/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.47  thf(t9_zfmisc_1, conjecture,
% 0.23/0.47    (![A:$i,B:$i,C:$i]:
% 0.23/0.47     ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( B ) = ( C ) ) ))).
% 0.23/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.47        ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( B ) = ( C ) ) ) )),
% 0.23/0.47    inference('cnf.neg', [status(esa)], [t9_zfmisc_1])).
% 0.23/0.47  thf('0', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C_1))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf(t70_enumset1, axiom,
% 0.23/0.47    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.23/0.47  thf('1', plain,
% 0.23/0.47      (![X18 : $i, X19 : $i]:
% 0.23/0.47         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.23/0.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.23/0.47  thf(d1_enumset1, axiom,
% 0.23/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.23/0.47       ( ![E:$i]:
% 0.23/0.47         ( ( r2_hidden @ E @ D ) <=>
% 0.23/0.47           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.23/0.47  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.23/0.47  thf(zf_stmt_2, axiom,
% 0.23/0.47    (![E:$i,C:$i,B:$i,A:$i]:
% 0.23/0.47     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.23/0.47       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.23/0.47  thf(zf_stmt_3, axiom,
% 0.23/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.23/0.47       ( ![E:$i]:
% 0.23/0.47         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.23/0.47  thf('2', plain,
% 0.23/0.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.47         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.23/0.47          | (r2_hidden @ X5 @ X9)
% 0.23/0.47          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.23/0.47  thf('3', plain,
% 0.23/0.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.47         ((r2_hidden @ X5 @ (k1_enumset1 @ X8 @ X7 @ X6))
% 0.23/0.47          | (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 0.23/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.23/0.47  thf('4', plain,
% 0.23/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.47         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.23/0.47          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.23/0.47      inference('sup+', [status(thm)], ['1', '3'])).
% 0.23/0.47  thf('5', plain,
% 0.23/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.47         (((X1) != (X0)) | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.23/0.47  thf('6', plain,
% 0.23/0.47      (![X0 : $i, X2 : $i, X3 : $i]: ~ (zip_tseitin_0 @ X0 @ X2 @ X3 @ X0)),
% 0.23/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.23/0.47  thf('7', plain,
% 0.23/0.47      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.23/0.47      inference('sup-', [status(thm)], ['4', '6'])).
% 0.23/0.47  thf('8', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C_1))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf(d1_tarski, axiom,
% 0.23/0.47    (![A:$i,B:$i]:
% 0.23/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.23/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.23/0.47  thf('9', plain,
% 0.23/0.47      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.23/0.47         (~ (r2_hidden @ X15 @ X14)
% 0.23/0.47          | ((X15) = (X12))
% 0.23/0.47          | ((X14) != (k1_tarski @ X12)))),
% 0.23/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.23/0.47  thf('10', plain,
% 0.23/0.47      (![X12 : $i, X15 : $i]:
% 0.23/0.47         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.23/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.23/0.47  thf('11', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C_1)) | ((X0) = (sk_A)))),
% 0.23/0.47      inference('sup-', [status(thm)], ['8', '10'])).
% 0.23/0.47  thf('12', plain, (((sk_B) = (sk_A))),
% 0.23/0.47      inference('sup-', [status(thm)], ['7', '11'])).
% 0.23/0.47  thf('13', plain, (((k1_tarski @ sk_B) = (k2_tarski @ sk_B @ sk_C_1))),
% 0.23/0.47      inference('demod', [status(thm)], ['0', '12'])).
% 0.23/0.47  thf('14', plain,
% 0.23/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.47         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.23/0.47          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.23/0.47      inference('sup+', [status(thm)], ['1', '3'])).
% 0.23/0.47  thf('15', plain,
% 0.23/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.47         (((X1) != (X2)) | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.23/0.47  thf('16', plain,
% 0.23/0.47      (![X0 : $i, X2 : $i, X3 : $i]: ~ (zip_tseitin_0 @ X2 @ X2 @ X3 @ X0)),
% 0.23/0.47      inference('simplify', [status(thm)], ['15'])).
% 0.23/0.47  thf('17', plain,
% 0.23/0.47      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.23/0.47      inference('sup-', [status(thm)], ['14', '16'])).
% 0.23/0.47  thf('18', plain, ((r2_hidden @ sk_C_1 @ (k1_tarski @ sk_B))),
% 0.23/0.47      inference('sup+', [status(thm)], ['13', '17'])).
% 0.23/0.47  thf('19', plain,
% 0.23/0.47      (![X12 : $i, X15 : $i]:
% 0.23/0.47         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.23/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.23/0.47  thf('20', plain, (((sk_C_1) = (sk_B))),
% 0.23/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.47  thf('21', plain, (((sk_B) != (sk_C_1))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('22', plain, ($false),
% 0.23/0.47      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.23/0.47  
% 0.23/0.47  % SZS output end Refutation
% 0.23/0.47  
% 0.23/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
