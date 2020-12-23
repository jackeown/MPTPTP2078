%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vEzqSlN29r

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:00 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  220 ( 229 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t12_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( X19 = X16 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vEzqSlN29r
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:21:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.35/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.58  % Solved by: fo/fo7.sh
% 0.35/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.58  % done 279 iterations in 0.126s
% 0.35/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.58  % SZS output start Refutation
% 0.35/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.35/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.35/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.58  thf(t12_zfmisc_1, conjecture,
% 0.35/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.35/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.58    (~( ![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )),
% 0.35/0.58    inference('cnf.neg', [status(esa)], [t12_zfmisc_1])).
% 0.35/0.58  thf('0', plain,
% 0.35/0.58      (~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf(t70_enumset1, axiom,
% 0.35/0.58    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.35/0.58  thf('1', plain,
% 0.35/0.58      (![X22 : $i, X23 : $i]:
% 0.35/0.58         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.35/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.35/0.58  thf(d1_enumset1, axiom,
% 0.35/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.35/0.58       ( ![E:$i]:
% 0.35/0.58         ( ( r2_hidden @ E @ D ) <=>
% 0.35/0.58           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.35/0.58  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.35/0.58  thf(zf_stmt_2, axiom,
% 0.35/0.58    (![E:$i,C:$i,B:$i,A:$i]:
% 0.35/0.58     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.35/0.58       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.35/0.58  thf(zf_stmt_3, axiom,
% 0.35/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.35/0.58       ( ![E:$i]:
% 0.35/0.58         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.35/0.58  thf('2', plain,
% 0.35/0.58      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.35/0.58         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.35/0.58          | (r2_hidden @ X9 @ X13)
% 0.35/0.58          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.58  thf('3', plain,
% 0.35/0.58      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.58         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.35/0.58          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.35/0.58      inference('simplify', [status(thm)], ['2'])).
% 0.35/0.58  thf('4', plain,
% 0.35/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.58         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.35/0.58          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.35/0.58      inference('sup+', [status(thm)], ['1', '3'])).
% 0.35/0.58  thf('5', plain,
% 0.35/0.58      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.35/0.58         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.58  thf('6', plain,
% 0.35/0.58      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.35/0.58      inference('simplify', [status(thm)], ['5'])).
% 0.35/0.58  thf('7', plain,
% 0.35/0.58      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.35/0.58      inference('sup-', [status(thm)], ['4', '6'])).
% 0.35/0.58  thf(d3_tarski, axiom,
% 0.35/0.58    (![A:$i,B:$i]:
% 0.35/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.35/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.35/0.58  thf('8', plain,
% 0.35/0.58      (![X1 : $i, X3 : $i]:
% 0.35/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.35/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.58  thf(d1_tarski, axiom,
% 0.35/0.58    (![A:$i,B:$i]:
% 0.35/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.35/0.58  thf('9', plain,
% 0.35/0.58      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.35/0.58         (~ (r2_hidden @ X19 @ X18)
% 0.35/0.58          | ((X19) = (X16))
% 0.35/0.58          | ((X18) != (k1_tarski @ X16)))),
% 0.35/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.58  thf('10', plain,
% 0.35/0.58      (![X16 : $i, X19 : $i]:
% 0.35/0.58         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.35/0.58      inference('simplify', [status(thm)], ['9'])).
% 0.35/0.58  thf('11', plain,
% 0.35/0.58      (![X0 : $i, X1 : $i]:
% 0.35/0.58         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.35/0.58          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['8', '10'])).
% 0.35/0.58  thf('12', plain,
% 0.35/0.58      (![X1 : $i, X3 : $i]:
% 0.35/0.58         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.35/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.58  thf('13', plain,
% 0.35/0.58      (![X0 : $i, X1 : $i]:
% 0.35/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.35/0.58          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.35/0.58          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.35/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.58  thf('14', plain,
% 0.35/0.58      (![X0 : $i, X1 : $i]:
% 0.35/0.58         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.35/0.58      inference('simplify', [status(thm)], ['13'])).
% 0.35/0.58  thf('15', plain,
% 0.35/0.58      (![X0 : $i, X1 : $i]:
% 0.35/0.58         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.35/0.58      inference('sup-', [status(thm)], ['7', '14'])).
% 0.35/0.58  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.35/0.58  
% 0.35/0.58  % SZS output end Refutation
% 0.35/0.58  
% 0.35/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
