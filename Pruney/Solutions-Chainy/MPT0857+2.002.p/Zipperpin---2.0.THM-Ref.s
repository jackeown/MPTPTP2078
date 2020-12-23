%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qfZSToQYQ1

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  279 ( 420 expanded)
%              Number of equality atoms :   28 (  38 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
       => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
          & ( ( k2_mcart_1 @ A )
            = C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_mcart_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X18 ) @ X20 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
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

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ~ ( zip_tseitin_0 @ ( k2_mcart_1 @ sk_A ) @ sk_C @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('17',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('19',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('21',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['14','21'])).

thf('23',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qfZSToQYQ1
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:11:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 38 iterations in 0.021s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(d1_enumset1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.48       ( ![E:$i]:
% 0.20/0.48         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.48           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, axiom,
% 0.20/0.48    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.48     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.48       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.20/0.48          | ((X1) = (X2))
% 0.20/0.48          | ((X1) = (X3))
% 0.20/0.48          | ((X1) = (X4)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t13_mcart_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.20/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.48         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.20/0.48          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.48            ( ( k2_mcart_1 @ A ) = ( C ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t13_mcart_1])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k1_tarski @ sk_C)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.48  thf(t10_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.48         ((r2_hidden @ (k2_mcart_1 @ X18) @ X20)
% 0.20/0.48          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.48  thf('3', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf(t69_enumset1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.48  thf('4', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.48  thf(t70_enumset1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.48  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.48  thf(zf_stmt_3, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.48       ( ![E:$i]:
% 0.20/0.48         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.48          | ~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.20/0.48          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.20/0.48         (~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.20/0.48          | ~ (r2_hidden @ X10 @ (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.48          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.48          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (~ (zip_tseitin_0 @ (k2_mcart_1 @ sk_A) @ sk_C @ sk_C @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((((k2_mcart_1 @ sk_A) = (sk_C))
% 0.20/0.48        | ((k2_mcart_1 @ sk_A) = (sk_C))
% 0.20/0.48        | ((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '10'])).
% 0.20/0.48  thf('12', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.20/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.20/0.48        | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.20/0.48         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.20/0.48      inference('split', [status(esa)], ['13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k1_tarski @ sk_C)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.48         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 0.20/0.48          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.48  thf('17', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))
% 0.20/0.48         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)))),
% 0.20/0.48      inference('split', [status(esa)], ['13'])).
% 0.20/0.48  thf('19', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | 
% 0.20/0.48       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.48      inference('split', [status(esa)], ['13'])).
% 0.20/0.48  thf('21', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['14', '21'])).
% 0.20/0.48  thf('23', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['12', '22'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
