%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RF6nJnDJhN

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  78 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  405 ( 751 expanded)
%              Number of equality atoms :   60 ( 109 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( X7 = X8 )
      | ( X7 = X9 )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( ( ( k2_mcart_1 @ A )
              = C )
            | ( ( k2_mcart_1 @ A )
              = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_mcart_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X31 ) @ X32 )
      | ~ ( r2_hidden @ X31 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
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
    ~ ( zip_tseitin_0 @ ( k1_mcart_1 @ sk_A ) @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['13'])).

thf('16',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( X7 = X8 )
      | ( X7 = X9 )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('20',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X31 ) @ X33 )
      | ~ ( r2_hidden @ X31 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('21',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('23',plain,(
    ~ ( zip_tseitin_0 @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_C ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['16'])).

thf('27',plain,
    ( ( ( sk_D_1 != sk_D_1 )
      | ( ( k2_mcart_1 @ sk_A )
        = sk_C ) )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['13'])).

thf('30',plain,
    ( ( sk_C != sk_C )
   <= ( ( ( k2_mcart_1 @ sk_A )
       != sk_D_1 )
      & ( ( k2_mcart_1 @ sk_A )
       != sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['15','17','31'])).

thf('33',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['14','32'])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RF6nJnDJhN
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:59:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 98 iterations in 0.039s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(d1_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.50       ( ![E:$i]:
% 0.21/0.50         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.50           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, axiom,
% 0.21/0.50    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.50     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.50       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.21/0.50          | ((X7) = (X8))
% 0.21/0.50          | ((X7) = (X9))
% 0.21/0.50          | ((X7) = (X10)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t18_mcart_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( r2_hidden @
% 0.21/0.50         A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.21/0.50       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.50         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_1, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50        ( ( r2_hidden @
% 0.21/0.50            A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.21/0.50          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.50            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t18_mcart_1])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((r2_hidden @ sk_A @ 
% 0.21/0.50        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.50  thf(t10_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.50       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.50         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.50         ((r2_hidden @ (k1_mcart_1 @ X31) @ X32)
% 0.21/0.50          | ~ (r2_hidden @ X31 @ (k2_zfmisc_1 @ X32 @ X33)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.50  thf('3', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf(t69_enumset1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.50  thf('4', plain, (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.50  thf(t70_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X19 : $i, X20 : $i]:
% 0.21/0.50         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.21/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.50  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.50  thf(zf_stmt_3, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.50       ( ![E:$i]:
% 0.21/0.50         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X16 @ X15)
% 0.21/0.50          | ~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.21/0.50          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.50         (~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.21/0.50          | ~ (r2_hidden @ X16 @ (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.50          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.21/0.50          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (~ (zip_tseitin_0 @ (k1_mcart_1 @ sk_A) @ sk_B @ sk_B @ sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      ((((k1_mcart_1 @ sk_A) = (sk_B))
% 0.21/0.50        | ((k1_mcart_1 @ sk_A) = (sk_B))
% 0.21/0.50        | ((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '10'])).
% 0.21/0.50  thf('12', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.21/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.50         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.50      inference('split', [status(esa)], ['13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.50      inference('split', [status(esa)], ['13'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.21/0.50       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.21/0.50      inference('split', [status(esa)], ['16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.21/0.50          | ((X7) = (X8))
% 0.21/0.50          | ((X7) = (X9))
% 0.21/0.50          | ((X7) = (X10)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((r2_hidden @ sk_A @ 
% 0.21/0.50        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.50         ((r2_hidden @ (k2_mcart_1 @ X31) @ X33)
% 0.21/0.50          | ~ (r2_hidden @ X31 @ (k2_zfmisc_1 @ X32 @ X33)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.50          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (~ (zip_tseitin_0 @ (k2_mcart_1 @ sk_A) @ sk_D_1 @ sk_C @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      ((((k2_mcart_1 @ sk_A) = (sk_C))
% 0.21/0.50        | ((k2_mcart_1 @ sk_A) = (sk_C))
% 0.21/0.50        | ((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((((k2_mcart_1 @ sk_A) = (sk_D_1)) | ((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 0.21/0.50         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.21/0.50      inference('split', [status(esa)], ['16'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (((((sk_D_1) != (sk_D_1)) | ((k2_mcart_1 @ sk_A) = (sk_C))))
% 0.21/0.50         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((((k2_mcart_1 @ sk_A) = (sk_C)))
% 0.21/0.50         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.21/0.50         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.50      inference('split', [status(esa)], ['13'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      ((((sk_C) != (sk_C)))
% 0.21/0.50         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))) & 
% 0.21/0.50             ~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((((k2_mcart_1 @ sk_A) = (sk_C))) | (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.50  thf('32', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['15', '17', '31'])).
% 0.21/0.50  thf('33', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['14', '32'])).
% 0.21/0.50  thf('34', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['12', '33'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
