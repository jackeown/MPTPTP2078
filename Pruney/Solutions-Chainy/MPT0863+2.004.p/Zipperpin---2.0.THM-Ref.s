%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NGLwjn0KbY

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (  89 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  471 (1035 expanded)
%              Number of equality atoms :   79 ( 166 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(t19_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( ( ( k2_mcart_1 @ A )
            = D )
          | ( ( k2_mcart_1 @ A )
            = E ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( ( ( k2_mcart_1 @ A )
              = D )
            | ( ( k2_mcart_1 @ A )
              = E ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_mcart_1])).

thf('0',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['4'])).

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
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('9',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_D @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('10',plain,(
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

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ~ ( zip_tseitin_0 @ ( k2_mcart_1 @ sk_A ) @ sk_E_1 @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_D )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_E_1 ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_E_1 )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_E_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( ( sk_E_1 != sk_E_1 )
      | ( ( k2_mcart_1 @ sk_A )
        = sk_D ) )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E_1 ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E_1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('22',plain,
    ( ( sk_D != sk_D )
   <= ( ( ( k2_mcart_1 @ sk_A )
       != sk_E_1 )
      & ( ( k2_mcart_1 @ sk_A )
       != sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_E_1 )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('28',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('30',plain,(
    ~ ( zip_tseitin_0 @ ( k1_mcart_1 @ sk_A ) @ sk_C @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('34',plain,
    ( ( ( sk_C != sk_C )
      | ( ( k1_mcart_1 @ sk_A )
        = sk_B ) )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k1_mcart_1 @ sk_A )
       != sk_C )
      & ( ( k1_mcart_1 @ sk_A )
       != sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','23','24','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NGLwjn0KbY
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 57 iterations in 0.025s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.47  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.47  thf(t19_mcart_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.47     ( ( r2_hidden @
% 0.21/0.47         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) =>
% 0.21/0.47       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.47         ( ( ( k2_mcart_1 @ A ) = ( D ) ) | ( ( k2_mcart_1 @ A ) = ( E ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.47        ( ( r2_hidden @
% 0.21/0.47            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) =>
% 0.21/0.47          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.47            ( ( ( k2_mcart_1 @ A ) = ( D ) ) | ( ( k2_mcart_1 @ A ) = ( E ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t19_mcart_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_E_1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | 
% 0.21/0.47       ~ (((k2_mcart_1 @ sk_A) = (sk_E_1)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.47      inference('split', [status(esa)], ['4'])).
% 0.21/0.47  thf(d1_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.47       ( ![E:$i]:
% 0.21/0.47         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.47           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_1, axiom,
% 0.21/0.47    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.47     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.47       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.47         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.21/0.47          | ((X1) = (X2))
% 0.21/0.47          | ((X1) = (X3))
% 0.21/0.47          | ((X1) = (X4)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      ((r2_hidden @ sk_A @ 
% 0.21/0.47        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k2_tarski @ sk_D @ sk_E_1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t10_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.47       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.47         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.47         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 0.21/0.47          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_D @ sk_E_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf(t70_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X12 @ X12 @ X13) = (k2_tarski @ X12 @ X13))),
% 0.21/0.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.47  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.47  thf(zf_stmt_3, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.47       ( ![E:$i]:
% 0.21/0.47         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.47          | ~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.21/0.47          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.47         (~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.21/0.47          | ~ (r2_hidden @ X10 @ (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.47          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (~ (zip_tseitin_0 @ (k2_mcart_1 @ sk_A) @ sk_E_1 @ sk_D @ sk_D)),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((((k2_mcart_1 @ sk_A) = (sk_D))
% 0.21/0.47        | ((k2_mcart_1 @ sk_A) = (sk_D))
% 0.21/0.47        | ((k2_mcart_1 @ sk_A) = (sk_E_1)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      ((((k2_mcart_1 @ sk_A) = (sk_E_1)) | ((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_E_1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      ((((k2_mcart_1 @ sk_A) != (sk_E_1)))
% 0.21/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E_1))))),
% 0.21/0.47      inference('split', [status(esa)], ['17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (((((sk_E_1) != (sk_E_1)) | ((k2_mcart_1 @ sk_A) = (sk_D))))
% 0.21/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E_1))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((((k2_mcart_1 @ sk_A) = (sk_D)))
% 0.21/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E_1))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.21/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((((sk_D) != (sk_D)))
% 0.21/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E_1))) & 
% 0.21/0.47             ~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      ((((k2_mcart_1 @ sk_A) = (sk_E_1))) | (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.21/0.47       ~ (((k2_mcart_1 @ sk_A) = (sk_E_1)))),
% 0.21/0.47      inference('split', [status(esa)], ['17'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.47         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.21/0.47          | ((X1) = (X2))
% 0.21/0.47          | ((X1) = (X3))
% 0.21/0.47          | ((X1) = (X4)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      ((r2_hidden @ sk_A @ 
% 0.21/0.47        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k2_tarski @ sk_D @ sk_E_1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.47         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 0.21/0.47          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.47          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      (~ (zip_tseitin_0 @ (k1_mcart_1 @ sk_A) @ sk_C @ sk_B @ sk_B)),
% 0.21/0.47      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) = (sk_B))
% 0.21/0.47        | ((k1_mcart_1 @ sk_A) = (sk_B))
% 0.21/0.47        | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['25', '30'])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) = (sk_C)) | ((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.21/0.47         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.47      inference('split', [status(esa)], ['4'])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (((((sk_C) != (sk_C)) | ((k1_mcart_1 @ sk_A) = (sk_B))))
% 0.21/0.47         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) = (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.47         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      ((((sk_B) != (sk_B)))
% 0.21/0.47         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))) & 
% 0.21/0.47             ~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.47  thf('38', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) = (sk_B))) | (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.47  thf('39', plain, ($false),
% 0.21/0.47      inference('sat_resolution*', [status(thm)],
% 0.21/0.47                ['1', '3', '5', '23', '24', '38'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
