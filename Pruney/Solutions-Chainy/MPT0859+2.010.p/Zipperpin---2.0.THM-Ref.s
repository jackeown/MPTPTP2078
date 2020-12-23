%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fJ3Ig3MQGs

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:49 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 (  77 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  363 ( 757 expanded)
%              Number of equality atoms :   41 (  77 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 )
      | ( X6 = X7 )
      | ( X6 = X8 )
      | ( X6 = X9 )
      | ( X6 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_mcart_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X3 @ X4 )
      = ( k1_enumset1 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X12 @ X13 @ X14 @ X15 )
      | ( X16
       != ( k2_enumset1 @ X15 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k2_enumset1 @ X15 @ X14 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ~ ( zip_tseitin_0 @ ( k1_mcart_1 @ sk_A ) @ sk_C @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X19 ) @ X21 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('17',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ) ),
    inference(split,[status(esa)],['13'])).

thf('19',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ) ),
    inference(split,[status(esa)],['13'])).

thf('21',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['14','21'])).

thf('23',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ) ),
    inference(split,[status(esa)],['23'])).

thf('26',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['19','25'])).

thf('27',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['24','26'])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','22','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fJ3Ig3MQGs
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 38 iterations in 0.026s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(d2_enumset1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.48     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.19/0.48       ( ![F:$i]:
% 0.19/0.48         ( ( r2_hidden @ F @ E ) <=>
% 0.19/0.48           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.19/0.48                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, axiom,
% 0.19/0.48    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.19/0.48     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.19/0.48       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.19/0.48         ( ( F ) != ( D ) ) ) ))).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.48         ((zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.19/0.48          | ((X6) = (X7))
% 0.19/0.48          | ((X6) = (X8))
% 0.19/0.48          | ((X6) = (X9))
% 0.19/0.48          | ((X6) = (X10)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t15_mcart_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.19/0.48       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.19/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 0.19/0.48  thf(zf_stmt_1, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.19/0.48          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.19/0.48            ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t15_mcart_1])).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.48  thf(t10_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.19/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.19/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.48         ((r2_hidden @ (k1_mcart_1 @ X19) @ X20)
% 0.19/0.48          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf(t70_enumset1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.48  thf(t71_enumset1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.48         ((k2_enumset1 @ X2 @ X2 @ X3 @ X4) = (k1_enumset1 @ X2 @ X3 @ X4))),
% 0.19/0.48      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.19/0.48  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.19/0.48  thf(zf_stmt_3, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.48     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.19/0.48       ( ![F:$i]:
% 0.19/0.48         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X17 @ X16)
% 0.19/0.48          | ~ (zip_tseitin_0 @ X17 @ X12 @ X13 @ X14 @ X15)
% 0.19/0.48          | ((X16) != (k2_enumset1 @ X15 @ X14 @ X13 @ X12)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 0.19/0.48         (~ (zip_tseitin_0 @ X17 @ X12 @ X13 @ X14 @ X15)
% 0.19/0.48          | ~ (r2_hidden @ X17 @ (k2_enumset1 @ X15 @ X14 @ X13 @ X12)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.19/0.48          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.19/0.48      inference('sup-', [status(thm)], ['5', '7'])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.19/0.48          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['4', '8'])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (~ (zip_tseitin_0 @ (k1_mcart_1 @ sk_A) @ sk_C @ sk_B @ sk_B @ sk_B)),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '9'])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      ((((k1_mcart_1 @ sk_A) = (sk_B))
% 0.19/0.48        | ((k1_mcart_1 @ sk_A) = (sk_B))
% 0.19/0.48        | ((k1_mcart_1 @ sk_A) = (sk_B))
% 0.19/0.48        | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '10'])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      ((((k1_mcart_1 @ sk_A) = (sk_C)) | ((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B))
% 0.19/0.48        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.19/0.48         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.19/0.48      inference('split', [status(esa)], ['13'])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.48         ((r2_hidden @ (k2_mcart_1 @ X19) @ X21)
% 0.19/0.48          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.19/0.48  thf('17', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D)),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))
% 0.19/0.48         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D)))),
% 0.19/0.48      inference('split', [status(esa)], ['13'])).
% 0.19/0.48  thf('19', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))),
% 0.19/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.19/0.48       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))),
% 0.19/0.48      inference('split', [status(esa)], ['13'])).
% 0.19/0.48  thf('21', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['19', '20'])).
% 0.19/0.48  thf('22', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['14', '21'])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      ((((k1_mcart_1 @ sk_A) != (sk_C))
% 0.19/0.48        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.19/0.48         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.19/0.48      inference('split', [status(esa)], ['23'])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | 
% 0.19/0.48       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))),
% 0.19/0.48      inference('split', [status(esa)], ['23'])).
% 0.19/0.48  thf('26', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['19', '25'])).
% 0.19/0.48  thf('27', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['24', '26'])).
% 0.19/0.48  thf('28', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['12', '22', '27'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
