%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GHmDC81Sk4

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 105 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  406 (1052 expanded)
%              Number of equality atoms :   53 ( 133 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

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

thf(t17_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( ( k2_mcart_1 @ A )
          = D ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( ( k2_mcart_1 @ A )
            = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_mcart_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X28 ) @ X29 )
      | ~ ( r2_hidden @ X28 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
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

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ~ ( zip_tseitin_0 @ ( k1_mcart_1 @ sk_A ) @ sk_C @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X28 ) @ X30 )
      | ~ ( r2_hidden @ X28 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('15',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( r2_hidden @ X24 @ ( k4_xboole_0 @ X25 @ ( k1_tarski @ X27 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_hidden @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ sk_A )
        = X0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ sk_A )
        = X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('24',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('27',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['25','26'])).

thf('28',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['12','27'])).

thf('29',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['29'])).

thf('32',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['25','31'])).

thf('33',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['30','32'])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','28','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GHmDC81Sk4
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:46:59 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.36  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 154 iterations in 0.058s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.52  thf(d1_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.52       ( ![E:$i]:
% 0.22/0.52         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.52           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, axiom,
% 0.22/0.52    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.52     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.52       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.52         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.22/0.52          | ((X7) = (X8))
% 0.22/0.52          | ((X7) = (X9))
% 0.22/0.52          | ((X7) = (X10)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t17_mcart_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( r2_hidden @
% 0.22/0.52         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.22/0.52       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.22/0.52         ( ( k2_mcart_1 @ A ) = ( D ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_1, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52        ( ( r2_hidden @
% 0.22/0.52            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.22/0.52          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.22/0.52            ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t17_mcart_1])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      ((r2_hidden @ sk_A @ 
% 0.22/0.52        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.52  thf(t10_mcart_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.22/0.52       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.52         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.52         ((r2_hidden @ (k1_mcart_1 @ X28) @ X29)
% 0.22/0.52          | ~ (r2_hidden @ X28 @ (k2_zfmisc_1 @ X29 @ X30)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf(t70_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X19 : $i, X20 : $i]:
% 0.22/0.52         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.22/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.52  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.52  thf(zf_stmt_3, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.52       ( ![E:$i]:
% 0.22/0.52         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X16 @ X15)
% 0.22/0.52          | ~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.22/0.52          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.22/0.52         (~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.22/0.52          | ~ (r2_hidden @ X16 @ (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.52          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '6'])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (~ (zip_tseitin_0 @ (k1_mcart_1 @ sk_A) @ sk_C @ sk_B @ sk_B)),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      ((((k1_mcart_1 @ sk_A) = (sk_B))
% 0.22/0.52        | ((k1_mcart_1 @ sk_A) = (sk_B))
% 0.22/0.52        | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      ((((k1_mcart_1 @ sk_A) = (sk_C)) | ((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.22/0.52         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.22/0.52      inference('split', [status(esa)], ['11'])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      ((r2_hidden @ sk_A @ 
% 0.22/0.52        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.52         ((r2_hidden @ (k2_mcart_1 @ X28) @ X30)
% 0.22/0.52          | ~ (r2_hidden @ X28 @ (k2_zfmisc_1 @ X29 @ X30)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.52  thf('15', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf(t64_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.22/0.52       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X24 : $i, X25 : $i, X27 : $i]:
% 0.22/0.52         ((r2_hidden @ X24 @ (k4_xboole_0 @ X25 @ (k1_tarski @ X27)))
% 0.22/0.52          | ((X24) = (X27))
% 0.22/0.52          | ~ (r2_hidden @ X24 @ X25))),
% 0.22/0.52      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_mcart_1 @ sk_A) = (X0))
% 0.22/0.52          | (r2_hidden @ (k2_mcart_1 @ sk_A) @ 
% 0.22/0.52             (k4_xboole_0 @ (k1_tarski @ sk_D_1) @ (k1_tarski @ X0))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf(d5_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.22/0.52       ( ![D:$i]:
% 0.22/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X4 @ X3)
% 0.22/0.52          | ~ (r2_hidden @ X4 @ X2)
% 0.22/0.52          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X4 @ X2)
% 0.22/0.52          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_mcart_1 @ sk_A) = (X0))
% 0.22/0.52          | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '20'])).
% 0.22/0.52  thf('22', plain, (((k2_mcart_1 @ sk_A) = (sk_D_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['15', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 0.22/0.52         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.22/0.52      inference('split', [status(esa)], ['11'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      ((((sk_D_1) != (sk_D_1))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain, ((((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.22/0.52       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.22/0.52      inference('split', [status(esa)], ['11'])).
% 0.22/0.52  thf('27', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['25', '26'])).
% 0.22/0.52  thf('28', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['12', '27'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.22/0.52         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.22/0.52      inference('split', [status(esa)], ['29'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | 
% 0.22/0.52       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.22/0.52      inference('split', [status(esa)], ['29'])).
% 0.22/0.52  thf('32', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['25', '31'])).
% 0.22/0.52  thf('33', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['30', '32'])).
% 0.22/0.52  thf('34', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['10', '28', '33'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
