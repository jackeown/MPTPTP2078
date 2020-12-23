%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9eKCn3sc8Z

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 109 expanded)
%              Number of leaves         :   20 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  515 (1380 expanded)
%              Number of equality atoms :   70 ( 210 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
     != sk_E_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_E_2 )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D_1 @ sk_E_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('4',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X10 )
      | ~ ( r2_hidden @ X5 @ X10 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ( X7
       != ( k4_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X5 @ X10 )
      | ( zip_tseitin_0 @ X6 @ X5 @ ( k4_tarski @ X5 @ X6 ) @ X8 @ X10 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k1_mcart_1 @ sk_A ) @ X1 @ ( k4_tarski @ X1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_tarski @ sk_B @ sk_C ) @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    zip_tseitin_0 @ ( k1_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) @ ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X13 @ X16 )
      | ( X16
       != ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X15 @ X14 ) )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t16_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_mcart_1 @ X24 )
        = X27 )
      | ( ( k2_mcart_1 @ X24 )
        = X26 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X25 @ ( k2_tarski @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_mcart_1])).

thf('14',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) )
      = sk_B )
    | ( ( k2_mcart_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('15',plain,(
    ! [X28: $i,X30: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X28 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('16',plain,(
    ! [X28: $i,X30: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X28 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('17',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('21',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E_2 ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D_1 @ sk_E_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_mcart_1 @ X24 )
        = X27 )
      | ( ( k2_mcart_1 @ X24 )
        = X26 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X25 @ ( k2_tarski @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_mcart_1])).

thf('25',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_E_2 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_E_2 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E_2 ) ),
    inference(split,[status(esa)],['21'])).

thf('27',plain,
    ( ( ( sk_E_2 != sk_E_2 )
      | ( ( k2_mcart_1 @ sk_A )
        = sk_D_1 ) )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E_2 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E_2 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('30',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( ( ( k2_mcart_1 @ sk_A )
       != sk_E_2 )
      & ( ( k2_mcart_1 @ sk_A )
       != sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_E_2 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['20','22','31'])).

thf('33',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['19','32'])).

thf('34',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_C ),
    inference('simplify_reflect-',[status(thm)],['17','33'])).

thf('35',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( sk_C != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_C ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['35'])).

thf('40',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','38','39','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9eKCn3sc8Z
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 116 iterations in 0.055s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.51  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.21/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(t19_mcart_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.51     ( ( r2_hidden @
% 0.21/0.51         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) =>
% 0.21/0.51       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.51         ( ( ( k2_mcart_1 @ A ) = ( D ) ) | ( ( k2_mcart_1 @ A ) = ( E ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.51        ( ( r2_hidden @
% 0.21/0.51            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) =>
% 0.21/0.51          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.51            ( ( ( k2_mcart_1 @ A ) = ( D ) ) | ( ( k2_mcart_1 @ A ) = ( E ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t19_mcart_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_E_2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (~ (((k2_mcart_1 @ sk_A) = (sk_E_2))) | 
% 0.21/0.51       ~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((r2_hidden @ sk_A @ 
% 0.21/0.51        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ 
% 0.21/0.51         (k2_tarski @ sk_D_1 @ sk_E_2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t10_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.51       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.51         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.51         ((r2_hidden @ (k1_mcart_1 @ X21) @ X22)
% 0.21/0.51          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf(d2_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.51       ( ![D:$i]:
% 0.21/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.51           ( ?[E:$i,F:$i]:
% 0.21/0.51             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.51               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_1, axiom,
% 0.21/0.51    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.21/0.51     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.21/0.51       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.51         ( r2_hidden @ E @ A ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.51         ((zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X10)
% 0.21/0.51          | ~ (r2_hidden @ X5 @ X10)
% 0.21/0.51          | ~ (r2_hidden @ X6 @ X8)
% 0.21/0.51          | ((X7) != (k4_tarski @ X5 @ X6)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i, X8 : $i, X10 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X6 @ X8)
% 0.21/0.51          | ~ (r2_hidden @ X5 @ X10)
% 0.21/0.51          | (zip_tseitin_0 @ X6 @ X5 @ (k4_tarski @ X5 @ X6) @ X8 @ X10))),
% 0.21/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((zip_tseitin_0 @ (k1_mcart_1 @ sk_A) @ X1 @ 
% 0.21/0.51           (k4_tarski @ X1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51           (k2_tarski @ sk_B @ sk_C) @ X0)
% 0.21/0.51          | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      ((zip_tseitin_0 @ (k1_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A) @ 
% 0.21/0.51        (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51        (k2_tarski @ sk_B @ sk_C) @ (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '8'])).
% 0.21/0.51  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.21/0.51  thf(zf_stmt_3, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.51       ( ![D:$i]:
% 0.21/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.51           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         (~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15)
% 0.21/0.51          | (r2_hidden @ X13 @ X16)
% 0.21/0.51          | ((X16) != (k2_zfmisc_1 @ X15 @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         ((r2_hidden @ X13 @ (k2_zfmisc_1 @ X15 @ X14))
% 0.21/0.51          | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X15))),
% 0.21/0.51      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((r2_hidden @ (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.51        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k2_tarski @ sk_B @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.51  thf(t16_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.21/0.51       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.51         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.51         (((k2_mcart_1 @ X24) = (X27))
% 0.21/0.51          | ((k2_mcart_1 @ X24) = (X26))
% 0.21/0.51          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X25 @ (k2_tarski @ X26 @ X27))))),
% 0.21/0.51      inference('cnf', [status(esa)], [t16_mcart_1])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      ((((k2_mcart_1 @ (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A)))
% 0.21/0.51          = (sk_B))
% 0.21/0.51        | ((k2_mcart_1 @ 
% 0.21/0.51            (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A))) = (
% 0.21/0.51            sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf(t7_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.51       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X28 : $i, X30 : $i]: ((k2_mcart_1 @ (k4_tarski @ X28 @ X30)) = (X30))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X28 : $i, X30 : $i]: ((k2_mcart_1 @ (k4_tarski @ X28 @ X30)) = (X30))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      ((((k1_mcart_1 @ sk_A) = (sk_B)) | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.51         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.21/0.51       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.21/0.51      inference('split', [status(esa)], ['18'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_E_2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.21/0.51       ~ (((k2_mcart_1 @ sk_A) = (sk_E_2)))),
% 0.21/0.51      inference('split', [status(esa)], ['21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      ((r2_hidden @ sk_A @ 
% 0.21/0.51        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ 
% 0.21/0.51         (k2_tarski @ sk_D_1 @ sk_E_2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.51         (((k2_mcart_1 @ X24) = (X27))
% 0.21/0.51          | ((k2_mcart_1 @ X24) = (X26))
% 0.21/0.51          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X25 @ (k2_tarski @ X26 @ X27))))),
% 0.21/0.51      inference('cnf', [status(esa)], [t16_mcart_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      ((((k2_mcart_1 @ sk_A) = (sk_D_1)) | ((k2_mcart_1 @ sk_A) = (sk_E_2)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      ((((k2_mcart_1 @ sk_A) != (sk_E_2)))
% 0.21/0.51         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E_2))))),
% 0.21/0.51      inference('split', [status(esa)], ['21'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (((((sk_E_2) != (sk_E_2)) | ((k2_mcart_1 @ sk_A) = (sk_D_1))))
% 0.21/0.51         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E_2))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      ((((k2_mcart_1 @ sk_A) = (sk_D_1)))
% 0.21/0.51         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E_2))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 0.21/0.51         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.21/0.51      inference('split', [status(esa)], ['18'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      ((((sk_D_1) != (sk_D_1)))
% 0.21/0.51         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E_2))) & 
% 0.21/0.51             ~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((((k2_mcart_1 @ sk_A) = (sk_D_1))) | (((k2_mcart_1 @ sk_A) = (sk_E_2)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.51  thf('32', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['20', '22', '31'])).
% 0.21/0.51  thf('33', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['19', '32'])).
% 0.21/0.51  thf('34', plain, (((k1_mcart_1 @ sk_A) = (sk_C))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['17', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.21/0.51         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.51      inference('split', [status(esa)], ['35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      ((((sk_C) != (sk_C))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '36'])).
% 0.21/0.51  thf('38', plain, ((((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))) | 
% 0.21/0.51       ~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['35'])).
% 0.21/0.51  thf('40', plain, ($false),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['1', '38', '39', '31'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
