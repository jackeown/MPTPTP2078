%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EM9m2gC7Op

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 107 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  471 (1360 expanded)
%              Number of equality atoms :   68 ( 212 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

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
     != sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_E )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ X5 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('4',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) )
     => ( ! [D: $i,E: $i] :
            ( A
           != ( k4_tarski @ D @ E ) )
        | ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10
       != ( k4_tarski @ X8 @ X9 ) )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ X10 ) @ X12 )
      | ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t11_mcart_1])).

thf('7',plain,(
    ! [X8: $i,X9: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k4_tarski @ X8 @ X9 ) ) @ X12 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ ( k4_tarski @ X8 @ X9 ) ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('8',plain,(
    ! [X17: $i,X19: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X17 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('10',plain,(
    ! [X8: $i,X9: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ~ ( r2_hidden @ X9 @ X12 )
      | ~ ( r2_hidden @ X8 @ X11 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ ( k2_tarski @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf(t16_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_mcart_1 @ X13 )
        = X16 )
      | ( ( k2_mcart_1 @ X13 )
        = X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_mcart_1])).

thf('14',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) )
      = sk_B )
    | ( ( k2_mcart_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X17: $i,X19: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X17 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('16',plain,(
    ! [X17: $i,X19: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X17 @ X19 ) )
      = X19 ) ),
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
     != sk_D ) ),
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
     != sk_D ) ),
    inference(split,[status(esa)],['18'])).

thf('21',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_mcart_1 @ X13 )
        = X16 )
      | ( ( k2_mcart_1 @ X13 )
        = X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_mcart_1])).

thf('25',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_D )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_E ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_E )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(split,[status(esa)],['21'])).

thf('27',plain,
    ( ( ( sk_E != sk_E )
      | ( ( k2_mcart_1 @ sk_A )
        = sk_D ) )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['18'])).

thf('30',plain,
    ( ( sk_D != sk_D )
   <= ( ( ( k2_mcart_1 @ sk_A )
       != sk_E )
      & ( ( k2_mcart_1 @ sk_A )
       != sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_D )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_E ) ),
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
     != sk_D ) ),
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
     != sk_D )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['35'])).

thf('40',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','38','39','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EM9m2gC7Op
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:00:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 72 iterations in 0.036s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.47  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.47  thf(t19_mcart_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47     ( ( r2_hidden @
% 0.20/0.47         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) =>
% 0.20/0.47       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.20/0.47         ( ( ( k2_mcart_1 @ A ) = ( D ) ) | ( ( k2_mcart_1 @ A ) = ( E ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47        ( ( r2_hidden @
% 0.20/0.47            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) =>
% 0.20/0.47          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.20/0.47            ( ( ( k2_mcart_1 @ A ) = ( D ) ) | ( ( k2_mcart_1 @ A ) = ( E ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t19_mcart_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_E)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (~ (((k2_mcart_1 @ sk_A) = (sk_E))) | ~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((r2_hidden @ sk_A @ 
% 0.20/0.47        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k2_tarski @ sk_D @ sk_E)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t10_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.47       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.47         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.47         ((r2_hidden @ (k1_mcart_1 @ X5) @ X6)
% 0.20/0.47          | ~ (r2_hidden @ X5 @ (k2_zfmisc_1 @ X6 @ X7)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf(t11_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.47         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) =>
% 0.20/0.47       ( ( ![D:$i,E:$i]: ( ( A ) != ( k4_tarski @ D @ E ) ) ) | 
% 0.20/0.47         ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         (((X10) != (k4_tarski @ X8 @ X9))
% 0.20/0.47          | ~ (r2_hidden @ (k1_mcart_1 @ X10) @ X11)
% 0.20/0.47          | ~ (r2_hidden @ (k2_mcart_1 @ X10) @ X12)
% 0.20/0.47          | (r2_hidden @ X10 @ (k2_zfmisc_1 @ X11 @ X12)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t11_mcart_1])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         ((r2_hidden @ (k4_tarski @ X8 @ X9) @ (k2_zfmisc_1 @ X11 @ X12))
% 0.20/0.47          | ~ (r2_hidden @ (k2_mcart_1 @ (k4_tarski @ X8 @ X9)) @ X12)
% 0.20/0.47          | ~ (r2_hidden @ (k1_mcart_1 @ (k4_tarski @ X8 @ X9)) @ X11))),
% 0.20/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.47  thf(t7_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.47       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X17 : $i, X19 : $i]: ((k2_mcart_1 @ (k4_tarski @ X17 @ X19)) = (X19))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X17 : $i, X18 : $i]: ((k1_mcart_1 @ (k4_tarski @ X17 @ X18)) = (X17))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         ((r2_hidden @ (k4_tarski @ X8 @ X9) @ (k2_zfmisc_1 @ X11 @ X12))
% 0.20/0.47          | ~ (r2_hidden @ X9 @ X12)
% 0.20/0.47          | ~ (r2_hidden @ X8 @ X11))),
% 0.20/0.47      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X1 @ X0)
% 0.20/0.47          | (r2_hidden @ (k4_tarski @ X1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.47             (k2_zfmisc_1 @ X0 @ (k2_tarski @ sk_B @ sk_C))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((r2_hidden @ (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.47        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k2_tarski @ sk_B @ sk_C)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '11'])).
% 0.20/0.47  thf(t16_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.47       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.47         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.47         (((k2_mcart_1 @ X13) = (X16))
% 0.20/0.47          | ((k2_mcart_1 @ X13) = (X15))
% 0.20/0.47          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ (k2_tarski @ X15 @ X16))))),
% 0.20/0.47      inference('cnf', [status(esa)], [t16_mcart_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      ((((k2_mcart_1 @ (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A)))
% 0.20/0.47          = (sk_B))
% 0.20/0.47        | ((k2_mcart_1 @ 
% 0.20/0.47            (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A))) = (
% 0.20/0.47            sk_C)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X17 : $i, X19 : $i]: ((k2_mcart_1 @ (k4_tarski @ X17 @ X19)) = (X19))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X17 : $i, X19 : $i]: ((k2_mcart_1 @ (k4_tarski @ X17 @ X19)) = (X19))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      ((((k1_mcart_1 @ sk_A) = (sk_B)) | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.20/0.47         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.20/0.47      inference('split', [status(esa)], ['18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.47      inference('split', [status(esa)], ['18'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_E)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_E)))),
% 0.20/0.47      inference('split', [status(esa)], ['21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      ((r2_hidden @ sk_A @ 
% 0.20/0.47        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k2_tarski @ sk_D @ sk_E)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.47         (((k2_mcart_1 @ X13) = (X16))
% 0.20/0.47          | ((k2_mcart_1 @ X13) = (X15))
% 0.20/0.47          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ (k2_tarski @ X15 @ X16))))),
% 0.20/0.47      inference('cnf', [status(esa)], [t16_mcart_1])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      ((((k2_mcart_1 @ sk_A) = (sk_D)) | ((k2_mcart_1 @ sk_A) = (sk_E)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      ((((k2_mcart_1 @ sk_A) != (sk_E)))
% 0.20/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))))),
% 0.20/0.47      inference('split', [status(esa)], ['21'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (((((sk_E) != (sk_E)) | ((k2_mcart_1 @ sk_A) = (sk_D))))
% 0.20/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      ((((k2_mcart_1 @ sk_A) = (sk_D))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.20/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.20/0.47      inference('split', [status(esa)], ['18'])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      ((((sk_D) != (sk_D)))
% 0.20/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))) & 
% 0.20/0.47             ~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      ((((k2_mcart_1 @ sk_A) = (sk_D))) | (((k2_mcart_1 @ sk_A) = (sk_E)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.47  thf('32', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['20', '22', '31'])).
% 0.20/0.47  thf('33', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['19', '32'])).
% 0.20/0.47  thf('34', plain, (((k1_mcart_1 @ sk_A) = (sk_C))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['17', '33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.20/0.47         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.20/0.47      inference('split', [status(esa)], ['35'])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      ((((sk_C) != (sk_C))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['34', '36'])).
% 0.20/0.47  thf('38', plain, ((((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (~ (((k2_mcart_1 @ sk_A) = (sk_D))) | ~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.47      inference('split', [status(esa)], ['35'])).
% 0.20/0.47  thf('40', plain, ($false),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['1', '38', '39', '31'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
