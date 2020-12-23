%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2nz0ZQwcIt

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  95 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  451 ( 995 expanded)
%              Number of equality atoms :   49 ( 129 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t17_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( ( k2_mcart_1 @ A )
          = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( ( k2_mcart_1 @ A )
            = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X22 ) @ X24 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_mcart_1 @ X25 )
        = X27 )
      | ~ ( r2_hidden @ X25 @ ( k2_zfmisc_1 @ X26 @ ( k1_tarski @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_mcart_1])).

thf('5',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('9',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X11 )
      | ~ ( r2_hidden @ X6 @ X11 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ( X8
       != ( k4_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X6 @ X11 )
      | ( zip_tseitin_0 @ X7 @ X6 @ ( k4_tarski @ X6 @ X7 ) @ X9 @ X11 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k1_mcart_1 @ sk_A ) @ X1 @ ( k4_tarski @ X1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_tarski @ sk_B @ sk_C ) @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    zip_tseitin_0 @ ( k1_mcart_1 @ sk_A ) @ sk_D_1 @ ( k4_tarski @ sk_D_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['6','12'])).

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

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X14 @ X17 )
      | ( X17
       != ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X16 @ X15 ) )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r2_hidden @ ( k4_tarski @ sk_D_1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_D_1 ) @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf(t16_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_mcart_1 @ X28 )
        = X31 )
      | ( ( k2_mcart_1 @ X28 )
        = X30 )
      | ~ ( r2_hidden @ X28 @ ( k2_zfmisc_1 @ X29 @ ( k2_tarski @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_mcart_1])).

thf('18',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ sk_D_1 @ ( k1_mcart_1 @ sk_A ) ) )
      = sk_B )
    | ( ( k2_mcart_1 @ ( k4_tarski @ sk_D_1 @ ( k1_mcart_1 @ sk_A ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('19',plain,(
    ! [X32: $i,X34: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X32 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('20',plain,(
    ! [X32: $i,X34: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X32 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('21',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('25',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['22'])).

thf('30',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['23','30'])).

thf('32',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['25'])).

thf('33',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['25'])).

thf('34',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['28','33'])).

thf('35',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['32','34'])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','31','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2nz0ZQwcIt
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 80 iterations in 0.091s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.54  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.54  thf(t17_mcart_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( r2_hidden @
% 0.20/0.54         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.20/0.54       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.20/0.54         ( ( k2_mcart_1 @ A ) = ( D ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54        ( ( r2_hidden @
% 0.20/0.54            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.20/0.54          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.20/0.54            ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t17_mcart_1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      ((r2_hidden @ sk_A @ 
% 0.20/0.54        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t10_mcart_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.54       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.54         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.54         ((r2_hidden @ (k2_mcart_1 @ X22) @ X24)
% 0.20/0.54          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.54  thf('2', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      ((r2_hidden @ sk_A @ 
% 0.20/0.54        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t13_mcart_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.20/0.54       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.54         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.54         (((k2_mcart_1 @ X25) = (X27))
% 0.20/0.54          | ~ (r2_hidden @ X25 @ (k2_zfmisc_1 @ X26 @ (k1_tarski @ X27))))),
% 0.20/0.54      inference('cnf', [status(esa)], [t13_mcart_1])).
% 0.20/0.54  thf('5', plain, (((k2_mcart_1 @ sk_A) = (sk_D_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.54  thf('6', plain, ((r2_hidden @ sk_D_1 @ (k1_tarski @ sk_D_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['2', '5'])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      ((r2_hidden @ sk_A @ 
% 0.20/0.54        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.54         ((r2_hidden @ (k1_mcart_1 @ X22) @ X23)
% 0.20/0.54          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf(d2_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.20/0.54       ( ![D:$i]:
% 0.20/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.54           ( ?[E:$i,F:$i]:
% 0.20/0.54             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.54               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_1, axiom,
% 0.20/0.54    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.20/0.54       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.54         ( r2_hidden @ E @ A ) ) ))).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X11)
% 0.20/0.54          | ~ (r2_hidden @ X6 @ X11)
% 0.20/0.54          | ~ (r2_hidden @ X7 @ X9)
% 0.20/0.54          | ((X8) != (k4_tarski @ X6 @ X7)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i, X9 : $i, X11 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X7 @ X9)
% 0.20/0.54          | ~ (r2_hidden @ X6 @ X11)
% 0.20/0.54          | (zip_tseitin_0 @ X7 @ X6 @ (k4_tarski @ X6 @ X7) @ X9 @ X11))),
% 0.20/0.54      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ (k1_mcart_1 @ sk_A) @ X1 @ 
% 0.20/0.54           (k4_tarski @ X1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.54           (k2_tarski @ sk_B @ sk_C) @ X0)
% 0.20/0.54          | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      ((zip_tseitin_0 @ (k1_mcart_1 @ sk_A) @ sk_D_1 @ 
% 0.20/0.54        (k4_tarski @ sk_D_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.54        (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '12'])).
% 0.20/0.54  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_3, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.20/0.54       ( ![D:$i]:
% 0.20/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.54           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         (~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.20/0.54          | (r2_hidden @ X14 @ X17)
% 0.20/0.54          | ((X17) != (k2_zfmisc_1 @ X16 @ X15)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         ((r2_hidden @ X14 @ (k2_zfmisc_1 @ X16 @ X15))
% 0.20/0.54          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16))),
% 0.20/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      ((r2_hidden @ (k4_tarski @ sk_D_1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.54        (k2_zfmisc_1 @ (k1_tarski @ sk_D_1) @ (k2_tarski @ sk_B @ sk_C)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.54  thf(t16_mcart_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.54       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.54         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.54         (((k2_mcart_1 @ X28) = (X31))
% 0.20/0.54          | ((k2_mcart_1 @ X28) = (X30))
% 0.20/0.54          | ~ (r2_hidden @ X28 @ (k2_zfmisc_1 @ X29 @ (k2_tarski @ X30 @ X31))))),
% 0.20/0.54      inference('cnf', [status(esa)], [t16_mcart_1])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      ((((k2_mcart_1 @ (k4_tarski @ sk_D_1 @ (k1_mcart_1 @ sk_A))) = (sk_B))
% 0.20/0.54        | ((k2_mcart_1 @ (k4_tarski @ sk_D_1 @ (k1_mcart_1 @ sk_A))) = (sk_C)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf(t7_mcart_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.54       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X32 : $i, X34 : $i]: ((k2_mcart_1 @ (k4_tarski @ X32 @ X34)) = (X34))),
% 0.20/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X32 : $i, X34 : $i]: ((k2_mcart_1 @ (k4_tarski @ X32 @ X34)) = (X34))),
% 0.20/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      ((((k1_mcart_1 @ sk_A) = (sk_B)) | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.54      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.20/0.54         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.20/0.54      inference('split', [status(esa)], ['22'])).
% 0.20/0.54  thf('24', plain, (((k2_mcart_1 @ sk_A) = (sk_D_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 0.20/0.54         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.20/0.54      inference('split', [status(esa)], ['25'])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      ((((sk_D_1) != (sk_D_1))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['24', '26'])).
% 0.20/0.55  thf('28', plain, ((((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | 
% 0.20/0.55       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.20/0.55      inference('split', [status(esa)], ['22'])).
% 0.20/0.55  thf('30', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['28', '29'])).
% 0.20/0.55  thf('31', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['23', '30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.20/0.55         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.20/0.55      inference('split', [status(esa)], ['25'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.20/0.55       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.20/0.55      inference('split', [status(esa)], ['25'])).
% 0.20/0.55  thf('34', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['28', '33'])).
% 0.20/0.55  thf('35', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['32', '34'])).
% 0.20/0.55  thf('36', plain, ($false),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['21', '31', '35'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
