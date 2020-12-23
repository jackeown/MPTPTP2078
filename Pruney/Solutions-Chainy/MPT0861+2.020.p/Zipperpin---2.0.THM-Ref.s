%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rBBJ1VKbtA

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:54 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 (  93 expanded)
%              Number of leaves         :   17 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  410 ( 978 expanded)
%              Number of equality atoms :   47 ( 131 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X6 ) @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_mcart_1 @ X14 )
        = X16 )
      | ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X15 @ ( k1_tarski @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_mcart_1])).

thf('5',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_D @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('9',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) )
     => ( ! [D: $i,E: $i] :
            ( A
           != ( k4_tarski @ D @ E ) )
        | ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11
       != ( k4_tarski @ X9 @ X10 ) )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ X11 ) @ X12 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ X11 ) @ X13 )
      | ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t11_mcart_1])).

thf('11',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X12 @ X13 ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k4_tarski @ X9 @ X10 ) ) @ X13 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ ( k4_tarski @ X9 @ X10 ) ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('12',plain,(
    ! [X21: $i,X23: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X21 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('14',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X12 @ X13 ) )
      | ~ ( r2_hidden @ X10 @ X13 )
      | ~ ( r2_hidden @ X9 @ X12 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ ( k2_tarski @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    r2_hidden @ ( k4_tarski @ sk_D @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_D ) @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf(t16_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_mcart_1 @ X17 )
        = X20 )
      | ( ( k2_mcart_1 @ X17 )
        = X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ ( k2_tarski @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_mcart_1])).

thf('18',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ sk_D @ ( k1_mcart_1 @ sk_A ) ) )
      = sk_B )
    | ( ( k2_mcart_1 @ ( k4_tarski @ sk_D @ ( k1_mcart_1 @ sk_A ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X21: $i,X23: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X21 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('20',plain,(
    ! [X21: $i,X23: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X21 @ X23 ) )
      = X23 ) ),
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
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D ),
    inference('sup-',[status(thm)],['3','4'])).

thf('25',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( sk_D != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
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
     != sk_D ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rBBJ1VKbtA
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:04:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 50 iterations in 0.023s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(t17_mcart_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( r2_hidden @
% 0.19/0.48         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.19/0.48       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.19/0.48         ( ( k2_mcart_1 @ A ) = ( D ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48        ( ( r2_hidden @
% 0.19/0.48            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.19/0.48          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.19/0.48            ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t17_mcart_1])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      ((r2_hidden @ sk_A @ 
% 0.19/0.48        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t10_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.19/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.19/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.48         ((r2_hidden @ (k2_mcart_1 @ X6) @ X8)
% 0.19/0.48          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.19/0.48  thf('2', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      ((r2_hidden @ sk_A @ 
% 0.19/0.48        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t13_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.19/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.19/0.48         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.48         (((k2_mcart_1 @ X14) = (X16))
% 0.19/0.48          | ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X15 @ (k1_tarski @ X16))))),
% 0.19/0.48      inference('cnf', [status(esa)], [t13_mcart_1])).
% 0.19/0.48  thf('5', plain, (((k2_mcart_1 @ sk_A) = (sk_D))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf('6', plain, ((r2_hidden @ sk_D @ (k1_tarski @ sk_D))),
% 0.19/0.48      inference('demod', [status(thm)], ['2', '5'])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      ((r2_hidden @ sk_A @ 
% 0.19/0.48        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.48         ((r2_hidden @ (k1_mcart_1 @ X6) @ X7)
% 0.19/0.48          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf(t11_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.19/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) =>
% 0.19/0.48       ( ( ![D:$i,E:$i]: ( ( A ) != ( k4_tarski @ D @ E ) ) ) | 
% 0.19/0.48         ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.48         (((X11) != (k4_tarski @ X9 @ X10))
% 0.19/0.48          | ~ (r2_hidden @ (k1_mcart_1 @ X11) @ X12)
% 0.19/0.48          | ~ (r2_hidden @ (k2_mcart_1 @ X11) @ X13)
% 0.19/0.48          | (r2_hidden @ X11 @ (k2_zfmisc_1 @ X12 @ X13)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t11_mcart_1])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.19/0.48         ((r2_hidden @ (k4_tarski @ X9 @ X10) @ (k2_zfmisc_1 @ X12 @ X13))
% 0.19/0.48          | ~ (r2_hidden @ (k2_mcart_1 @ (k4_tarski @ X9 @ X10)) @ X13)
% 0.19/0.48          | ~ (r2_hidden @ (k1_mcart_1 @ (k4_tarski @ X9 @ X10)) @ X12))),
% 0.19/0.48      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.48  thf(t7_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.19/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X21 : $i, X23 : $i]: ((k2_mcart_1 @ (k4_tarski @ X21 @ X23)) = (X23))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X21 : $i, X22 : $i]: ((k1_mcart_1 @ (k4_tarski @ X21 @ X22)) = (X21))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.19/0.48         ((r2_hidden @ (k4_tarski @ X9 @ X10) @ (k2_zfmisc_1 @ X12 @ X13))
% 0.19/0.48          | ~ (r2_hidden @ X10 @ X13)
% 0.19/0.48          | ~ (r2_hidden @ X9 @ X12))),
% 0.19/0.48      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X1 @ X0)
% 0.19/0.48          | (r2_hidden @ (k4_tarski @ X1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.19/0.48             (k2_zfmisc_1 @ X0 @ (k2_tarski @ sk_B @ sk_C))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['9', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      ((r2_hidden @ (k4_tarski @ sk_D @ (k1_mcart_1 @ sk_A)) @ 
% 0.19/0.48        (k2_zfmisc_1 @ (k1_tarski @ sk_D) @ (k2_tarski @ sk_B @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['6', '15'])).
% 0.19/0.48  thf(t16_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.19/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.19/0.48         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.48         (((k2_mcart_1 @ X17) = (X20))
% 0.19/0.48          | ((k2_mcart_1 @ X17) = (X19))
% 0.19/0.48          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ (k2_tarski @ X19 @ X20))))),
% 0.19/0.48      inference('cnf', [status(esa)], [t16_mcart_1])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      ((((k2_mcart_1 @ (k4_tarski @ sk_D @ (k1_mcart_1 @ sk_A))) = (sk_B))
% 0.19/0.48        | ((k2_mcart_1 @ (k4_tarski @ sk_D @ (k1_mcart_1 @ sk_A))) = (sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X21 : $i, X23 : $i]: ((k2_mcart_1 @ (k4_tarski @ X21 @ X23)) = (X23))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X21 : $i, X23 : $i]: ((k2_mcart_1 @ (k4_tarski @ X21 @ X23)) = (X23))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      ((((k1_mcart_1 @ sk_A) = (sk_B)) | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.19/0.48      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.19/0.48         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.19/0.48      inference('split', [status(esa)], ['22'])).
% 0.19/0.48  thf('24', plain, (((k2_mcart_1 @ sk_A) = (sk_D))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.19/0.48         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.19/0.48      inference('split', [status(esa)], ['25'])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      ((((sk_D) != (sk_D))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['24', '26'])).
% 0.19/0.48  thf('28', plain, ((((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.19/0.48      inference('split', [status(esa)], ['22'])).
% 0.19/0.48  thf('30', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['28', '29'])).
% 0.19/0.48  thf('31', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['23', '30'])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.19/0.48         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.19/0.48      inference('split', [status(esa)], ['25'])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.19/0.48      inference('split', [status(esa)], ['25'])).
% 0.19/0.48  thf('34', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['28', '33'])).
% 0.19/0.48  thf('35', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['32', '34'])).
% 0.19/0.48  thf('36', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['21', '31', '35'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.34/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
