%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EgQF79bV6Y

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  93 expanded)
%              Number of leaves         :   17 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  408 ( 976 expanded)
%              Number of equality atoms :   47 ( 131 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t18_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( ( ( k2_mcart_1 @ A )
              = C )
            | ( ( k2_mcart_1 @ A )
              = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('5',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_mcart_1 @ X10 )
        = X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ ( k1_tarski @ X9 ) @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('8',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(t11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) )
     => ( ! [D: $i,E: $i] :
            ( A
           != ( k4_tarski @ D @ E ) )
        | ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6
       != ( k4_tarski @ X4 @ X5 ) )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ X6 ) @ X8 )
      | ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t11_mcart_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k4_tarski @ X4 @ X5 ) ) @ X8 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ ( k4_tarski @ X4 @ X5 ) ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('12',plain,(
    ! [X16: $i,X18: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X16 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ X5 @ X8 )
      | ~ ( r2_hidden @ X4 @ X7 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    r2_hidden @ ( k4_tarski @ ( k2_mcart_1 @ sk_A ) @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf(t15_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_mcart_1 @ X13 )
        = X12 )
      | ( ( k1_mcart_1 @ X13 )
        = X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ ( k2_tarski @ X14 @ X12 ) @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t15_mcart_1])).

thf('18',plain,
    ( ( ( k1_mcart_1 @ ( k4_tarski @ ( k2_mcart_1 @ sk_A ) @ sk_B ) )
      = sk_C )
    | ( ( k1_mcart_1 @ ( k4_tarski @ ( k2_mcart_1 @ sk_A ) @ sk_B ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('21',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf('25',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( sk_B != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['22'])).

thf('30',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference('sat_resolution*',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference(simpl_trail,[status(thm)],['23','30'])).

thf('32',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['25'])).

thf('33',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['25'])).

thf('34',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['28','33'])).

thf('35',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['32','34'])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','31','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EgQF79bV6Y
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 31 iterations in 0.018s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(t18_mcart_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( r2_hidden @
% 0.21/0.49         A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.21/0.49       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.49         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49        ( ( r2_hidden @
% 0.21/0.49            A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.21/0.49          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.49            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t18_mcart_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((r2_hidden @ sk_A @ 
% 0.21/0.49        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t10_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.49       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.49         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((r2_hidden @ (k2_mcart_1 @ X1) @ X3)
% 0.21/0.49          | ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X2 @ X3)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      ((r2_hidden @ sk_A @ 
% 0.21/0.49        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((r2_hidden @ (k1_mcart_1 @ X1) @ X2)
% 0.21/0.49          | ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X2 @ X3)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.49  thf('5', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      ((r2_hidden @ sk_A @ 
% 0.21/0.49        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t12_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.21/0.49       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.49         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         (((k1_mcart_1 @ X10) = (X9))
% 0.21/0.49          | ~ (r2_hidden @ X10 @ (k2_zfmisc_1 @ (k1_tarski @ X9) @ X11)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.21/0.49  thf('8', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '8'])).
% 0.21/0.49  thf(t11_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.49         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) =>
% 0.21/0.49       ( ( ![D:$i,E:$i]: ( ( A ) != ( k4_tarski @ D @ E ) ) ) | 
% 0.21/0.49         ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.49         (((X6) != (k4_tarski @ X4 @ X5))
% 0.21/0.49          | ~ (r2_hidden @ (k1_mcart_1 @ X6) @ X7)
% 0.21/0.49          | ~ (r2_hidden @ (k2_mcart_1 @ X6) @ X8)
% 0.21/0.49          | (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t11_mcart_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.49         ((r2_hidden @ (k4_tarski @ X4 @ X5) @ (k2_zfmisc_1 @ X7 @ X8))
% 0.21/0.49          | ~ (r2_hidden @ (k2_mcart_1 @ (k4_tarski @ X4 @ X5)) @ X8)
% 0.21/0.49          | ~ (r2_hidden @ (k1_mcart_1 @ (k4_tarski @ X4 @ X5)) @ X7))),
% 0.21/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.49  thf(t7_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.49       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X16 : $i, X18 : $i]: ((k2_mcart_1 @ (k4_tarski @ X16 @ X18)) = (X18))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]: ((k1_mcart_1 @ (k4_tarski @ X16 @ X17)) = (X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.49         ((r2_hidden @ (k4_tarski @ X4 @ X5) @ (k2_zfmisc_1 @ X7 @ X8))
% 0.21/0.49          | ~ (r2_hidden @ X5 @ X8)
% 0.21/0.49          | ~ (r2_hidden @ X4 @ X7))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ 
% 0.21/0.49             (k2_zfmisc_1 @ X0 @ (k1_tarski @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((r2_hidden @ (k4_tarski @ (k2_mcart_1 @ sk_A) @ sk_B) @ 
% 0.21/0.49        (k2_zfmisc_1 @ (k2_tarski @ sk_C @ sk_D) @ (k1_tarski @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '15'])).
% 0.21/0.49  thf(t15_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.21/0.49       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.49         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.49         (((k1_mcart_1 @ X13) = (X12))
% 0.21/0.49          | ((k1_mcart_1 @ X13) = (X14))
% 0.21/0.49          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ (k2_tarski @ X14 @ X12) @ X15)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t15_mcart_1])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((((k1_mcart_1 @ (k4_tarski @ (k2_mcart_1 @ sk_A) @ sk_B)) = (sk_C))
% 0.21/0.49        | ((k1_mcart_1 @ (k4_tarski @ (k2_mcart_1 @ sk_A) @ sk_B)) = (sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]: ((k1_mcart_1 @ (k4_tarski @ X16 @ X17)) = (X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]: ((k1_mcart_1 @ (k4_tarski @ X16 @ X17)) = (X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      ((((k2_mcart_1 @ sk_A) = (sk_C)) | ((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.49      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.21/0.49         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.21/0.49      inference('split', [status(esa)], ['22'])).
% 0.21/0.49  thf('24', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.49         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((((sk_B) != (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['24', '26'])).
% 0.21/0.49  thf('28', plain, ((((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (~ (((k2_mcart_1 @ sk_A) = (sk_D))) | ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['22'])).
% 0.21/0.49  thf('30', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['28', '29'])).
% 0.21/0.49  thf('31', plain, (((k2_mcart_1 @ sk_A) != (sk_D))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['23', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.21/0.49         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.49      inference('split', [status(esa)], ['25'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['25'])).
% 0.21/0.49  thf('34', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['28', '33'])).
% 0.21/0.49  thf('35', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['32', '34'])).
% 0.21/0.49  thf('36', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['21', '31', '35'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
