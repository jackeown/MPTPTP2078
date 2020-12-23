%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sqPvbS4cbp

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 128 expanded)
%              Number of leaves         :   17 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  364 (1296 expanded)
%              Number of equality atoms :   46 ( 145 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t15_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_mcart_1])).

thf('0',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k4_tarski @ ( sk_D_1 @ X6 ) @ ( sk_E @ X6 ) )
        = X6 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('5',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('8',plain,
    ( ( k1_mcart_1 @ sk_A )
    = ( sk_D_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('11',plain,(
    ! [X14: $i,X16: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X14 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('12',plain,
    ( ( k2_mcart_1 @ sk_A )
    = ( sk_E @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['9','12'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['17'])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['9','12'])).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('27',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( ( sk_C != sk_C )
      | ( ( k1_mcart_1 @ sk_A )
        = sk_B ) )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('33',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k1_mcart_1 @ sk_A )
       != sk_C )
      & ( ( k1_mcart_1 @ sk_A )
       != sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','19','20','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sqPvbS4cbp
% 0.15/0.34  % Computer   : n008.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 15:04:15 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.34  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 118 iterations in 0.101s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(sk_E_type, type, sk_E: $i > $i).
% 0.21/0.56  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 0.21/0.56  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.56  thf(t15_mcart_1, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.21/0.56       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.56         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.21/0.56          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.56            ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t15_mcart_1])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      ((((k1_mcart_1 @ sk_A) != (sk_C))
% 0.21/0.56        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | 
% 0.21/0.56       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D_2))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D_2))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(l139_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.56          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.56         (((k4_tarski @ (sk_D_1 @ X6) @ (sk_E @ X6)) = (X6))
% 0.21/0.56          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.21/0.56      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.21/0.56  thf('5', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.56  thf('6', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.56  thf(t7_mcart_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.56       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.56  thf('8', plain, (((k1_mcart_1 @ sk_A) = (sk_D_1 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['5', '8'])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['5', '8'])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X14 : $i, X16 : $i]: ((k2_mcart_1 @ (k4_tarski @ X14 @ X16)) = (X16))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.56  thf('12', plain, (((k2_mcart_1 @ sk_A) = (sk_E @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)) = (sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['9', '12'])).
% 0.21/0.56  thf(t106_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.56       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.56         ((r2_hidden @ X11 @ X12)
% 0.21/0.56          | ~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ (k2_zfmisc_1 @ X10 @ X12)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.56          | (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.56  thf('16', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2)),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      ((((k1_mcart_1 @ sk_A) != (sk_B))
% 0.21/0.56        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2))
% 0.21/0.56         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2)))),
% 0.21/0.56      inference('split', [status(esa)], ['17'])).
% 0.21/0.56  thf('19', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.21/0.56       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2))),
% 0.21/0.56      inference('split', [status(esa)], ['17'])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D_2))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)) = (sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['9', '12'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.56         ((r2_hidden @ X9 @ X10)
% 0.21/0.56          | ~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ (k2_zfmisc_1 @ X10 @ X12)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.56          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.56  thf(d2_tarski, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.56       ( ![D:$i]:
% 0.21/0.56         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.56          | ((X4) = (X3))
% 0.21/0.56          | ((X4) = (X0))
% 0.21/0.56          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.21/0.56         (((X4) = (X0))
% 0.21/0.56          | ((X4) = (X3))
% 0.21/0.56          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      ((((k1_mcart_1 @ sk_A) = (sk_B)) | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '27'])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.21/0.56         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (((((sk_C) != (sk_C)) | ((k1_mcart_1 @ sk_A) = (sk_B))))
% 0.21/0.56         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      ((((k1_mcart_1 @ sk_A) = (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.56         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.56      inference('split', [status(esa)], ['17'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      ((((sk_B) != (sk_B)))
% 0.21/0.56         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))) & 
% 0.21/0.56             ~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      ((((k1_mcart_1 @ sk_A) = (sk_B))) | (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.56  thf('35', plain, ($false),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['1', '19', '20', '34'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
