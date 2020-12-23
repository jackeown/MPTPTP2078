%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wMZnj8mwWn

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:51 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 241 expanded)
%              Number of leaves         :   19 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :  398 (2223 expanded)
%              Number of equality atoms :   20 ( 140 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_2 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t32_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ~ ( ( r1_tarski @ A @ B )
          & ( A != k1_xboole_0 )
          & ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ~ ( ( r2_hidden @ C @ A )
                  & ! [D: $i] :
                      ( ( v3_ordinal1 @ D )
                     => ( ( r2_hidden @ D @ A )
                       => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v3_ordinal1 @ B )
       => ~ ( ( r1_tarski @ A @ B )
            & ( A != k1_xboole_0 )
            & ! [C: $i] :
                ( ( v3_ordinal1 @ C )
               => ~ ( ( r2_hidden @ C @ A )
                    & ! [D: $i] :
                        ( ( v3_ordinal1 @ D )
                       => ( ( r2_hidden @ D @ A )
                         => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_ordinal1])).

thf('8',plain,(
    ! [X18: $i] :
      ( ( r2_hidden @ ( sk_D @ X18 ) @ sk_A )
      | ~ ( r2_hidden @ X18 @ sk_A )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v3_ordinal1 @ ( sk_C_2 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_C_2 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_2 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_C_2 @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('13',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v3_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('20',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( v3_ordinal1 @ ( sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_ordinal1 @ ( sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ ( sk_D @ ( sk_C_2 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['11','22'])).

thf('24',plain,(
    v3_ordinal1 @ ( sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ( r1_ordinal1 @ X17 @ X16 )
      | ( r2_hidden @ X16 @ X17 )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( sk_C_2 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C_2 @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C_2 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,
    ( ( r1_ordinal1 @ ( sk_C_2 @ sk_A ) @ ( sk_D @ ( sk_C_2 @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ ( sk_D @ ( sk_C_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('32',plain,(
    ! [X18: $i] :
      ( ( v3_ordinal1 @ ( sk_D @ X18 ) )
      | ~ ( r2_hidden @ X18 @ sk_A )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v3_ordinal1 @ ( sk_C_2 @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D @ ( sk_C_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_2 @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D @ ( sk_C_2 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_ordinal1 @ ( sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('37',plain,(
    v3_ordinal1 @ ( sk_D @ ( sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    r1_ordinal1 @ ( sk_C_2 @ sk_A ) @ ( sk_D @ ( sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X18: $i] :
      ( ~ ( r1_ordinal1 @ X18 @ ( sk_D @ X18 ) )
      | ~ ( r2_hidden @ X18 @ sk_A )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_2 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_ordinal1 @ ( sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('42',plain,(
    r2_hidden @ ( sk_D @ ( sk_C_2 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['11','22'])).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_2 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('44',plain,(
    r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['40','41','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wMZnj8mwWn
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:12:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 214 iterations in 0.107s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.38/0.56  thf(sk_D_type, type, sk_D: $i > $i).
% 0.38/0.56  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.38/0.56  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.56  thf(t2_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.38/0.56       ( ( A ) = ( B ) ) ))).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      (![X4 : $i, X5 : $i]:
% 0.38/0.56         (((X5) = (X4))
% 0.38/0.56          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.38/0.56          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.38/0.56      inference('cnf', [status(esa)], [t2_tarski])).
% 0.38/0.56  thf(t113_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      (![X7 : $i, X8 : $i]:
% 0.38/0.56         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['1'])).
% 0.38/0.56  thf(t152_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (![X9 : $i, X10 : $i]: ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.38/0.56      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.38/0.56  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.38/0.56          | ((X0) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['0', '4'])).
% 0.38/0.56  thf(t7_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ~( ( r2_hidden @ A @ B ) & 
% 0.38/0.56          ( ![C:$i]:
% 0.38/0.56            ( ~( ( r2_hidden @ C @ B ) & 
% 0.38/0.56                 ( ![D:$i]:
% 0.38/0.56                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X11 : $i, X12 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X11 @ X12) | (r2_hidden @ (sk_C_2 @ X12) @ X12))),
% 0.38/0.56      inference('cnf', [status(esa)], [t7_tarski])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.56  thf(t32_ordinal1, conjecture,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v3_ordinal1 @ B ) =>
% 0.38/0.56       ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56            ( ![C:$i]:
% 0.38/0.56              ( ( v3_ordinal1 @ C ) =>
% 0.38/0.56                ( ~( ( r2_hidden @ C @ A ) & 
% 0.38/0.56                     ( ![D:$i]:
% 0.38/0.56                       ( ( v3_ordinal1 @ D ) =>
% 0.38/0.56                         ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i]:
% 0.38/0.56        ( ( v3_ordinal1 @ B ) =>
% 0.38/0.56          ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56               ( ![C:$i]:
% 0.38/0.56                 ( ( v3_ordinal1 @ C ) =>
% 0.38/0.56                   ( ~( ( r2_hidden @ C @ A ) & 
% 0.38/0.56                        ( ![D:$i]:
% 0.38/0.56                          ( ( v3_ordinal1 @ D ) =>
% 0.38/0.56                            ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t32_ordinal1])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X18 : $i]:
% 0.38/0.56         ((r2_hidden @ (sk_D @ X18) @ sk_A)
% 0.38/0.56          | ~ (r2_hidden @ X18 @ sk_A)
% 0.38/0.56          | ~ (v3_ordinal1 @ X18))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      ((((sk_A) = (k1_xboole_0))
% 0.38/0.56        | ~ (v3_ordinal1 @ (sk_C_2 @ sk_A))
% 0.38/0.56        | (r2_hidden @ (sk_D @ (sk_C_2 @ sk_A)) @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.56  thf('10', plain, (((sk_A) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      ((~ (v3_ordinal1 @ (sk_C_2 @ sk_A))
% 0.38/0.56        | (r2_hidden @ (sk_D @ (sk_C_2 @ sk_A)) @ sk_A))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.56  thf('13', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d3_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.56          | (r2_hidden @ X0 @ X2)
% 0.38/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      ((((sk_A) = (k1_xboole_0)) | (r2_hidden @ (sk_C_2 @ sk_A) @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['12', '15'])).
% 0.38/0.56  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('18', plain, ((r2_hidden @ (sk_C_2 @ sk_A) @ sk_B)),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.38/0.56  thf(t23_ordinal1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X14 : $i, X15 : $i]:
% 0.38/0.56         ((v3_ordinal1 @ X14)
% 0.38/0.56          | ~ (v3_ordinal1 @ X15)
% 0.38/0.56          | ~ (r2_hidden @ X14 @ X15))),
% 0.38/0.56      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      ((~ (v3_ordinal1 @ sk_B) | (v3_ordinal1 @ (sk_C_2 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.56  thf('21', plain, ((v3_ordinal1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('22', plain, ((v3_ordinal1 @ (sk_C_2 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.38/0.56  thf('23', plain, ((r2_hidden @ (sk_D @ (sk_C_2 @ sk_A)) @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['11', '22'])).
% 0.38/0.56  thf('24', plain, ((v3_ordinal1 @ (sk_C_2 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.38/0.56  thf(t26_ordinal1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v3_ordinal1 @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( v3_ordinal1 @ B ) =>
% 0.38/0.56           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      (![X16 : $i, X17 : $i]:
% 0.38/0.56         (~ (v3_ordinal1 @ X16)
% 0.38/0.56          | (r1_ordinal1 @ X17 @ X16)
% 0.38/0.56          | (r2_hidden @ X16 @ X17)
% 0.38/0.56          | ~ (v3_ordinal1 @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X11 @ X12)
% 0.38/0.56          | ~ (r2_hidden @ X13 @ X12)
% 0.38/0.56          | ~ (r2_hidden @ X13 @ (sk_C_2 @ X12)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t7_tarski])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X1 @ (sk_C_2 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.56      inference('condensation', [status(thm)], ['26'])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v3_ordinal1 @ (sk_C_2 @ X0))
% 0.38/0.56          | (r1_ordinal1 @ (sk_C_2 @ X0) @ X1)
% 0.38/0.56          | ~ (v3_ordinal1 @ X1)
% 0.38/0.56          | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['25', '27'])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.56          | ~ (v3_ordinal1 @ X0)
% 0.38/0.56          | (r1_ordinal1 @ (sk_C_2 @ sk_A) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['24', '28'])).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      (((r1_ordinal1 @ (sk_C_2 @ sk_A) @ (sk_D @ (sk_C_2 @ sk_A)))
% 0.38/0.56        | ~ (v3_ordinal1 @ (sk_D @ (sk_C_2 @ sk_A))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['23', '29'])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      (![X18 : $i]:
% 0.38/0.56         ((v3_ordinal1 @ (sk_D @ X18))
% 0.38/0.56          | ~ (r2_hidden @ X18 @ sk_A)
% 0.38/0.56          | ~ (v3_ordinal1 @ X18))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      ((((sk_A) = (k1_xboole_0))
% 0.38/0.56        | ~ (v3_ordinal1 @ (sk_C_2 @ sk_A))
% 0.38/0.56        | (v3_ordinal1 @ (sk_D @ (sk_C_2 @ sk_A))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.56  thf('34', plain, (((sk_A) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      ((~ (v3_ordinal1 @ (sk_C_2 @ sk_A))
% 0.38/0.56        | (v3_ordinal1 @ (sk_D @ (sk_C_2 @ sk_A))))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.38/0.56  thf('36', plain, ((v3_ordinal1 @ (sk_C_2 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.38/0.56  thf('37', plain, ((v3_ordinal1 @ (sk_D @ (sk_C_2 @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      ((r1_ordinal1 @ (sk_C_2 @ sk_A) @ (sk_D @ (sk_C_2 @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['30', '37'])).
% 0.38/0.56  thf('39', plain,
% 0.38/0.56      (![X18 : $i]:
% 0.38/0.56         (~ (r1_ordinal1 @ X18 @ (sk_D @ X18))
% 0.38/0.56          | ~ (r2_hidden @ X18 @ sk_A)
% 0.38/0.56          | ~ (v3_ordinal1 @ X18))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      ((~ (v3_ordinal1 @ (sk_C_2 @ sk_A))
% 0.38/0.56        | ~ (r2_hidden @ (sk_C_2 @ sk_A) @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.56  thf('41', plain, ((v3_ordinal1 @ (sk_C_2 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.38/0.56  thf('42', plain, ((r2_hidden @ (sk_D @ (sk_C_2 @ sk_A)) @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['11', '22'])).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      (![X11 : $i, X12 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X11 @ X12) | (r2_hidden @ (sk_C_2 @ X12) @ X12))),
% 0.38/0.56      inference('cnf', [status(esa)], [t7_tarski])).
% 0.38/0.56  thf('44', plain, ((r2_hidden @ (sk_C_2 @ sk_A) @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.56  thf('45', plain, ($false),
% 0.38/0.56      inference('demod', [status(thm)], ['40', '41', '44'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
