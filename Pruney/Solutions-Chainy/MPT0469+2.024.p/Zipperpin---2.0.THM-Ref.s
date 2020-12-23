%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YLqmolyIyg

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:19 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   59 (  99 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  282 ( 539 expanded)
%              Number of equality atoms :   41 (  84 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13
        = ( k1_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X10 ) @ ( sk_D @ X13 @ X10 ) ) @ X10 )
      | ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ~ ( r2_hidden @ X5 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('7',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ X16 @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('12',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('13',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','15'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('17',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('18',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','18'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('20',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','15'])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('31',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['21','31'])).

thf('33',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['19','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('35',plain,(
    $false ),
    inference('sup-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YLqmolyIyg
% 0.15/0.35  % Computer   : n003.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:07:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 293 iterations in 0.122s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.38/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.59  thf(d4_relat_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.38/0.59       ( ![C:$i]:
% 0.38/0.59         ( ( r2_hidden @ C @ B ) <=>
% 0.38/0.59           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.38/0.59  thf('0', plain,
% 0.38/0.59      (![X10 : $i, X13 : $i]:
% 0.38/0.59         (((X13) = (k1_relat_1 @ X10))
% 0.38/0.59          | (r2_hidden @ 
% 0.38/0.59             (k4_tarski @ (sk_C @ X13 @ X10) @ (sk_D @ X13 @ X10)) @ X10)
% 0.38/0.59          | (r2_hidden @ (sk_C @ X13 @ X10) @ X13))),
% 0.38/0.59      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.38/0.59  thf(t113_zfmisc_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.59  thf('1', plain,
% 0.38/0.59      (![X3 : $i, X4 : $i]:
% 0.38/0.59         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['1'])).
% 0.38/0.59  thf(t152_zfmisc_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      (![X5 : $i, X6 : $i]: ~ (r2_hidden @ X5 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.38/0.59      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.38/0.59  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.59  thf('5', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.38/0.59          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['0', '4'])).
% 0.38/0.59  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.59  thf('7', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.59  thf(t7_xboole_0, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.59          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.38/0.59  thf('8', plain,
% 0.38/0.59      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.38/0.59  thf(t19_relat_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ B ) =>
% 0.38/0.59       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 0.38/0.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      (![X15 : $i, X16 : $i]:
% 0.38/0.59         ((r2_hidden @ (sk_C_1 @ X15) @ (k1_relat_1 @ X15))
% 0.38/0.59          | ~ (r2_hidden @ X16 @ (k2_relat_1 @ X15))
% 0.38/0.59          | ~ (v1_relat_1 @ X15))),
% 0.38/0.59      inference('cnf', [status(esa)], [t19_relat_1])).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | (r2_hidden @ (sk_C_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.59  thf('11', plain,
% 0.38/0.59      (((r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)
% 0.38/0.59        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.38/0.59        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['7', '10'])).
% 0.38/0.59  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.38/0.59  thf('12', plain, ((v1_xboole_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.38/0.59  thf('13', plain, ((v1_xboole_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.38/0.59  thf(l13_xboole_0, axiom,
% 0.38/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.59  thf('14', plain,
% 0.38/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.59  thf('15', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.59  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.59      inference('demod', [status(thm)], ['12', '15'])).
% 0.38/0.59  thf(cc1_relat_1, axiom,
% 0.38/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.38/0.59  thf('17', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.38/0.59  thf('18', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.38/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      (((r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)
% 0.38/0.59        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['11', '18'])).
% 0.38/0.59  thf(t60_relat_1, conjecture,
% 0.38/0.59    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.38/0.59     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.38/0.59        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.38/0.59  thf('20', plain,
% 0.38/0.59      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.38/0.59        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.38/0.59         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.38/0.59      inference('split', [status(esa)], ['20'])).
% 0.38/0.59  thf('22', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.59  thf('23', plain,
% 0.38/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.59  thf('24', plain,
% 0.38/0.59      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.38/0.59         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.38/0.59      inference('split', [status(esa)], ['20'])).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      ((![X0 : $i]:
% 0.38/0.59          (((k1_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.38/0.59         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.38/0.59         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['22', '25'])).
% 0.38/0.59  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.59      inference('demod', [status(thm)], ['12', '15'])).
% 0.38/0.59  thf('28', plain,
% 0.38/0.59      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.38/0.59         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.38/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.59  thf('29', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['28'])).
% 0.38/0.59  thf('30', plain,
% 0.38/0.59      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.38/0.59       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.38/0.59      inference('split', [status(esa)], ['20'])).
% 0.38/0.59  thf('31', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.38/0.59      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 0.38/0.59  thf('32', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.38/0.59      inference('simpl_trail', [status(thm)], ['21', '31'])).
% 0.38/0.59  thf('33', plain, ((r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.38/0.59      inference('simplify_reflect-', [status(thm)], ['19', '32'])).
% 0.38/0.59  thf('34', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.59  thf('35', plain, ($false), inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
