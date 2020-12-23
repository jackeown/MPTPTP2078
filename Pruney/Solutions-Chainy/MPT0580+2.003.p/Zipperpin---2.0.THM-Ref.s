%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yVY271IFR9

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 (  97 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  469 ( 754 expanded)
%              Number of equality atoms :   38 (  64 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_relat_1_type,type,(
    v3_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t184_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v3_relat_1 @ A )
      <=> ! [B: $i] :
            ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) )
           => ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( v3_relat_1 @ A )
        <=> ! [B: $i] :
              ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) )
             => ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t184_relat_1])).

thf('0',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X21: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ sk_A ) )
      | ( X21 = k1_xboole_0 )
      | ( v3_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v3_relat_1 @ sk_A )
   <= ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(d15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v3_relat_1 @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ) )).

thf('6',plain,(
    ! [X20: $i] :
      ( ~ ( v3_relat_1 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d15_relat_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v3_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k1_tarski @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X19 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( sk_B = X0 )
        | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k1_tarski @ X0 ) ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( r2_hidden @ sk_B @ k1_xboole_0 )
      | ~ ( v3_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( r2_hidden @ sk_B @ k1_xboole_0 )
      | ~ ( v3_relat_1 @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X18 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ~ ( r2_hidden @ X18 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ~ ( v3_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['14','21'])).

thf('23',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v3_relat_1 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('28',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ ( k2_tarski @ X12 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,
    ( ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ sk_A ) ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) )
          = k1_xboole_0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ k1_xboole_0 @ X0 )
        | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_tarski @ k1_xboole_0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ( v3_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d15_relat_1])).

thf('41',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v3_relat_1 @ sk_A ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v3_relat_1 @ sk_A )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v3_relat_1 @ sk_A )
   <= ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ~ ! [X21: $i] :
          ( ( X21 = k1_xboole_0 )
          | ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','26','27','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yVY271IFR9
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:47:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 157 iterations in 0.045s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(v3_relat_1_type, type, v3_relat_1: $i > $o).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(t184_relat_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ( v3_relat_1 @ A ) <=>
% 0.22/0.50         ( ![B:$i]:
% 0.22/0.50           ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.22/0.50             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( v1_relat_1 @ A ) =>
% 0.22/0.50          ( ( v3_relat_1 @ A ) <=>
% 0.22/0.50            ( ![B:$i]:
% 0.22/0.50              ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.22/0.50                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t184_relat_1])).
% 0.22/0.50  thf('0', plain, ((((sk_B) != (k1_xboole_0)) | ~ (v3_relat_1 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain, (~ (((sk_B) = (k1_xboole_0))) | ~ ((v3_relat_1 @ sk_A))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)) | ~ (v3_relat_1 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | ~ ((v3_relat_1 @ sk_A))),
% 0.22/0.50      inference('split', [status(esa)], ['2'])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X21 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X21 @ (k2_relat_1 @ sk_A))
% 0.22/0.50          | ((X21) = (k1_xboole_0))
% 0.22/0.50          | (v3_relat_1 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('5', plain, (((v3_relat_1 @ sk_A)) <= (((v3_relat_1 @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['4'])).
% 0.22/0.50  thf(d15_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ( v3_relat_1 @ A ) <=>
% 0.22/0.50         ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X20 : $i]:
% 0.22/0.50         (~ (v3_relat_1 @ X20)
% 0.22/0.50          | (r1_tarski @ (k2_relat_1 @ X20) @ (k1_tarski @ k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X20))),
% 0.22/0.50      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.22/0.50  thf(l32_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X7 : $i, X9 : $i]:
% 0.22/0.50         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v3_relat_1 @ X0)
% 0.22/0.50          | ((k4_xboole_0 @ (k2_relat_1 @ X0) @ (k1_tarski @ k1_xboole_0))
% 0.22/0.50              = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.22/0.50         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.22/0.50      inference('split', [status(esa)], ['2'])).
% 0.22/0.50  thf(t64_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.22/0.50       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.22/0.50         ((r2_hidden @ X16 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X19)))
% 0.22/0.50          | ((X16) = (X19))
% 0.22/0.50          | ~ (r2_hidden @ X16 @ X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          (((sk_B) = (X0))
% 0.22/0.50           | (r2_hidden @ sk_B @ 
% 0.22/0.50              (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k1_tarski @ X0)))))
% 0.22/0.50         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      ((((r2_hidden @ sk_B @ k1_xboole_0)
% 0.22/0.50         | ~ (v3_relat_1 @ sk_A)
% 0.22/0.50         | ~ (v1_relat_1 @ sk_A)
% 0.22/0.50         | ((sk_B) = (k1_xboole_0))))
% 0.22/0.50         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['8', '11'])).
% 0.22/0.50  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((((r2_hidden @ sk_B @ k1_xboole_0)
% 0.22/0.50         | ~ (v3_relat_1 @ sk_A)
% 0.22/0.50         | ((sk_B) = (k1_xboole_0))))
% 0.22/0.50         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf(d10_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.50  thf('16', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.22/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X7 : $i, X9 : $i]:
% 0.22/0.50         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.50  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.50         (((X16) != (X18))
% 0.22/0.50          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X18))))),
% 0.22/0.50      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X17 : $i, X18 : $i]:
% 0.22/0.50         ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X18)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.50  thf('21', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.50      inference('sup-', [status(thm)], ['18', '20'])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (((((sk_B) = (k1_xboole_0)) | ~ (v3_relat_1 @ sk_A)))
% 0.22/0.50         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.22/0.50      inference('clc', [status(thm)], ['14', '21'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      ((((sk_B) = (k1_xboole_0)))
% 0.22/0.50         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '22'])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      ((((sk_B) != (sk_B)))
% 0.22/0.50         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.22/0.50             ((v3_relat_1 @ sk_A)) & 
% 0.22/0.50             ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (~ ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | 
% 0.22/0.50       ~ ((v3_relat_1 @ sk_A)) | (((sk_B) = (k1_xboole_0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      ((![X21 : $i]:
% 0.22/0.50          (((X21) = (k1_xboole_0)) | ~ (r2_hidden @ X21 @ (k2_relat_1 @ sk_A)))) | 
% 0.22/0.50       ((v3_relat_1 @ sk_A))),
% 0.22/0.50      inference('split', [status(esa)], ['4'])).
% 0.22/0.50  thf('28', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.22/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.50  thf(t69_enumset1, axiom,
% 0.22/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.22/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.50  thf(t38_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.22/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.50         ((r2_hidden @ X12 @ X13)
% 0.22/0.50          | ~ (r1_tarski @ (k2_tarski @ X12 @ X14) @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['28', '31'])).
% 0.22/0.50  thf(d3_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X1 : $i, X3 : $i]:
% 0.22/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      ((![X21 : $i]:
% 0.22/0.50          (((X21) = (k1_xboole_0)) | ~ (r2_hidden @ X21 @ (k2_relat_1 @ sk_A))))
% 0.22/0.50         <= ((![X21 : $i]:
% 0.22/0.50                (((X21) = (k1_xboole_0))
% 0.22/0.50                 | ~ (r2_hidden @ X21 @ (k2_relat_1 @ sk_A)))))),
% 0.22/0.50      inference('split', [status(esa)], ['4'])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.22/0.50           | ((sk_C @ X0 @ (k2_relat_1 @ sk_A)) = (k1_xboole_0))))
% 0.22/0.50         <= ((![X21 : $i]:
% 0.22/0.50                (((X21) = (k1_xboole_0))
% 0.22/0.50                 | ~ (r2_hidden @ X21 @ (k2_relat_1 @ sk_A)))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X1 : $i, X3 : $i]:
% 0.22/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          (~ (r2_hidden @ k1_xboole_0 @ X0)
% 0.22/0.50           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.22/0.50           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)))
% 0.22/0.50         <= ((![X21 : $i]:
% 0.22/0.50                (((X21) = (k1_xboole_0))
% 0.22/0.50                 | ~ (r2_hidden @ X21 @ (k2_relat_1 @ sk_A)))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.22/0.50           | ~ (r2_hidden @ k1_xboole_0 @ X0)))
% 0.22/0.50         <= ((![X21 : $i]:
% 0.22/0.50                (((X21) = (k1_xboole_0))
% 0.22/0.50                 | ~ (r2_hidden @ X21 @ (k2_relat_1 @ sk_A)))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_tarski @ k1_xboole_0)))
% 0.22/0.50         <= ((![X21 : $i]:
% 0.22/0.50                (((X21) = (k1_xboole_0))
% 0.22/0.50                 | ~ (r2_hidden @ X21 @ (k2_relat_1 @ sk_A)))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['32', '38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X20 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k2_relat_1 @ X20) @ (k1_tarski @ k1_xboole_0))
% 0.22/0.50          | (v3_relat_1 @ X20)
% 0.22/0.50          | ~ (v1_relat_1 @ X20))),
% 0.22/0.50      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (((~ (v1_relat_1 @ sk_A) | (v3_relat_1 @ sk_A)))
% 0.22/0.50         <= ((![X21 : $i]:
% 0.22/0.50                (((X21) = (k1_xboole_0))
% 0.22/0.50                 | ~ (r2_hidden @ X21 @ (k2_relat_1 @ sk_A)))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.50  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      (((v3_relat_1 @ sk_A))
% 0.22/0.50         <= ((![X21 : $i]:
% 0.22/0.50                (((X21) = (k1_xboole_0))
% 0.22/0.50                 | ~ (r2_hidden @ X21 @ (k2_relat_1 @ sk_A)))))),
% 0.22/0.50      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.50  thf('44', plain, ((~ (v3_relat_1 @ sk_A)) <= (~ ((v3_relat_1 @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      (~
% 0.22/0.50       (![X21 : $i]:
% 0.22/0.50          (((X21) = (k1_xboole_0)) | ~ (r2_hidden @ X21 @ (k2_relat_1 @ sk_A)))) | 
% 0.22/0.50       ((v3_relat_1 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.50  thf('46', plain, ($false),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['1', '3', '26', '27', '45'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
