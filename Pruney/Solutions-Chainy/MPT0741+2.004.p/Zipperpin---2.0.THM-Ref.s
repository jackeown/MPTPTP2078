%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tcXw6j1WLj

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 275 expanded)
%              Number of leaves         :   19 (  86 expanded)
%              Depth                    :   20
%              Number of atoms          :  458 (1859 expanded)
%              Number of equality atoms :    7 (  17 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(cc2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) )
     => ( v3_ordinal1 @ A ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( v3_ordinal1 @ X5 )
      | ~ ( v2_ordinal1 @ X5 )
      | ~ ( v1_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_ordinal1])).

thf(t31_ordinal1,conjecture,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( ( v3_ordinal1 @ B )
            & ( r1_tarski @ B @ A ) ) )
     => ( v3_ordinal1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( ( v3_ordinal1 @ B )
              & ( r1_tarski @ B @ A ) ) )
       => ( v3_ordinal1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t31_ordinal1])).

thf('1',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( v1_ordinal1 @ sk_A )
    | ~ ( v2_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X8: $i] :
      ( ( v1_ordinal1 @ X8 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('4',plain,(
    ! [X17: $i] :
      ( ( r1_tarski @ X17 @ sk_A )
      | ~ ( r2_hidden @ X17 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X8: $i] :
      ( ( v1_ordinal1 @ X8 )
      | ~ ( r1_tarski @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('7',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ( v1_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_ordinal1 @ sk_A ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','8'])).

thf(d3_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v2_ordinal1 @ A )
    <=> ! [B: $i,C: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ( r2_hidden @ C @ A )
            & ~ ( r2_hidden @ B @ C )
            & ( B != C )
            & ~ ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X12: $i] :
      ( ( v2_ordinal1 @ X12 )
      | ( r2_hidden @ ( sk_B_1 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('11',plain,(
    ! [X17: $i] :
      ( ( v3_ordinal1 @ X17 )
      | ~ ( r2_hidden @ X17 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('14',plain,(
    ! [X12: $i] :
      ( ( v2_ordinal1 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('15',plain,(
    ! [X17: $i] :
      ( ( v3_ordinal1 @ X17 )
      | ~ ( r2_hidden @ X17 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','8'])).

thf('18',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ( r1_ordinal1 @ X16 @ X15 )
      | ( r2_hidden @ X15 @ X16 )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('20',plain,(
    ! [X12: $i] :
      ( ( v2_ordinal1 @ X12 )
      | ~ ( r2_hidden @ ( sk_B_1 @ X12 ) @ ( sk_C @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C @ X0 ) @ ( sk_B_1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( sk_B_1 @ X0 ) )
      | ( v2_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) )
    | ( r1_ordinal1 @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','8'])).

thf('24',plain,
    ( ( r1_ordinal1 @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','8'])).

thf('27',plain,(
    r1_ordinal1 @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ~ ( v3_ordinal1 @ X14 )
      | ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_ordinal1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('29',plain,
    ( ( r1_tarski @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('31',plain,
    ( ( r1_tarski @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( r1_tarski @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','31'])).

thf('33',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','8'])).

thf('34',plain,(
    r1_tarski @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['32','33'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('36',plain,
    ( ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( r2_xboole_0 @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('38',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ( r1_ordinal1 @ X16 @ X15 )
      | ( r2_hidden @ X15 @ X16 )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('40',plain,(
    ! [X12: $i] :
      ( ( v2_ordinal1 @ X12 )
      | ~ ( r2_hidden @ ( sk_C @ X12 ) @ ( sk_B_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_B_1 @ X0 ) )
      | ( r1_ordinal1 @ ( sk_B_1 @ X0 ) @ ( sk_C @ X0 ) )
      | ~ ( v3_ordinal1 @ ( sk_C @ X0 ) )
      | ( v2_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v2_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ ( sk_C @ sk_A ) )
    | ( r1_ordinal1 @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('44',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v2_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_ordinal1 @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) )
    | ( v2_ordinal1 @ sk_A ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','8'])).

thf('47',plain,(
    r1_ordinal1 @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ~ ( v3_ordinal1 @ X14 )
      | ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_ordinal1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('49',plain,
    ( ( r1_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_C @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('51',plain,
    ( ( r1_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( r1_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','51'])).

thf('53',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','8'])).

thf('54',plain,(
    r1_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('55',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r2_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('56',plain,(
    ~ ( r2_xboole_0 @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_C @ sk_A )
    = ( sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','56'])).

thf('58',plain,(
    ! [X12: $i] :
      ( ( v2_ordinal1 @ X12 )
      | ( ( sk_B_1 @ X12 )
       != ( sk_C @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('59',plain,
    ( ( ( sk_B_1 @ sk_A )
     != ( sk_B_1 @ sk_A ) )
    | ( v2_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_ordinal1 @ sk_A ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['9','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tcXw6j1WLj
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 101 iterations in 0.061s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.49  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.21/0.49  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.49  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(cc2_ordinal1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) => ( v3_ordinal1 @ A ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X5 : $i]:
% 0.21/0.49         ((v3_ordinal1 @ X5) | ~ (v2_ordinal1 @ X5) | ~ (v1_ordinal1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc2_ordinal1])).
% 0.21/0.49  thf(t31_ordinal1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ![B:$i]:
% 0.21/0.49         ( ( r2_hidden @ B @ A ) =>
% 0.21/0.49           ( ( v3_ordinal1 @ B ) & ( r1_tarski @ B @ A ) ) ) ) =>
% 0.21/0.49       ( v3_ordinal1 @ A ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ![B:$i]:
% 0.21/0.49            ( ( r2_hidden @ B @ A ) =>
% 0.21/0.49              ( ( v3_ordinal1 @ B ) & ( r1_tarski @ B @ A ) ) ) ) =>
% 0.21/0.49          ( v3_ordinal1 @ A ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t31_ordinal1])).
% 0.21/0.49  thf('1', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('2', plain, ((~ (v1_ordinal1 @ sk_A) | ~ (v2_ordinal1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(d2_ordinal1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_ordinal1 @ A ) <=>
% 0.21/0.49       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X8 : $i]: ((v1_ordinal1 @ X8) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X17 : $i]: ((r1_tarski @ X17 @ sk_A) | ~ (r2_hidden @ X17 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((v1_ordinal1 @ sk_A) | (r1_tarski @ (sk_B @ sk_A) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X8 : $i]: ((v1_ordinal1 @ X8) | ~ (r1_tarski @ (sk_B @ X8) @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.21/0.49  thf('7', plain, (((v1_ordinal1 @ sk_A) | (v1_ordinal1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain, ((v1_ordinal1 @ sk_A)),
% 0.21/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.49  thf('9', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '8'])).
% 0.21/0.49  thf(d3_ordinal1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v2_ordinal1 @ A ) <=>
% 0.21/0.49       ( ![B:$i,C:$i]:
% 0.21/0.49         ( ~( ( r2_hidden @ B @ A ) & ( r2_hidden @ C @ A ) & 
% 0.21/0.49              ( ~( r2_hidden @ B @ C ) ) & ( ( B ) != ( C ) ) & 
% 0.21/0.49              ( ~( r2_hidden @ C @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X12 : $i]: ((v2_ordinal1 @ X12) | (r2_hidden @ (sk_B_1 @ X12) @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X17 : $i]: ((v3_ordinal1 @ X17) | ~ (r2_hidden @ X17 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain, (((v2_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain, (((v2_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X12 : $i]: ((v2_ordinal1 @ X12) | (r2_hidden @ (sk_C @ X12) @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X17 : $i]: ((v3_ordinal1 @ X17) | ~ (r2_hidden @ X17 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain, (((v2_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_C @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '8'])).
% 0.21/0.49  thf('18', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf(t26_ordinal1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.49           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X15)
% 0.21/0.49          | (r1_ordinal1 @ X16 @ X15)
% 0.21/0.49          | (r2_hidden @ X15 @ X16)
% 0.21/0.49          | ~ (v3_ordinal1 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X12 : $i]:
% 0.21/0.49         ((v2_ordinal1 @ X12) | ~ (r2_hidden @ (sk_B_1 @ X12) @ (sk_C @ X12)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ (sk_C @ X0))
% 0.21/0.49          | (r1_ordinal1 @ (sk_C @ X0) @ (sk_B_1 @ X0))
% 0.21/0.49          | ~ (v3_ordinal1 @ (sk_B_1 @ X0))
% 0.21/0.49          | (v2_ordinal1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (((v2_ordinal1 @ sk_A)
% 0.21/0.49        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A))
% 0.21/0.49        | (r1_ordinal1 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '21'])).
% 0.21/0.49  thf('23', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '8'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (((r1_ordinal1 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))
% 0.21/0.49        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.21/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (((v2_ordinal1 @ sk_A) | (r1_ordinal1 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '24'])).
% 0.21/0.49  thf('26', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '8'])).
% 0.21/0.49  thf('27', plain, ((r1_ordinal1 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf(redefinition_r1_ordinal1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.21/0.49       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X13)
% 0.21/0.49          | ~ (v3_ordinal1 @ X14)
% 0.21/0.49          | (r1_tarski @ X13 @ X14)
% 0.21/0.49          | ~ (r1_ordinal1 @ X13 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((r1_tarski @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))
% 0.21/0.49        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A))
% 0.21/0.49        | ~ (v3_ordinal1 @ (sk_C @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((r1_tarski @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))
% 0.21/0.49        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (((v2_ordinal1 @ sk_A) | (r1_tarski @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '31'])).
% 0.21/0.49  thf('33', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '8'])).
% 0.21/0.49  thf('34', plain, ((r1_tarski @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.49  thf(d8_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.49       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X0 : $i, X2 : $i]:
% 0.21/0.49         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      ((((sk_C @ sk_A) = (sk_B_1 @ sk_A))
% 0.21/0.49        | (r2_xboole_0 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain, (((v2_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('38', plain, (((v2_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X15)
% 0.21/0.49          | (r1_ordinal1 @ X16 @ X15)
% 0.21/0.49          | (r2_hidden @ X15 @ X16)
% 0.21/0.49          | ~ (v3_ordinal1 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X12 : $i]:
% 0.21/0.49         ((v2_ordinal1 @ X12) | ~ (r2_hidden @ (sk_C @ X12) @ (sk_B_1 @ X12)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ (sk_B_1 @ X0))
% 0.21/0.49          | (r1_ordinal1 @ (sk_B_1 @ X0) @ (sk_C @ X0))
% 0.21/0.49          | ~ (v3_ordinal1 @ (sk_C @ X0))
% 0.21/0.49          | (v2_ordinal1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (((v2_ordinal1 @ sk_A)
% 0.21/0.49        | (v2_ordinal1 @ sk_A)
% 0.21/0.49        | ~ (v3_ordinal1 @ (sk_C @ sk_A))
% 0.21/0.49        | (r1_ordinal1 @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['38', '41'])).
% 0.21/0.49  thf('43', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (((v2_ordinal1 @ sk_A)
% 0.21/0.49        | (v2_ordinal1 @ sk_A)
% 0.21/0.49        | (r1_ordinal1 @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (((r1_ordinal1 @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A)) | (v2_ordinal1 @ sk_A))),
% 0.21/0.49      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.49  thf('46', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '8'])).
% 0.21/0.49  thf('47', plain, ((r1_ordinal1 @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X13)
% 0.21/0.49          | ~ (v3_ordinal1 @ X14)
% 0.21/0.49          | (r1_tarski @ X13 @ X14)
% 0.21/0.49          | ~ (r1_ordinal1 @ X13 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (((r1_tarski @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A))
% 0.21/0.49        | ~ (v3_ordinal1 @ (sk_C @ sk_A))
% 0.21/0.49        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('50', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (((r1_tarski @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A))
% 0.21/0.49        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (((v2_ordinal1 @ sk_A) | (r1_tarski @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['37', '51'])).
% 0.21/0.49  thf('53', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '8'])).
% 0.21/0.49  thf('54', plain, ((r1_tarski @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['52', '53'])).
% 0.21/0.49  thf(t60_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X3 @ X4) | ~ (r2_xboole_0 @ X4 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.21/0.49  thf('56', plain, (~ (r2_xboole_0 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.49  thf('57', plain, (((sk_C @ sk_A) = (sk_B_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '56'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (![X12 : $i]: ((v2_ordinal1 @ X12) | ((sk_B_1 @ X12) != (sk_C @ X12)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      ((((sk_B_1 @ sk_A) != (sk_B_1 @ sk_A)) | (v2_ordinal1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.49  thf('60', plain, ((v2_ordinal1 @ sk_A)),
% 0.21/0.49      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.49  thf('61', plain, ($false), inference('demod', [status(thm)], ['9', '60'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
