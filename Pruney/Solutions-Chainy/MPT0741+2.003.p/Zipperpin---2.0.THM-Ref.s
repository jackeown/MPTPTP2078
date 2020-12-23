%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r7hrD6XxPi

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 271 expanded)
%              Number of leaves         :   17 (  84 expanded)
%              Depth                    :   20
%              Number of atoms          :  441 (1842 expanded)
%              Number of equality atoms :    7 (  17 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(cc2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) )
     => ( v3_ordinal1 @ A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( v3_ordinal1 @ X3 )
      | ~ ( v2_ordinal1 @ X3 )
      | ~ ( v1_ordinal1 @ X3 ) ) ),
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
    ! [X6: $i] :
      ( ( v1_ordinal1 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('4',plain,(
    ! [X15: $i] :
      ( ( r1_tarski @ X15 @ sk_A )
      | ~ ( r2_hidden @ X15 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X6: $i] :
      ( ( v1_ordinal1 @ X6 )
      | ~ ( r1_tarski @ ( sk_B @ X6 ) @ X6 ) ) ),
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
    ! [X10: $i] :
      ( ( v2_ordinal1 @ X10 )
      | ( r2_hidden @ ( sk_B_1 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('11',plain,(
    ! [X15: $i] :
      ( ( v3_ordinal1 @ X15 )
      | ~ ( r2_hidden @ X15 @ sk_A ) ) ),
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
    ! [X10: $i] :
      ( ( v2_ordinal1 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('15',plain,(
    ! [X15: $i] :
      ( ( v3_ordinal1 @ X15 )
      | ~ ( r2_hidden @ X15 @ sk_A ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ( r1_ordinal1 @ X14 @ X13 )
      | ( r2_hidden @ X13 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('20',plain,(
    ! [X10: $i] :
      ( ( v2_ordinal1 @ X10 )
      | ~ ( r2_hidden @ ( sk_B_1 @ X10 ) @ ( sk_C @ X10 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ~ ( v3_ordinal1 @ X12 )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_ordinal1 @ X11 @ X12 ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) )
    | ( ( sk_B_1 @ sk_A )
      = ( sk_C @ sk_A ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ( r1_ordinal1 @ X14 @ X13 )
      | ( r2_hidden @ X13 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('40',plain,(
    ! [X10: $i] :
      ( ( v2_ordinal1 @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X10 ) @ ( sk_B_1 @ X10 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ~ ( v3_ordinal1 @ X12 )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_ordinal1 @ X11 @ X12 ) ) ),
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

thf('55',plain,
    ( ( sk_B_1 @ sk_A )
    = ( sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['36','54'])).

thf('56',plain,(
    ! [X10: $i] :
      ( ( v2_ordinal1 @ X10 )
      | ( ( sk_B_1 @ X10 )
       != ( sk_C @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('57',plain,
    ( ( ( sk_B_1 @ sk_A )
     != ( sk_B_1 @ sk_A ) )
    | ( v2_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_ordinal1 @ sk_A ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['9','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r7hrD6XxPi
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 82 iterations in 0.057s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.19/0.50  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.19/0.50  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.50  thf(cc2_ordinal1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) => ( v3_ordinal1 @ A ) ))).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      (![X3 : $i]:
% 0.19/0.50         ((v3_ordinal1 @ X3) | ~ (v2_ordinal1 @ X3) | ~ (v1_ordinal1 @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [cc2_ordinal1])).
% 0.19/0.50  thf(t31_ordinal1, conjecture,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ![B:$i]:
% 0.19/0.50         ( ( r2_hidden @ B @ A ) =>
% 0.19/0.50           ( ( v3_ordinal1 @ B ) & ( r1_tarski @ B @ A ) ) ) ) =>
% 0.19/0.50       ( v3_ordinal1 @ A ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i]:
% 0.19/0.50        ( ( ![B:$i]:
% 0.19/0.50            ( ( r2_hidden @ B @ A ) =>
% 0.19/0.50              ( ( v3_ordinal1 @ B ) & ( r1_tarski @ B @ A ) ) ) ) =>
% 0.19/0.50          ( v3_ordinal1 @ A ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t31_ordinal1])).
% 0.19/0.50  thf('1', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('2', plain, ((~ (v1_ordinal1 @ sk_A) | ~ (v2_ordinal1 @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf(d2_ordinal1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_ordinal1 @ A ) <=>
% 0.19/0.50       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X6 : $i]: ((v1_ordinal1 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X15 : $i]: ((r1_tarski @ X15 @ sk_A) | ~ (r2_hidden @ X15 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (((v1_ordinal1 @ sk_A) | (r1_tarski @ (sk_B @ sk_A) @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X6 : $i]: ((v1_ordinal1 @ X6) | ~ (r1_tarski @ (sk_B @ X6) @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.19/0.50  thf('7', plain, (((v1_ordinal1 @ sk_A) | (v1_ordinal1 @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.50  thf('8', plain, ((v1_ordinal1 @ sk_A)),
% 0.19/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.50  thf('9', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.19/0.50      inference('demod', [status(thm)], ['2', '8'])).
% 0.19/0.50  thf(d3_ordinal1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v2_ordinal1 @ A ) <=>
% 0.19/0.50       ( ![B:$i,C:$i]:
% 0.19/0.50         ( ~( ( r2_hidden @ B @ A ) & ( r2_hidden @ C @ A ) & 
% 0.19/0.50              ( ~( r2_hidden @ B @ C ) ) & ( ( B ) != ( C ) ) & 
% 0.19/0.50              ( ~( r2_hidden @ C @ B ) ) ) ) ) ))).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X10 : $i]: ((v2_ordinal1 @ X10) | (r2_hidden @ (sk_B_1 @ X10) @ X10))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X15 : $i]: ((v3_ordinal1 @ X15) | ~ (r2_hidden @ X15 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('12', plain, (((v2_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf('13', plain, (((v2_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X10 : $i]: ((v2_ordinal1 @ X10) | (r2_hidden @ (sk_C @ X10) @ X10))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X15 : $i]: ((v3_ordinal1 @ X15) | ~ (r2_hidden @ X15 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('16', plain, (((v2_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_C @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.50  thf('17', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.19/0.50      inference('demod', [status(thm)], ['2', '8'])).
% 0.19/0.50  thf('18', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.19/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf(t26_ordinal1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v3_ordinal1 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( v3_ordinal1 @ B ) =>
% 0.19/0.50           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X13 : $i, X14 : $i]:
% 0.19/0.50         (~ (v3_ordinal1 @ X13)
% 0.19/0.50          | (r1_ordinal1 @ X14 @ X13)
% 0.19/0.50          | (r2_hidden @ X13 @ X14)
% 0.19/0.50          | ~ (v3_ordinal1 @ X14))),
% 0.19/0.50      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X10 : $i]:
% 0.19/0.50         ((v2_ordinal1 @ X10) | ~ (r2_hidden @ (sk_B_1 @ X10) @ (sk_C @ X10)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (v3_ordinal1 @ (sk_C @ X0))
% 0.19/0.50          | (r1_ordinal1 @ (sk_C @ X0) @ (sk_B_1 @ X0))
% 0.19/0.50          | ~ (v3_ordinal1 @ (sk_B_1 @ X0))
% 0.19/0.50          | (v2_ordinal1 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (((v2_ordinal1 @ sk_A)
% 0.19/0.50        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A))
% 0.19/0.50        | (r1_ordinal1 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['18', '21'])).
% 0.19/0.50  thf('23', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.19/0.50      inference('demod', [status(thm)], ['2', '8'])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (((r1_ordinal1 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))
% 0.19/0.50        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.19/0.50      inference('clc', [status(thm)], ['22', '23'])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (((v2_ordinal1 @ sk_A) | (r1_ordinal1 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['13', '24'])).
% 0.19/0.50  thf('26', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.19/0.50      inference('demod', [status(thm)], ['2', '8'])).
% 0.19/0.50  thf('27', plain, ((r1_ordinal1 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))),
% 0.19/0.50      inference('clc', [status(thm)], ['25', '26'])).
% 0.19/0.50  thf(redefinition_r1_ordinal1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.19/0.50       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i]:
% 0.19/0.50         (~ (v3_ordinal1 @ X11)
% 0.19/0.50          | ~ (v3_ordinal1 @ X12)
% 0.19/0.50          | (r1_tarski @ X11 @ X12)
% 0.19/0.50          | ~ (r1_ordinal1 @ X11 @ X12))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (((r1_tarski @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))
% 0.19/0.50        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A))
% 0.19/0.50        | ~ (v3_ordinal1 @ (sk_C @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.50  thf('30', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.19/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      (((r1_tarski @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))
% 0.19/0.50        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (((v2_ordinal1 @ sk_A) | (r1_tarski @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['12', '31'])).
% 0.19/0.50  thf('33', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.19/0.50      inference('demod', [status(thm)], ['2', '8'])).
% 0.19/0.50  thf('34', plain, ((r1_tarski @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))),
% 0.19/0.50      inference('clc', [status(thm)], ['32', '33'])).
% 0.19/0.50  thf(d10_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      (![X0 : $i, X2 : $i]:
% 0.19/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      ((~ (r1_tarski @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A))
% 0.19/0.50        | ((sk_B_1 @ sk_A) = (sk_C @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.50  thf('37', plain, (((v2_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf('38', plain, (((v2_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      (![X13 : $i, X14 : $i]:
% 0.19/0.50         (~ (v3_ordinal1 @ X13)
% 0.19/0.50          | (r1_ordinal1 @ X14 @ X13)
% 0.19/0.50          | (r2_hidden @ X13 @ X14)
% 0.19/0.50          | ~ (v3_ordinal1 @ X14))),
% 0.19/0.50      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      (![X10 : $i]:
% 0.19/0.50         ((v2_ordinal1 @ X10) | ~ (r2_hidden @ (sk_C @ X10) @ (sk_B_1 @ X10)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (v3_ordinal1 @ (sk_B_1 @ X0))
% 0.19/0.50          | (r1_ordinal1 @ (sk_B_1 @ X0) @ (sk_C @ X0))
% 0.19/0.50          | ~ (v3_ordinal1 @ (sk_C @ X0))
% 0.19/0.50          | (v2_ordinal1 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      (((v2_ordinal1 @ sk_A)
% 0.19/0.50        | (v2_ordinal1 @ sk_A)
% 0.19/0.50        | ~ (v3_ordinal1 @ (sk_C @ sk_A))
% 0.19/0.50        | (r1_ordinal1 @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['38', '41'])).
% 0.19/0.50  thf('43', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.19/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf('44', plain,
% 0.19/0.50      (((v2_ordinal1 @ sk_A)
% 0.19/0.50        | (v2_ordinal1 @ sk_A)
% 0.19/0.50        | (r1_ordinal1 @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['42', '43'])).
% 0.19/0.50  thf('45', plain,
% 0.19/0.50      (((r1_ordinal1 @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A)) | (v2_ordinal1 @ sk_A))),
% 0.19/0.50      inference('simplify', [status(thm)], ['44'])).
% 0.19/0.50  thf('46', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.19/0.50      inference('demod', [status(thm)], ['2', '8'])).
% 0.19/0.50  thf('47', plain, ((r1_ordinal1 @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A))),
% 0.19/0.50      inference('clc', [status(thm)], ['45', '46'])).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i]:
% 0.19/0.50         (~ (v3_ordinal1 @ X11)
% 0.19/0.50          | ~ (v3_ordinal1 @ X12)
% 0.19/0.50          | (r1_tarski @ X11 @ X12)
% 0.19/0.50          | ~ (r1_ordinal1 @ X11 @ X12))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.19/0.50  thf('49', plain,
% 0.19/0.50      (((r1_tarski @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A))
% 0.19/0.50        | ~ (v3_ordinal1 @ (sk_C @ sk_A))
% 0.19/0.50        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.50  thf('50', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.19/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf('51', plain,
% 0.19/0.50      (((r1_tarski @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A))
% 0.19/0.50        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.50  thf('52', plain,
% 0.19/0.50      (((v2_ordinal1 @ sk_A) | (r1_tarski @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['37', '51'])).
% 0.19/0.50  thf('53', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.19/0.50      inference('demod', [status(thm)], ['2', '8'])).
% 0.19/0.50  thf('54', plain, ((r1_tarski @ (sk_B_1 @ sk_A) @ (sk_C @ sk_A))),
% 0.19/0.50      inference('clc', [status(thm)], ['52', '53'])).
% 0.19/0.50  thf('55', plain, (((sk_B_1 @ sk_A) = (sk_C @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['36', '54'])).
% 0.19/0.50  thf('56', plain,
% 0.19/0.50      (![X10 : $i]: ((v2_ordinal1 @ X10) | ((sk_B_1 @ X10) != (sk_C @ X10)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.19/0.50  thf('57', plain,
% 0.19/0.50      ((((sk_B_1 @ sk_A) != (sk_B_1 @ sk_A)) | (v2_ordinal1 @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.50  thf('58', plain, ((v2_ordinal1 @ sk_A)),
% 0.19/0.50      inference('simplify', [status(thm)], ['57'])).
% 0.19/0.50  thf('59', plain, ($false), inference('demod', [status(thm)], ['9', '58'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
