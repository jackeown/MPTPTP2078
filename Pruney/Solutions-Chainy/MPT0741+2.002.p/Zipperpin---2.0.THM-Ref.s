%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.scRhUxkHg5

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 210 expanded)
%              Number of leaves         :   20 (  71 expanded)
%              Depth                    :   17
%              Number of atoms          :  356 (1412 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(cc2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) )
     => ( v3_ordinal1 @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( v3_ordinal1 @ X4 )
      | ~ ( v2_ordinal1 @ X4 )
      | ~ ( v1_ordinal1 @ X4 ) ) ),
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
    ! [X7: $i] :
      ( ( v1_ordinal1 @ X7 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('4',plain,(
    ! [X18: $i] :
      ( ( r1_tarski @ X18 @ sk_A )
      | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X7: $i] :
      ( ( v1_ordinal1 @ X7 )
      | ~ ( r1_tarski @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('7',plain,(
    v1_ordinal1 @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf(d3_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v2_ordinal1 @ A )
    <=> ! [B: $i,C: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ( r2_hidden @ C @ A )
            & ~ ( r2_hidden @ B @ C )
            & ( B != C )
            & ~ ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X11: $i] :
      ( ( v2_ordinal1 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('10',plain,(
    ! [X18: $i] :
      ( ( v3_ordinal1 @ X18 )
      | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('13',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ( r1_ordinal1 @ X17 @ X16 )
      | ( r2_hidden @ X16 @ X17 )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('15',plain,(
    ! [X11: $i] :
      ( ( v2_ordinal1 @ X11 )
      | ~ ( r2_hidden @ ( sk_B_1 @ X11 ) @ ( sk_C @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C @ X0 ) @ ( sk_B_1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( sk_B_1 @ X0 ) )
      | ( v2_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) )
    | ( r1_ordinal1 @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X11: $i] :
      ( ( v2_ordinal1 @ X11 )
      | ( r2_hidden @ ( sk_B_1 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('19',plain,(
    ! [X18: $i] :
      ( ( v3_ordinal1 @ X18 )
      | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('22',plain,(
    v3_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('25',plain,(
    r1_ordinal1 @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( v3_ordinal1 @ X13 )
      | ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_ordinal1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('27',plain,
    ( ( r1_tarski @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v3_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('29',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('30',plain,(
    r1_tarski @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('32',plain,
    ( ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( r2_xboole_0 @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ( r2_hidden @ X15 @ X14 )
      | ~ ( r2_xboole_0 @ X15 @ X14 )
      | ~ ( v1_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('34',plain,
    ( ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ~ ( v1_ordinal1 @ ( sk_C @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('36',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('37',plain,(
    v1_ordinal1 @ ( sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('39',plain,
    ( ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','37','38'])).

thf('40',plain,(
    ! [X11: $i] :
      ( ( v2_ordinal1 @ X11 )
      | ~ ( r2_hidden @ ( sk_C @ X11 ) @ ( sk_B_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('41',plain,
    ( ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( v2_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X11: $i] :
      ( ( v2_ordinal1 @ X11 )
      | ( ( sk_B_1 @ X11 )
       != ( sk_C @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('43',plain,(
    v2_ordinal1 @ sk_A ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['8','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.scRhUxkHg5
% 0.11/0.33  % Computer   : n023.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 19:02:21 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 118 iterations in 0.066s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i).
% 0.20/0.51  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.51  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.20/0.51  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.20/0.51  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.20/0.51  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.51  thf(cc2_ordinal1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) => ( v3_ordinal1 @ A ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X4 : $i]:
% 0.20/0.51         ((v3_ordinal1 @ X4) | ~ (v2_ordinal1 @ X4) | ~ (v1_ordinal1 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_ordinal1])).
% 0.20/0.51  thf(t31_ordinal1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ![B:$i]:
% 0.20/0.51         ( ( r2_hidden @ B @ A ) =>
% 0.20/0.51           ( ( v3_ordinal1 @ B ) & ( r1_tarski @ B @ A ) ) ) ) =>
% 0.20/0.51       ( v3_ordinal1 @ A ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ![B:$i]:
% 0.20/0.51            ( ( r2_hidden @ B @ A ) =>
% 0.20/0.51              ( ( v3_ordinal1 @ B ) & ( r1_tarski @ B @ A ) ) ) ) =>
% 0.20/0.51          ( v3_ordinal1 @ A ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t31_ordinal1])).
% 0.20/0.51  thf('1', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('2', plain, ((~ (v1_ordinal1 @ sk_A) | ~ (v2_ordinal1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf(d2_ordinal1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_ordinal1 @ A ) <=>
% 0.20/0.51       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X7 : $i]: ((v1_ordinal1 @ X7) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X18 : $i]: ((r1_tarski @ X18 @ sk_A) | ~ (r2_hidden @ X18 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (((v1_ordinal1 @ sk_A) | (r1_tarski @ (sk_B @ sk_A) @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X7 : $i]: ((v1_ordinal1 @ X7) | ~ (r1_tarski @ (sk_B @ X7) @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.20/0.51  thf('7', plain, ((v1_ordinal1 @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf('8', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '7'])).
% 0.20/0.51  thf(d3_ordinal1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v2_ordinal1 @ A ) <=>
% 0.20/0.51       ( ![B:$i,C:$i]:
% 0.20/0.51         ( ~( ( r2_hidden @ B @ A ) & ( r2_hidden @ C @ A ) & 
% 0.20/0.51              ( ~( r2_hidden @ B @ C ) ) & ( ( B ) != ( C ) ) & 
% 0.20/0.51              ( ~( r2_hidden @ C @ B ) ) ) ) ) ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X11 : $i]: ((v2_ordinal1 @ X11) | (r2_hidden @ (sk_C @ X11) @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X18 : $i]: ((v3_ordinal1 @ X18) | ~ (r2_hidden @ X18 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('11', plain, (((v2_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_C @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('12', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '7'])).
% 0.20/0.51  thf('13', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf(t26_ordinal1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X16)
% 0.20/0.51          | (r1_ordinal1 @ X17 @ X16)
% 0.20/0.51          | (r2_hidden @ X16 @ X17)
% 0.20/0.51          | ~ (v3_ordinal1 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X11 : $i]:
% 0.20/0.51         ((v2_ordinal1 @ X11) | ~ (r2_hidden @ (sk_B_1 @ X11) @ (sk_C @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ (sk_C @ X0))
% 0.20/0.51          | (r1_ordinal1 @ (sk_C @ X0) @ (sk_B_1 @ X0))
% 0.20/0.51          | ~ (v3_ordinal1 @ (sk_B_1 @ X0))
% 0.20/0.51          | (v2_ordinal1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (((v2_ordinal1 @ sk_A)
% 0.20/0.51        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A))
% 0.20/0.51        | (r1_ordinal1 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X11 : $i]: ((v2_ordinal1 @ X11) | (r2_hidden @ (sk_B_1 @ X11) @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X18 : $i]: ((v3_ordinal1 @ X18) | ~ (r2_hidden @ X18 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('20', plain, (((v2_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '7'])).
% 0.20/0.51  thf('22', plain, ((v3_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (((v2_ordinal1 @ sk_A) | (r1_ordinal1 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '22'])).
% 0.20/0.51  thf('24', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '7'])).
% 0.20/0.51  thf('25', plain, ((r1_ordinal1 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf(redefinition_r1_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.51       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X12)
% 0.20/0.51          | ~ (v3_ordinal1 @ X13)
% 0.20/0.51          | (r1_tarski @ X12 @ X13)
% 0.20/0.51          | ~ (r1_ordinal1 @ X12 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (((r1_tarski @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))
% 0.20/0.51        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A))
% 0.20/0.51        | ~ (v3_ordinal1 @ (sk_C @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('28', plain, ((v3_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('29', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf('30', plain, ((r1_tarski @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.20/0.51  thf(d8_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.51       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i]:
% 0.20/0.51         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((((sk_C @ sk_A) = (sk_B_1 @ sk_A))
% 0.20/0.51        | (r2_xboole_0 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf(t21_ordinal1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_ordinal1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X14)
% 0.20/0.51          | (r2_hidden @ X15 @ X14)
% 0.20/0.51          | ~ (r2_xboole_0 @ X15 @ X14)
% 0.20/0.51          | ~ (v1_ordinal1 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((((sk_C @ sk_A) = (sk_B_1 @ sk_A))
% 0.20/0.51        | ~ (v1_ordinal1 @ (sk_C @ sk_A))
% 0.20/0.51        | (r2_hidden @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))
% 0.20/0.51        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf(cc1_ordinal1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.20/0.51  thf('36', plain, (![X3 : $i]: ((v1_ordinal1 @ X3) | ~ (v3_ordinal1 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.20/0.51  thf('37', plain, ((v1_ordinal1 @ (sk_C @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.51  thf('38', plain, ((v3_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((((sk_C @ sk_A) = (sk_B_1 @ sk_A))
% 0.20/0.51        | (r2_hidden @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['34', '37', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X11 : $i]:
% 0.20/0.51         ((v2_ordinal1 @ X11) | ~ (r2_hidden @ (sk_C @ X11) @ (sk_B_1 @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      ((((sk_C @ sk_A) = (sk_B_1 @ sk_A)) | (v2_ordinal1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X11 : $i]: ((v2_ordinal1 @ X11) | ((sk_B_1 @ X11) != (sk_C @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.20/0.51  thf('43', plain, ((v2_ordinal1 @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain, ($false), inference('demod', [status(thm)], ['8', '43'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
