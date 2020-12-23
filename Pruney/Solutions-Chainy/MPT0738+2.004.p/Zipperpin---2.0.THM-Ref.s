%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RXWMjAC4iE

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  65 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  226 ( 405 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v3_ordinal1 @ X8 )
      | ~ ( v3_ordinal1 @ X9 )
      | ( r1_ordinal1 @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t26_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r1_ordinal1 @ A @ B )
              | ( r2_hidden @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_ordinal1])).

thf('7',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ( r2_hidden @ X11 @ X10 )
      | ( X11 = X10 )
      | ( r2_hidden @ X10 @ X11 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('9',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = sk_A ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r1_tarski @ X5 @ X6 )
      | ~ ( v1_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('15',plain,
    ( ( sk_B_1 = sk_A )
    | ~ ( v1_ordinal1 @ sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('17',plain,(
    ! [X4: $i] :
      ( ( v1_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('18',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_B_1 = sk_A )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v3_ordinal1 @ X8 )
      | ~ ( v3_ordinal1 @ X9 )
      | ( r1_ordinal1 @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('21',plain,
    ( ( sk_B_1 = sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_B_1 = sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_B_1 = sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['7','26'])).

thf('28',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','27'])).

thf('29',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RXWMjAC4iE
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 38 iterations in 0.019s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.47  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.21/0.47  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.21/0.47  thf(d3_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X1 : $i, X3 : $i]:
% 0.21/0.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X1 : $i, X3 : $i]:
% 0.21/0.47         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.47  thf(redefinition_r1_ordinal1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.21/0.47       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]:
% 0.21/0.47         (~ (v3_ordinal1 @ X8)
% 0.21/0.47          | ~ (v3_ordinal1 @ X9)
% 0.21/0.47          | (r1_ordinal1 @ X8 @ X9)
% 0.21/0.47          | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.47  thf(t26_ordinal1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.47           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( v3_ordinal1 @ A ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( v3_ordinal1 @ B ) =>
% 0.21/0.47              ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t26_ordinal1])).
% 0.21/0.47  thf('7', plain, (~ (r1_ordinal1 @ sk_A @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t24_ordinal1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.47           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.21/0.47                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]:
% 0.21/0.47         (~ (v3_ordinal1 @ X10)
% 0.21/0.47          | (r2_hidden @ X11 @ X10)
% 0.21/0.47          | ((X11) = (X10))
% 0.21/0.47          | (r2_hidden @ X10 @ X11)
% 0.21/0.47          | ~ (v3_ordinal1 @ X11))),
% 0.21/0.47      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.21/0.47  thf('9', plain, (~ (r2_hidden @ sk_B_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((~ (v3_ordinal1 @ sk_B_1)
% 0.21/0.47        | (r2_hidden @ sk_A @ sk_B_1)
% 0.21/0.47        | ((sk_B_1) = (sk_A))
% 0.21/0.47        | ~ (v3_ordinal1 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('12', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('13', plain, (((r2_hidden @ sk_A @ sk_B_1) | ((sk_B_1) = (sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.21/0.47  thf(d2_ordinal1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_ordinal1 @ A ) <=>
% 0.21/0.47       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.47          | (r1_tarski @ X5 @ X6)
% 0.21/0.47          | ~ (v1_ordinal1 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((((sk_B_1) = (sk_A))
% 0.21/0.47        | ~ (v1_ordinal1 @ sk_B_1)
% 0.21/0.47        | (r1_tarski @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(cc1_ordinal1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.21/0.47  thf('17', plain, (![X4 : $i]: ((v1_ordinal1 @ X4) | ~ (v3_ordinal1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.47  thf('18', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain, ((((sk_B_1) = (sk_A)) | (r1_tarski @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]:
% 0.21/0.47         (~ (v3_ordinal1 @ X8)
% 0.21/0.47          | ~ (v3_ordinal1 @ X9)
% 0.21/0.47          | (r1_ordinal1 @ X8 @ X9)
% 0.21/0.47          | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      ((((sk_B_1) = (sk_A))
% 0.21/0.47        | (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.21/0.47        | ~ (v3_ordinal1 @ sk_B_1)
% 0.21/0.47        | ~ (v3_ordinal1 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('24', plain, ((((sk_B_1) = (sk_A)) | (r1_ordinal1 @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.21/0.47  thf('25', plain, (~ (r1_ordinal1 @ sk_A @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('26', plain, (((sk_B_1) = (sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain, (~ (r1_ordinal1 @ sk_A @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '26'])).
% 0.21/0.47  thf('28', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '27'])).
% 0.21/0.47  thf('29', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('30', plain, ($false), inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
