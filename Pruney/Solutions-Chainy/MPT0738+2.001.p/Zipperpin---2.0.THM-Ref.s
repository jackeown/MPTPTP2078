%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5VB61vSkN5

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  95 expanded)
%              Number of leaves         :   12 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  270 ( 743 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ( r2_hidden @ X14 @ X13 )
      | ( X14 = X13 )
      | ( r2_hidden @ X13 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('2',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ~ ( v3_ordinal1 @ X10 )
      | ( r1_ordinal1 @ X9 @ X10 )
      | ( r1_ordinal1 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ~ ( v3_ordinal1 @ X12 )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_ordinal1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('21',plain,
    ( ( sk_B = sk_A )
    | ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('23',plain,(
    sk_B = sk_A ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ~ ( v3_ordinal1 @ X10 )
      | ( r1_ordinal1 @ X9 @ X10 )
      | ( r1_ordinal1 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('28',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5VB61vSkN5
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 47 iterations in 0.028s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(t26_ordinal1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.48           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( v3_ordinal1 @ A ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( v3_ordinal1 @ B ) =>
% 0.21/0.48              ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t26_ordinal1])).
% 0.21/0.48  thf('0', plain, (~ (r1_ordinal1 @ sk_A @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t24_ordinal1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.48           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.21/0.48                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i]:
% 0.21/0.48         (~ (v3_ordinal1 @ X13)
% 0.21/0.48          | (r2_hidden @ X14 @ X13)
% 0.21/0.48          | ((X14) = (X13))
% 0.21/0.48          | (r2_hidden @ X13 @ X14)
% 0.21/0.48          | ~ (v3_ordinal1 @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.21/0.48  thf('2', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((~ (v3_ordinal1 @ sk_B)
% 0.21/0.48        | (r2_hidden @ sk_A @ sk_B)
% 0.21/0.48        | ((sk_B) = (sk_A))
% 0.21/0.48        | ~ (v3_ordinal1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('5', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain, (((r2_hidden @ sk_A @ sk_B) | ((sk_B) = (sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.48  thf(connectedness_r1_ordinal1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.21/0.48       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (v3_ordinal1 @ X9)
% 0.21/0.48          | ~ (v3_ordinal1 @ X10)
% 0.21/0.48          | (r1_ordinal1 @ X9 @ X10)
% 0.21/0.48          | (r1_ordinal1 @ X10 @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.21/0.48  thf(redefinition_r1_ordinal1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.21/0.48       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (v3_ordinal1 @ X11)
% 0.21/0.48          | ~ (v3_ordinal1 @ X12)
% 0.21/0.48          | (r1_tarski @ X11 @ X12)
% 0.21/0.48          | ~ (r1_ordinal1 @ X11 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_ordinal1 @ X0 @ X1)
% 0.21/0.48          | ~ (v3_ordinal1 @ X0)
% 0.21/0.48          | ~ (v3_ordinal1 @ X1)
% 0.21/0.48          | (r1_tarski @ X1 @ X0)
% 0.21/0.48          | ~ (v3_ordinal1 @ X0)
% 0.21/0.48          | ~ (v3_ordinal1 @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_tarski @ X1 @ X0)
% 0.21/0.48          | ~ (v3_ordinal1 @ X1)
% 0.21/0.48          | ~ (v3_ordinal1 @ X0)
% 0.21/0.48          | (r1_ordinal1 @ X0 @ X1))),
% 0.21/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.48  thf(d3_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ X3)
% 0.21/0.48          | (r2_hidden @ X2 @ X4)
% 0.21/0.48          | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((r1_ordinal1 @ X0 @ X1)
% 0.21/0.48          | ~ (v3_ordinal1 @ X0)
% 0.21/0.48          | ~ (v3_ordinal1 @ X1)
% 0.21/0.48          | (r2_hidden @ X2 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X2 @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((sk_B) = (sk_A))
% 0.21/0.48          | (r2_hidden @ sk_A @ X0)
% 0.21/0.48          | ~ (v3_ordinal1 @ sk_B)
% 0.21/0.48          | ~ (v3_ordinal1 @ X0)
% 0.21/0.48          | (r1_ordinal1 @ X0 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '12'])).
% 0.21/0.48  thf('14', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((sk_B) = (sk_A))
% 0.21/0.48          | (r2_hidden @ sk_A @ X0)
% 0.21/0.48          | ~ (v3_ordinal1 @ X0)
% 0.21/0.48          | (r1_ordinal1 @ X0 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain, (~ (r1_ordinal1 @ sk_A @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((~ (v3_ordinal1 @ sk_A) | (r2_hidden @ sk_A @ sk_A) | ((sk_B) = (sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('18', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain, (((r2_hidden @ sk_A @ sk_A) | ((sk_B) = (sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf(antisymmetry_r2_hidden, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.21/0.48  thf('21', plain, ((((sk_B) = (sk_A)) | ~ (r2_hidden @ sk_A @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain, (((r2_hidden @ sk_A @ sk_A) | ((sk_B) = (sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('23', plain, (((sk_B) = (sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (v3_ordinal1 @ X9)
% 0.21/0.48          | ~ (v3_ordinal1 @ X10)
% 0.21/0.48          | (r1_ordinal1 @ X9 @ X10)
% 0.21/0.48          | (r1_ordinal1 @ X10 @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_ordinal1 @ X0 @ sk_A)
% 0.21/0.48          | (r1_ordinal1 @ sk_A @ X0)
% 0.21/0.48          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.48  thf('27', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.21/0.48      inference('eq_fact', [status(thm)], ['26'])).
% 0.21/0.48  thf('28', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('29', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain, ($false),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '23', '29'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
