%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7NsiZhiTxv

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  194 ( 221 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

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

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('4',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X14 ) )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t37_ordinal1,conjecture,(
    ! [A: $i] :
      ~ ! [B: $i] :
          ( ( r2_hidden @ B @ A )
        <=> ( v3_ordinal1 @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ! [B: $i] :
            ( ( r2_hidden @ B @ A )
          <=> ( v3_ordinal1 @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t37_ordinal1])).

thf('5',plain,(
    ! [X19: $i] :
      ( ( r2_hidden @ X19 @ sk_A )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k1_ordinal1 @ X13 ) )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('7',plain,(
    ! [X13: $i] :
      ( r2_hidden @ X13 @ ( k1_ordinal1 @ X13 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k3_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X0 @ ( k3_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf(t35_ordinal1,axiom,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( v3_ordinal1 @ B ) )
     => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )).

thf('16',plain,(
    ! [X15: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X15 ) )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t35_ordinal1])).

thf('17',plain,(
    ! [X18: $i] :
      ( ( v3_ordinal1 @ X18 )
      | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v3_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X15: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X15 ) )
      | ~ ( v3_ordinal1 @ ( sk_B @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t35_ordinal1])).

thf('20',plain,(
    v3_ordinal1 @ ( k3_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['15','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7NsiZhiTxv
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 41 iterations in 0.024s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.48  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.22/0.48  thf(d3_tarski, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (![X1 : $i, X3 : $i]:
% 0.22/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X1 : $i, X3 : $i]:
% 0.22/0.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.48  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.22/0.48      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.48  thf(t29_ordinal1, axiom,
% 0.22/0.48    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X14 : $i]:
% 0.22/0.48         ((v3_ordinal1 @ (k1_ordinal1 @ X14)) | ~ (v3_ordinal1 @ X14))),
% 0.22/0.48      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.22/0.48  thf(t37_ordinal1, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ~( ![B:$i]: ( ( r2_hidden @ B @ A ) <=> ( v3_ordinal1 @ B ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ~( ![B:$i]: ( ( r2_hidden @ B @ A ) <=> ( v3_ordinal1 @ B ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t37_ordinal1])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X19 : $i]: ((r2_hidden @ X19 @ sk_A) | ~ (v3_ordinal1 @ X19))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t13_ordinal1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.22/0.48       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X12 : $i, X13 : $i]:
% 0.22/0.48         ((r2_hidden @ X12 @ (k1_ordinal1 @ X13)) | ((X12) != (X13)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.22/0.48  thf('7', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_ordinal1 @ X13))),
% 0.22/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.48  thf(d4_tarski, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.22/0.48       ( ![C:$i]:
% 0.22/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.48           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X4 @ X5)
% 0.22/0.48          | ~ (r2_hidden @ X6 @ X4)
% 0.22/0.48          | (r2_hidden @ X6 @ X7)
% 0.22/0.48          | ((X7) != (k3_tarski @ X5)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d4_tarski])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.48         ((r2_hidden @ X6 @ (k3_tarski @ X5))
% 0.22/0.48          | ~ (r2_hidden @ X6 @ X4)
% 0.22/0.48          | ~ (r2_hidden @ X4 @ X5))),
% 0.22/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (r2_hidden @ (k1_ordinal1 @ X0) @ X1)
% 0.22/0.48          | (r2_hidden @ X0 @ (k3_tarski @ X1)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['7', '9'])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.22/0.48          | (r2_hidden @ X0 @ (k3_tarski @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['5', '10'])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v3_ordinal1 @ X0) | (r2_hidden @ X0 @ (k3_tarski @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '11'])).
% 0.22/0.48  thf(t7_ordinal1, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X16 : $i, X17 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 0.22/0.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v3_ordinal1 @ X0) | ~ (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.48  thf('15', plain, (~ (v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['3', '14'])).
% 0.22/0.48  thf(t35_ordinal1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v3_ordinal1 @ B ) ) ) =>
% 0.22/0.48       ( v3_ordinal1 @ ( k3_tarski @ A ) ) ))).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X15 : $i]:
% 0.22/0.48         ((v3_ordinal1 @ (k3_tarski @ X15)) | (r2_hidden @ (sk_B @ X15) @ X15))),
% 0.22/0.48      inference('cnf', [status(esa)], [t35_ordinal1])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X18 : $i]: ((v3_ordinal1 @ X18) | ~ (r2_hidden @ X18 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (((v3_ordinal1 @ (k3_tarski @ sk_A)) | (v3_ordinal1 @ (sk_B @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (![X15 : $i]:
% 0.22/0.48         ((v3_ordinal1 @ (k3_tarski @ X15)) | ~ (v3_ordinal1 @ (sk_B @ X15)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t35_ordinal1])).
% 0.22/0.48  thf('20', plain, ((v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.22/0.48      inference('clc', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf('21', plain, ($false), inference('demod', [status(thm)], ['15', '20'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
