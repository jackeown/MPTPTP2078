%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1u5jrxgojY

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:17 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   28 (  37 expanded)
%              Number of leaves         :   10 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  170 ( 283 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(t50_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_xboole_0 @ A @ B )
              & ( A != B )
              & ~ ( r2_xboole_0 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ~ ( ~ ( r2_xboole_0 @ A @ B )
                & ( A != B )
                & ~ ( r2_xboole_0 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_ordinal1])).

thf('0',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( r3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ( r3_xboole_0 @ X7 @ X6 )
      | ~ ( v3_ordinal1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t25_ordinal1])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        | ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X4 @ X3 )
      | ~ ( r3_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ X0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ~ ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_A = sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1u5jrxgojY
% 0.15/0.37  % Computer   : n012.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 10:44:37 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 54 iterations in 0.024s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.24/0.50  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.50  thf(r3_xboole_0_type, type, r3_xboole_0: $i > $i > $o).
% 0.24/0.50  thf(t50_ordinal1, conjecture,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( v3_ordinal1 @ A ) =>
% 0.24/0.50       ( ![B:$i]:
% 0.24/0.50         ( ( v3_ordinal1 @ B ) =>
% 0.24/0.50           ( ~( ( ~( r2_xboole_0 @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.24/0.50                ( ~( r2_xboole_0 @ B @ A ) ) ) ) ) ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i]:
% 0.24/0.50        ( ( v3_ordinal1 @ A ) =>
% 0.24/0.50          ( ![B:$i]:
% 0.24/0.50            ( ( v3_ordinal1 @ B ) =>
% 0.24/0.50              ( ~( ( ~( r2_xboole_0 @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.24/0.50                   ( ~( r2_xboole_0 @ B @ A ) ) ) ) ) ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t50_ordinal1])).
% 0.24/0.50  thf('0', plain, (~ (r2_xboole_0 @ sk_A @ sk_B)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(t25_ordinal1, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( v3_ordinal1 @ A ) =>
% 0.24/0.50       ( ![B:$i]: ( ( v3_ordinal1 @ B ) => ( r3_xboole_0 @ A @ B ) ) ) ))).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      (![X6 : $i, X7 : $i]:
% 0.24/0.50         (~ (v3_ordinal1 @ X6) | (r3_xboole_0 @ X7 @ X6) | ~ (v3_ordinal1 @ X7))),
% 0.24/0.50      inference('cnf', [status(esa)], [t25_ordinal1])).
% 0.24/0.50  thf(d9_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( r3_xboole_0 @ A @ B ) <=>
% 0.24/0.50       ( ( r1_tarski @ A @ B ) | ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      (![X3 : $i, X4 : $i]:
% 0.24/0.50         ((r1_tarski @ X3 @ X4)
% 0.24/0.50          | (r1_tarski @ X4 @ X3)
% 0.24/0.50          | ~ (r3_xboole_0 @ X4 @ X3))),
% 0.24/0.50      inference('cnf', [status(esa)], [d9_xboole_0])).
% 0.24/0.50  thf('3', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (~ (v3_ordinal1 @ X1)
% 0.24/0.50          | ~ (v3_ordinal1 @ X0)
% 0.24/0.50          | (r1_tarski @ X1 @ X0)
% 0.24/0.50          | (r1_tarski @ X0 @ X1))),
% 0.24/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.50  thf(d8_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.24/0.50       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (![X0 : $i, X2 : $i]:
% 0.24/0.50         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.24/0.50      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         ((r1_tarski @ X0 @ X1)
% 0.24/0.50          | ~ (v3_ordinal1 @ X0)
% 0.24/0.50          | ~ (v3_ordinal1 @ X1)
% 0.24/0.50          | ((X1) = (X0))
% 0.24/0.50          | (r2_xboole_0 @ X1 @ X0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.50  thf('6', plain,
% 0.24/0.50      (![X0 : $i, X2 : $i]:
% 0.24/0.50         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.24/0.50      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.24/0.50  thf('7', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         ((r2_xboole_0 @ X0 @ X1)
% 0.24/0.50          | ((X0) = (X1))
% 0.24/0.50          | ~ (v3_ordinal1 @ X0)
% 0.24/0.50          | ~ (v3_ordinal1 @ X1)
% 0.24/0.50          | ((X1) = (X0))
% 0.24/0.50          | (r2_xboole_0 @ X1 @ X0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.24/0.50  thf('8', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         ((r2_xboole_0 @ X1 @ X0)
% 0.24/0.50          | ~ (v3_ordinal1 @ X1)
% 0.24/0.50          | ~ (v3_ordinal1 @ X0)
% 0.24/0.50          | ((X0) = (X1))
% 0.24/0.50          | (r2_xboole_0 @ X0 @ X1))),
% 0.24/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.24/0.50  thf('9', plain, (~ (r2_xboole_0 @ sk_B @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('10', plain,
% 0.24/0.50      (((r2_xboole_0 @ sk_A @ sk_B)
% 0.24/0.50        | ((sk_A) = (sk_B))
% 0.24/0.50        | ~ (v3_ordinal1 @ sk_A)
% 0.24/0.50        | ~ (v3_ordinal1 @ sk_B))),
% 0.24/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.50  thf('11', plain, ((v3_ordinal1 @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('12', plain, ((v3_ordinal1 @ sk_B)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('13', plain, (((r2_xboole_0 @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 0.24/0.50      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.24/0.50  thf('14', plain, (((sk_A) != (sk_B))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('15', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.24/0.50      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.24/0.50  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
