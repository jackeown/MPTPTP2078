%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vvpQDeEIL5

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:47 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   42 (  49 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  289 ( 362 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t82_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) )
        = ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) )
     => ( r3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) )
          = ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) )
       => ( r3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t82_zfmisc_1])).

thf('0',plain,(
    ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X19 )
      | ( X19
       != ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
    = ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r1_tarski @ X20 @ X18 )
      | ( X19
       != ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_tarski @ X20 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_tarski @ X20 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('15',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X14 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('17',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X14 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        | ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r3_xboole_0 @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('23',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r3_xboole_0 @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('25',plain,(
    r3_xboole_0 @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vvpQDeEIL5
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:41:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 308 iterations in 0.133s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(r3_xboole_0_type, type, r3_xboole_0: $i > $i > $o).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(t82_zfmisc_1, conjecture,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) =
% 0.40/0.58         ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) =>
% 0.40/0.58       ( r3_xboole_0 @ A @ B ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i]:
% 0.40/0.58        ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) =
% 0.40/0.58            ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) =>
% 0.40/0.58          ( r3_xboole_0 @ A @ B ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t82_zfmisc_1])).
% 0.40/0.58  thf('0', plain, (~ (r3_xboole_0 @ sk_A @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(d10_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.58  thf('2', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.40/0.58      inference('simplify', [status(thm)], ['1'])).
% 0.40/0.58  thf(d1_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.40/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.58         (~ (r1_tarski @ X17 @ X18)
% 0.40/0.58          | (r2_hidden @ X17 @ X19)
% 0.40/0.58          | ((X19) != (k1_zfmisc_1 @ X18)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (![X17 : $i, X18 : $i]:
% 0.40/0.58         ((r2_hidden @ X17 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X17 @ X18))),
% 0.40/0.58      inference('simplify', [status(thm)], ['3'])).
% 0.40/0.58  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['2', '4'])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (((k2_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.40/0.58         = (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(d3_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.40/0.58       ( ![D:$i]:
% 0.40/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.58           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X6 @ X4)
% 0.40/0.58          | (r2_hidden @ X6 @ X5)
% 0.40/0.58          | (r2_hidden @ X6 @ X3)
% 0.40/0.58          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.40/0.58         ((r2_hidden @ X6 @ X3)
% 0.40/0.58          | (r2_hidden @ X6 @ X5)
% 0.40/0.58          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['7'])).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))
% 0.40/0.58          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.58          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['6', '8'])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (((r2_hidden @ (k2_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))
% 0.40/0.58        | (r2_hidden @ (k2_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '9'])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X20 @ X19)
% 0.40/0.58          | (r1_tarski @ X20 @ X18)
% 0.40/0.58          | ((X19) != (k1_zfmisc_1 @ X18)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X18 : $i, X20 : $i]:
% 0.40/0.58         ((r1_tarski @ X20 @ X18) | ~ (r2_hidden @ X20 @ (k1_zfmisc_1 @ X18)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (((r2_hidden @ (k2_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.58        | (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['10', '12'])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X18 : $i, X20 : $i]:
% 0.40/0.58         ((r1_tarski @ X20 @ X18) | ~ (r2_hidden @ X20 @ (k1_zfmisc_1 @ X18)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.40/0.58        | (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.58  thf(t11_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.58         ((r1_tarski @ X14 @ X15)
% 0.40/0.58          | ~ (r1_tarski @ (k2_xboole_0 @ X14 @ X16) @ X15))),
% 0.40/0.58      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 0.40/0.58        | (r1_tarski @ sk_A @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.58  thf(commutativity_k2_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.58         ((r1_tarski @ X14 @ X15)
% 0.40/0.58          | ~ (r1_tarski @ (k2_xboole_0 @ X14 @ X16) @ X15))),
% 0.40/0.58      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 0.40/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.58  thf('21', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_B @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['17', '20'])).
% 0.40/0.58  thf(d9_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r3_xboole_0 @ A @ B ) <=>
% 0.40/0.58       ( ( r1_tarski @ A @ B ) | ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      (![X12 : $i, X13 : $i]:
% 0.40/0.58         ((r3_xboole_0 @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.40/0.58      inference('cnf', [status(esa)], [d9_xboole_0])).
% 0.40/0.58  thf('23', plain, (((r1_tarski @ sk_A @ sk_B) | (r3_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X12 : $i, X13 : $i]:
% 0.40/0.58         ((r3_xboole_0 @ X12 @ X13) | ~ (r1_tarski @ X12 @ X13))),
% 0.40/0.58      inference('cnf', [status(esa)], [d9_xboole_0])).
% 0.40/0.58  thf('25', plain, ((r3_xboole_0 @ sk_A @ sk_B)),
% 0.40/0.58      inference('clc', [status(thm)], ['23', '24'])).
% 0.40/0.58  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
