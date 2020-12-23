%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NMQMSDyPjW

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:11 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  184 ( 228 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('6',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 )
      | ( r1_xboole_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('13',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NMQMSDyPjW
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 411 iterations in 0.162s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.62  thf(t73_xboole_1, conjecture,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.40/0.62       ( r1_tarski @ A @ B ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.62        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.40/0.62            ( r1_xboole_0 @ A @ C ) ) =>
% 0.40/0.62          ( r1_tarski @ A @ B ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.40/0.62  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(symmetry_r1_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      (![X1 : $i, X2 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ X1 @ X2) | ~ (r1_xboole_0 @ X2 @ X1))),
% 0.40/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.40/0.62  thf('3', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.40/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.62  thf('4', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(t43_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.40/0.62       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.40/0.62  thf('5', plain,
% 0.40/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.62         ((r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.40/0.62          | ~ (r1_tarski @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.40/0.62  thf('6', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.40/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.62  thf(t63_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.40/0.62       ( r1_xboole_0 @ A @ C ) ))).
% 0.40/0.62  thf('7', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.62         (~ (r1_tarski @ X11 @ X12)
% 0.40/0.62          | ~ (r1_xboole_0 @ X12 @ X13)
% 0.40/0.62          | (r1_xboole_0 @ X11 @ X13))),
% 0.40/0.62      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.40/0.62  thf('8', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.40/0.62          | ~ (r1_xboole_0 @ sk_C @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.62  thf('9', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)),
% 0.40/0.62      inference('sup-', [status(thm)], ['3', '8'])).
% 0.40/0.62  thf(t69_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.62       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.40/0.62  thf('10', plain,
% 0.40/0.62      (![X14 : $i, X15 : $i]:
% 0.40/0.62         (~ (r1_xboole_0 @ X14 @ X15)
% 0.40/0.62          | ~ (r1_tarski @ X14 @ X15)
% 0.40/0.62          | (v1_xboole_0 @ X14))),
% 0.40/0.62      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      (((v1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.40/0.62        | ~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 0.40/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.62  thf(t36_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.40/0.62  thf('12', plain,
% 0.40/0.62      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.40/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.40/0.62  thf('13', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['11', '12'])).
% 0.40/0.62  thf(l13_xboole_0, axiom,
% 0.40/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.40/0.62  thf('15', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.62  thf(l32_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.62  thf('16', plain,
% 0.40/0.62      (![X3 : $i, X4 : $i]:
% 0.40/0.62         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.40/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.62  thf('18', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.40/0.62      inference('simplify', [status(thm)], ['17'])).
% 0.40/0.62  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.40/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
