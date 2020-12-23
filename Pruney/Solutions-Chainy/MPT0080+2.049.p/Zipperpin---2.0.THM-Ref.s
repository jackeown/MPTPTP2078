%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aibayxIji0

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:10 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  193 ( 237 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      | ~ ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ~ ( r1_xboole_0 @ X27 @ X28 )
      | ( r1_xboole_0 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['3','8'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ( ( k4_xboole_0 @ X18 @ X19 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aibayxIji0
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 234 iterations in 0.092s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(t73_xboole_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.37/0.55       ( r1_tarski @ A @ B ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.55        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.37/0.55            ( r1_xboole_0 @ A @ C ) ) =>
% 0.37/0.55          ( r1_tarski @ A @ B ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.37/0.55  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(symmetry_r1_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X3 : $i, X4 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.55  thf('3', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf('4', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t43_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.37/0.55       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.55         ((r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 0.37/0.55          | ~ (r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.37/0.55  thf('6', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.55  thf(t63_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.37/0.55       ( r1_xboole_0 @ A @ C ) ))).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.55         (~ (r1_tarski @ X26 @ X27)
% 0.37/0.55          | ~ (r1_xboole_0 @ X27 @ X28)
% 0.37/0.55          | (r1_xboole_0 @ X26 @ X28))),
% 0.37/0.55      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.37/0.55          | ~ (r1_xboole_0 @ sk_C @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.55  thf('9', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['3', '8'])).
% 0.37/0.55  thf(d7_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.37/0.55       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.55  thf(t36_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.37/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.55  thf(t28_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X13 : $i, X14 : $i]:
% 0.37/0.55         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.37/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.37/0.55           = (k4_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.55  thf('15', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['11', '14'])).
% 0.37/0.55  thf(t37_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i]:
% 0.37/0.55         ((r1_tarski @ X18 @ X19)
% 0.37/0.55          | ((k4_xboole_0 @ X18 @ X19) != (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf('18', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.37/0.55      inference('simplify', [status(thm)], ['17'])).
% 0.37/0.55  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.40/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
