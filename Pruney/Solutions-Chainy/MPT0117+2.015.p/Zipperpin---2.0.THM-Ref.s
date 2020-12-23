%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K8sICbIVAy

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:49 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   28 (  36 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  156 ( 228 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t110_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ B ) )
       => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t110_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('2',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ X1 ) @ sk_B )
      | ~ ( r1_tarski @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X1 ) @ ( k4_xboole_0 @ sk_C @ X0 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup+',[status(thm)],['1','12'])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['0','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K8sICbIVAy
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:39:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.28/1.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.28/1.50  % Solved by: fo/fo7.sh
% 1.28/1.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.28/1.50  % done 466 iterations in 1.045s
% 1.28/1.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.28/1.50  % SZS output start Refutation
% 1.28/1.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.28/1.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.28/1.50  thf(sk_C_type, type, sk_C: $i).
% 1.28/1.50  thf(sk_A_type, type, sk_A: $i).
% 1.28/1.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.28/1.50  thf(sk_B_type, type, sk_B: $i).
% 1.28/1.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.28/1.50  thf(t110_xboole_1, conjecture,
% 1.28/1.50    (![A:$i,B:$i,C:$i]:
% 1.28/1.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.28/1.50       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.28/1.50  thf(zf_stmt_0, negated_conjecture,
% 1.28/1.50    (~( ![A:$i,B:$i,C:$i]:
% 1.28/1.50        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.28/1.50          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 1.28/1.50    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 1.28/1.50  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 1.28/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.50  thf(d6_xboole_0, axiom,
% 1.28/1.50    (![A:$i,B:$i]:
% 1.28/1.50     ( ( k5_xboole_0 @ A @ B ) =
% 1.28/1.50       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.28/1.50  thf('1', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         ((k5_xboole_0 @ X0 @ X1)
% 1.28/1.50           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.28/1.50      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.28/1.50  thf('2', plain, ((r1_tarski @ sk_C @ sk_B)),
% 1.28/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.50  thf(t36_xboole_1, axiom,
% 1.28/1.50    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.28/1.50  thf('3', plain,
% 1.28/1.50      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 1.28/1.50      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.28/1.50  thf(t1_xboole_1, axiom,
% 1.28/1.50    (![A:$i,B:$i,C:$i]:
% 1.28/1.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.28/1.50       ( r1_tarski @ A @ C ) ))).
% 1.28/1.50  thf('4', plain,
% 1.28/1.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.28/1.50         (~ (r1_tarski @ X2 @ X3)
% 1.28/1.50          | ~ (r1_tarski @ X3 @ X4)
% 1.28/1.50          | (r1_tarski @ X2 @ X4))),
% 1.28/1.50      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.28/1.50  thf('5', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.50         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 1.28/1.50      inference('sup-', [status(thm)], ['3', '4'])).
% 1.28/1.50  thf('6', plain, (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C @ X0) @ sk_B)),
% 1.28/1.50      inference('sup-', [status(thm)], ['2', '5'])).
% 1.28/1.50  thf('7', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.28/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.50  thf('8', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.50         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 1.28/1.50      inference('sup-', [status(thm)], ['3', '4'])).
% 1.28/1.50  thf('9', plain, (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B)),
% 1.28/1.50      inference('sup-', [status(thm)], ['7', '8'])).
% 1.28/1.50  thf(t8_xboole_1, axiom,
% 1.28/1.50    (![A:$i,B:$i,C:$i]:
% 1.28/1.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.28/1.50       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.28/1.50  thf('10', plain,
% 1.28/1.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.28/1.50         (~ (r1_tarski @ X7 @ X8)
% 1.28/1.50          | ~ (r1_tarski @ X9 @ X8)
% 1.28/1.50          | (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 1.28/1.50      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.28/1.50  thf('11', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         ((r1_tarski @ (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ X1) @ sk_B)
% 1.28/1.50          | ~ (r1_tarski @ X1 @ sk_B))),
% 1.28/1.50      inference('sup-', [status(thm)], ['9', '10'])).
% 1.28/1.50  thf('12', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         (r1_tarski @ 
% 1.28/1.50          (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X1) @ (k4_xboole_0 @ sk_C @ X0)) @ 
% 1.28/1.50          sk_B)),
% 1.28/1.50      inference('sup-', [status(thm)], ['6', '11'])).
% 1.28/1.50  thf('13', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 1.28/1.50      inference('sup+', [status(thm)], ['1', '12'])).
% 1.28/1.50  thf('14', plain, ($false), inference('demod', [status(thm)], ['0', '13'])).
% 1.28/1.50  
% 1.28/1.50  % SZS output end Refutation
% 1.28/1.50  
% 1.34/1.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
