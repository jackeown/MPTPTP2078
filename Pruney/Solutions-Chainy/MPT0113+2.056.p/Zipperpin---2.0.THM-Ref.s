%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dc3PcAfGyY

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:36 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  208 ( 316 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','14'])).

thf('16',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['15','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dc3PcAfGyY
% 0.11/0.33  % Computer   : n022.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 18:37:11 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.18/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.47  % Solved by: fo/fo7.sh
% 0.18/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.47  % done 57 iterations in 0.036s
% 0.18/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.47  % SZS output start Refutation
% 0.18/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.18/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.18/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.47  thf(t106_xboole_1, conjecture,
% 0.18/0.47    (![A:$i,B:$i,C:$i]:
% 0.18/0.47     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.18/0.47       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.18/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.18/0.47        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.18/0.47          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.18/0.47    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.18/0.47  thf('0', plain,
% 0.18/0.47      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf('1', plain,
% 0.18/0.47      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.18/0.47      inference('split', [status(esa)], ['0'])).
% 0.18/0.47  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf(t36_xboole_1, axiom,
% 0.18/0.47    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.18/0.47  thf('3', plain,
% 0.18/0.47      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.18/0.47      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.18/0.47  thf(t28_xboole_1, axiom,
% 0.18/0.47    (![A:$i,B:$i]:
% 0.18/0.47     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.18/0.47  thf('4', plain,
% 0.18/0.47      (![X7 : $i, X8 : $i]:
% 0.18/0.47         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.18/0.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.18/0.47  thf('5', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i]:
% 0.18/0.47         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.18/0.47           = (k4_xboole_0 @ X0 @ X1))),
% 0.18/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.18/0.47  thf(commutativity_k3_xboole_0, axiom,
% 0.18/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.18/0.47  thf('6', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.18/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.18/0.47  thf('7', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i]:
% 0.18/0.47         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.18/0.47           = (k4_xboole_0 @ X0 @ X1))),
% 0.18/0.47      inference('demod', [status(thm)], ['5', '6'])).
% 0.18/0.47  thf(t18_xboole_1, axiom,
% 0.18/0.47    (![A:$i,B:$i,C:$i]:
% 0.18/0.47     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.18/0.47  thf('8', plain,
% 0.18/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.18/0.47         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.18/0.47      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.18/0.47  thf('9', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.47         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 0.18/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.18/0.47  thf('10', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.18/0.47      inference('sup-', [status(thm)], ['2', '9'])).
% 0.18/0.47  thf('11', plain,
% 0.18/0.47      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.18/0.47      inference('split', [status(esa)], ['0'])).
% 0.18/0.47  thf('12', plain, (((r1_tarski @ sk_A @ sk_B))),
% 0.18/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.18/0.47  thf('13', plain,
% 0.18/0.47      (~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_tarski @ sk_A @ sk_B))),
% 0.18/0.47      inference('split', [status(esa)], ['0'])).
% 0.18/0.47  thf('14', plain, (~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.18/0.47      inference('sat_resolution*', [status(thm)], ['12', '13'])).
% 0.18/0.47  thf('15', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.18/0.47      inference('simpl_trail', [status(thm)], ['1', '14'])).
% 0.18/0.47  thf('16', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf('17', plain,
% 0.18/0.47      (![X7 : $i, X8 : $i]:
% 0.18/0.47         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.18/0.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.18/0.47  thf('18', plain,
% 0.18/0.47      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.18/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.18/0.47  thf(t49_xboole_1, axiom,
% 0.18/0.47    (![A:$i,B:$i,C:$i]:
% 0.18/0.47     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.18/0.47       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.18/0.47  thf('19', plain,
% 0.18/0.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.18/0.47         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.18/0.47           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.18/0.47      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.18/0.47  thf(t79_xboole_1, axiom,
% 0.18/0.47    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.18/0.47  thf('20', plain,
% 0.18/0.47      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 0.18/0.47      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.18/0.47  thf('21', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.47         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 0.18/0.47      inference('sup+', [status(thm)], ['19', '20'])).
% 0.18/0.47  thf('22', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.18/0.47      inference('sup+', [status(thm)], ['18', '21'])).
% 0.18/0.47  thf('23', plain, ($false), inference('demod', [status(thm)], ['15', '22'])).
% 0.18/0.47  
% 0.18/0.47  % SZS output end Refutation
% 0.18/0.47  
% 0.18/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
