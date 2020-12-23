%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JaNN8iPKuq

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:49 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  188 ( 232 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ sk_C ) @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup+',[status(thm)],['3','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JaNN8iPKuq
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:55:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.72/1.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.72/1.96  % Solved by: fo/fo7.sh
% 1.72/1.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.72/1.96  % done 2737 iterations in 1.497s
% 1.72/1.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.72/1.96  % SZS output start Refutation
% 1.72/1.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.72/1.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.72/1.96  thf(sk_A_type, type, sk_A: $i).
% 1.72/1.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.72/1.96  thf(sk_C_type, type, sk_C: $i).
% 1.72/1.96  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.72/1.96  thf(sk_B_type, type, sk_B: $i).
% 1.72/1.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.72/1.96  thf(t110_xboole_1, conjecture,
% 1.72/1.96    (![A:$i,B:$i,C:$i]:
% 1.72/1.96     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.72/1.96       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.72/1.96  thf(zf_stmt_0, negated_conjecture,
% 1.72/1.96    (~( ![A:$i,B:$i,C:$i]:
% 1.72/1.96        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.72/1.96          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 1.72/1.96    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 1.72/1.96  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf(t12_xboole_1, axiom,
% 1.72/1.96    (![A:$i,B:$i]:
% 1.72/1.96     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.72/1.96  thf('2', plain,
% 1.72/1.96      (![X4 : $i, X5 : $i]:
% 1.72/1.96         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 1.72/1.96      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.72/1.96  thf('3', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 1.72/1.96      inference('sup-', [status(thm)], ['1', '2'])).
% 1.72/1.96  thf('4', plain, ((r1_tarski @ sk_C @ sk_B)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf(l98_xboole_1, axiom,
% 1.72/1.96    (![A:$i,B:$i]:
% 1.72/1.96     ( ( k5_xboole_0 @ A @ B ) =
% 1.72/1.96       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.72/1.96  thf('5', plain,
% 1.72/1.96      (![X0 : $i, X1 : $i]:
% 1.72/1.96         ((k5_xboole_0 @ X0 @ X1)
% 1.72/1.96           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 1.72/1.96      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.72/1.96  thf(t36_xboole_1, axiom,
% 1.72/1.96    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.72/1.96  thf('6', plain,
% 1.72/1.96      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 1.72/1.96      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.72/1.96  thf('7', plain,
% 1.72/1.96      (![X0 : $i, X1 : $i]:
% 1.72/1.96         (r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 1.72/1.96      inference('sup+', [status(thm)], ['5', '6'])).
% 1.72/1.96  thf(t43_xboole_1, axiom,
% 1.72/1.96    (![A:$i,B:$i,C:$i]:
% 1.72/1.96     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.72/1.96       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.72/1.96  thf('8', plain,
% 1.72/1.96      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.72/1.96         ((r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.72/1.96          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.72/1.96      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.72/1.96  thf('9', plain,
% 1.72/1.96      (![X0 : $i, X1 : $i]:
% 1.72/1.96         (r1_tarski @ (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 1.72/1.96      inference('sup-', [status(thm)], ['7', '8'])).
% 1.72/1.96  thf(t1_xboole_1, axiom,
% 1.72/1.96    (![A:$i,B:$i,C:$i]:
% 1.72/1.96     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.72/1.96       ( r1_tarski @ A @ C ) ))).
% 1.72/1.96  thf('10', plain,
% 1.72/1.96      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.72/1.96         (~ (r1_tarski @ X6 @ X7)
% 1.72/1.96          | ~ (r1_tarski @ X7 @ X8)
% 1.72/1.96          | (r1_tarski @ X6 @ X8))),
% 1.72/1.96      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.72/1.96  thf('11', plain,
% 1.72/1.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.96         ((r1_tarski @ (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1) @ X2)
% 1.72/1.96          | ~ (r1_tarski @ X0 @ X2))),
% 1.72/1.96      inference('sup-', [status(thm)], ['9', '10'])).
% 1.72/1.96  thf('12', plain,
% 1.72/1.96      (![X0 : $i]:
% 1.72/1.96         (r1_tarski @ (k4_xboole_0 @ (k5_xboole_0 @ X0 @ sk_C) @ X0) @ sk_B)),
% 1.72/1.96      inference('sup-', [status(thm)], ['4', '11'])).
% 1.72/1.96  thf(t44_xboole_1, axiom,
% 1.72/1.96    (![A:$i,B:$i,C:$i]:
% 1.72/1.96     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.72/1.96       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.72/1.96  thf('13', plain,
% 1.72/1.96      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.72/1.96         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 1.72/1.96          | ~ (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16))),
% 1.72/1.96      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.72/1.96  thf('14', plain,
% 1.72/1.96      (![X0 : $i]:
% 1.72/1.96         (r1_tarski @ (k5_xboole_0 @ X0 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 1.72/1.96      inference('sup-', [status(thm)], ['12', '13'])).
% 1.72/1.96  thf('15', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 1.72/1.96      inference('sup+', [status(thm)], ['3', '14'])).
% 1.72/1.96  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 1.72/1.96  
% 1.72/1.96  % SZS output end Refutation
% 1.72/1.96  
% 1.72/1.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
