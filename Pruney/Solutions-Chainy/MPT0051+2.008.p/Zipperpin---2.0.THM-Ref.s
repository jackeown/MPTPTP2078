%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uN1uXwJayC

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  24 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 137 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t44_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
       => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    $false ),
    inference(demod,[status(thm)],['0','8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uN1uXwJayC
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 7 iterations in 0.010s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(t44_xboole_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.21/0.47       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.21/0.47          ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t44_xboole_1])).
% 0.21/0.47  thf('0', plain, (~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(l32_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i, X2 : $i]:
% 0.21/0.47         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(t41_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.47       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.47         ((k4_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ X5)
% 0.21/0.47           = (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 0.21/0.47          | (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.47        | (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.47  thf('8', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.47  thf('9', plain, ($false), inference('demod', [status(thm)], ['0', '8'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
