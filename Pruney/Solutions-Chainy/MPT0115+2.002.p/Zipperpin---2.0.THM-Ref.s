%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hLn8ixMhXr

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   30 (  34 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  138 ( 168 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t108_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t108_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','9','10'])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k2_xboole_0 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['0','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hLn8ixMhXr
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:40:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 38 iterations in 0.021s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(t108_xboole_1, conjecture,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.47        ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t108_xboole_1])).
% 0.19/0.47  thf('0', plain, (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(l32_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X2 : $i, X4 : $i]:
% 0.19/0.47         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.19/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.47  thf('3', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.47  thf(t39_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X9 : $i, X10 : $i]:
% 0.19/0.47         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.19/0.47           = (k2_xboole_0 @ X9 @ X10))),
% 0.19/0.47      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.47      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.47  thf(commutativity_k2_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.47  thf(t1_boole, axiom,
% 0.19/0.47    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.47  thf('8', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.19/0.47      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.47  thf('9', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.47  thf('11', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['5', '6', '9', '10'])).
% 0.19/0.47  thf(t29_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.47         (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ (k2_xboole_0 @ X6 @ X8))),
% 0.19/0.47      inference('cnf', [status(esa)], [t29_xboole_1])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.19/0.47      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.47  thf('14', plain, ($false), inference('demod', [status(thm)], ['0', '13'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
