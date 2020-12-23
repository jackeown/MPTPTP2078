%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Ny2slzMTa

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:10 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   38 (  40 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  230 ( 244 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t100_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t100_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k4_xboole_0 @ X44 @ ( k3_xboole_0 @ X44 @ X45 ) )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k4_xboole_0 @ X46 @ ( k4_xboole_0 @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X25: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X27 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X17: $i] :
      ( ( k2_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','11','12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','16'])).

thf('18',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Ny2slzMTa
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:02:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 1.04/1.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.04/1.20  % Solved by: fo/fo7.sh
% 1.04/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.20  % done 1774 iterations in 0.761s
% 1.04/1.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.04/1.20  % SZS output start Refutation
% 1.04/1.20  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.04/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.04/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.04/1.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.04/1.20  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.04/1.20  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.04/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.20  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.04/1.20  thf(t100_xboole_1, conjecture,
% 1.04/1.20    (![A:$i,B:$i]:
% 1.04/1.20     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.04/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.20    (~( ![A:$i,B:$i]:
% 1.04/1.20        ( ( k4_xboole_0 @ A @ B ) =
% 1.04/1.20          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 1.04/1.20    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 1.04/1.20  thf('0', plain,
% 1.04/1.20      (((k4_xboole_0 @ sk_A @ sk_B)
% 1.04/1.20         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.04/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.20  thf(commutativity_k3_xboole_0, axiom,
% 1.04/1.20    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.04/1.20  thf('1', plain,
% 1.04/1.20      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.04/1.20      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.04/1.20  thf('2', plain,
% 1.04/1.20      (((k4_xboole_0 @ sk_A @ sk_B)
% 1.04/1.20         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.04/1.20      inference('demod', [status(thm)], ['0', '1'])).
% 1.04/1.20  thf('3', plain,
% 1.04/1.20      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.04/1.20      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.04/1.20  thf(t47_xboole_1, axiom,
% 1.04/1.20    (![A:$i,B:$i]:
% 1.04/1.20     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.04/1.20  thf('4', plain,
% 1.04/1.20      (![X44 : $i, X45 : $i]:
% 1.04/1.20         ((k4_xboole_0 @ X44 @ (k3_xboole_0 @ X44 @ X45))
% 1.04/1.20           = (k4_xboole_0 @ X44 @ X45))),
% 1.04/1.20      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.04/1.20  thf(d6_xboole_0, axiom,
% 1.04/1.20    (![A:$i,B:$i]:
% 1.04/1.20     ( ( k5_xboole_0 @ A @ B ) =
% 1.04/1.20       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.04/1.20  thf('5', plain,
% 1.04/1.20      (![X4 : $i, X5 : $i]:
% 1.04/1.20         ((k5_xboole_0 @ X4 @ X5)
% 1.04/1.20           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 1.04/1.20      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.04/1.20  thf('6', plain,
% 1.04/1.20      (![X0 : $i, X1 : $i]:
% 1.04/1.20         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.04/1.20           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.04/1.20              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 1.04/1.20      inference('sup+', [status(thm)], ['4', '5'])).
% 1.04/1.20  thf(t48_xboole_1, axiom,
% 1.04/1.20    (![A:$i,B:$i]:
% 1.04/1.20     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.04/1.20  thf('7', plain,
% 1.04/1.20      (![X46 : $i, X47 : $i]:
% 1.04/1.20         ((k4_xboole_0 @ X46 @ (k4_xboole_0 @ X46 @ X47))
% 1.04/1.20           = (k3_xboole_0 @ X46 @ X47))),
% 1.04/1.20      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.04/1.20  thf(t36_xboole_1, axiom,
% 1.04/1.20    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.04/1.20  thf('8', plain,
% 1.04/1.20      (![X23 : $i, X24 : $i]: (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X23)),
% 1.04/1.20      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.04/1.20  thf('9', plain,
% 1.04/1.20      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.04/1.20      inference('sup+', [status(thm)], ['7', '8'])).
% 1.04/1.20  thf(t37_xboole_1, axiom,
% 1.04/1.20    (![A:$i,B:$i]:
% 1.04/1.20     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.04/1.20  thf('10', plain,
% 1.04/1.20      (![X25 : $i, X27 : $i]:
% 1.04/1.20         (((k4_xboole_0 @ X25 @ X27) = (k1_xboole_0))
% 1.04/1.20          | ~ (r1_tarski @ X25 @ X27))),
% 1.04/1.20      inference('cnf', [status(esa)], [t37_xboole_1])).
% 1.04/1.20  thf('11', plain,
% 1.04/1.20      (![X0 : $i, X1 : $i]:
% 1.04/1.20         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.04/1.20      inference('sup-', [status(thm)], ['9', '10'])).
% 1.04/1.20  thf(commutativity_k2_xboole_0, axiom,
% 1.04/1.20    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.04/1.20  thf('12', plain,
% 1.04/1.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.04/1.20      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.04/1.20  thf('13', plain,
% 1.04/1.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.04/1.20      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.04/1.20  thf(t1_boole, axiom,
% 1.04/1.20    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.04/1.20  thf('14', plain, (![X17 : $i]: ((k2_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.04/1.20      inference('cnf', [status(esa)], [t1_boole])).
% 1.04/1.20  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.04/1.20      inference('sup+', [status(thm)], ['13', '14'])).
% 1.04/1.20  thf('16', plain,
% 1.04/1.20      (![X0 : $i, X1 : $i]:
% 1.04/1.20         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.04/1.20           = (k4_xboole_0 @ X1 @ X0))),
% 1.04/1.20      inference('demod', [status(thm)], ['6', '11', '12', '15'])).
% 1.04/1.20  thf('17', plain,
% 1.04/1.20      (![X0 : $i, X1 : $i]:
% 1.04/1.20         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.04/1.20           = (k4_xboole_0 @ X0 @ X1))),
% 1.04/1.20      inference('sup+', [status(thm)], ['3', '16'])).
% 1.04/1.20  thf('18', plain,
% 1.04/1.20      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.04/1.20      inference('demod', [status(thm)], ['2', '17'])).
% 1.04/1.20  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 1.04/1.20  
% 1.04/1.20  % SZS output end Refutation
% 1.04/1.20  
% 1.04/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
