%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Vs22xVC4j

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:53 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  270 ( 293 expanded)
%              Number of equality atoms :   27 (  30 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t93_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t93_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k2_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Vs22xVC4j
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.60/1.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.60/1.79  % Solved by: fo/fo7.sh
% 1.60/1.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.60/1.79  % done 1575 iterations in 1.333s
% 1.60/1.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.60/1.79  % SZS output start Refutation
% 1.60/1.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.60/1.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.60/1.79  thf(sk_B_type, type, sk_B: $i).
% 1.60/1.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.60/1.79  thf(sk_A_type, type, sk_A: $i).
% 1.60/1.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.60/1.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.60/1.79  thf(t93_xboole_1, conjecture,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( k2_xboole_0 @ A @ B ) =
% 1.60/1.79       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.60/1.79  thf(zf_stmt_0, negated_conjecture,
% 1.60/1.79    (~( ![A:$i,B:$i]:
% 1.60/1.79        ( ( k2_xboole_0 @ A @ B ) =
% 1.60/1.79          ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 1.60/1.79    inference('cnf.neg', [status(esa)], [t93_xboole_1])).
% 1.60/1.79  thf('0', plain,
% 1.60/1.79      (((k2_xboole_0 @ sk_A @ sk_B)
% 1.60/1.79         != (k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 1.60/1.79             (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf(d6_xboole_0, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( k5_xboole_0 @ A @ B ) =
% 1.60/1.79       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.60/1.79  thf('1', plain,
% 1.60/1.79      (![X2 : $i, X3 : $i]:
% 1.60/1.79         ((k5_xboole_0 @ X2 @ X3)
% 1.60/1.79           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 1.60/1.79      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.60/1.79  thf(t47_xboole_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.60/1.79  thf('2', plain,
% 1.60/1.79      (![X13 : $i, X14 : $i]:
% 1.60/1.79         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 1.60/1.79           = (k4_xboole_0 @ X13 @ X14))),
% 1.60/1.79      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.60/1.79  thf(t39_xboole_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.60/1.79  thf('3', plain,
% 1.60/1.79      (![X8 : $i, X9 : $i]:
% 1.60/1.79         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 1.60/1.79           = (k2_xboole_0 @ X8 @ X9))),
% 1.60/1.79      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.60/1.79  thf('4', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i]:
% 1.60/1.79         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.60/1.79           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.60/1.79      inference('sup+', [status(thm)], ['2', '3'])).
% 1.60/1.79  thf(commutativity_k2_xboole_0, axiom,
% 1.60/1.79    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.60/1.79  thf('5', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.60/1.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.60/1.79  thf('6', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i]:
% 1.60/1.79         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.60/1.79           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.60/1.79      inference('demod', [status(thm)], ['4', '5'])).
% 1.60/1.79  thf(t17_xboole_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.60/1.79  thf('7', plain,
% 1.60/1.79      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 1.60/1.79      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.60/1.79  thf(t12_xboole_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.60/1.79  thf('8', plain,
% 1.60/1.79      (![X4 : $i, X5 : $i]:
% 1.60/1.79         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 1.60/1.79      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.60/1.79  thf('9', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i]:
% 1.60/1.79         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.60/1.79      inference('sup-', [status(thm)], ['7', '8'])).
% 1.60/1.79  thf('10', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.60/1.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.60/1.79  thf('11', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i]:
% 1.60/1.79         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 1.60/1.79      inference('demod', [status(thm)], ['9', '10'])).
% 1.60/1.79  thf('12', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i]:
% 1.60/1.79         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.60/1.79           = (X1))),
% 1.60/1.79      inference('demod', [status(thm)], ['6', '11'])).
% 1.60/1.79  thf(t4_xboole_1, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i]:
% 1.60/1.79     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.60/1.79       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.60/1.79  thf('13', plain,
% 1.60/1.79      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.60/1.79         ((k2_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X19)
% 1.60/1.79           = (k2_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 1.60/1.79      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.60/1.79  thf('14', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.79         ((k2_xboole_0 @ X0 @ X1)
% 1.60/1.79           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ 
% 1.60/1.79              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)))),
% 1.60/1.79      inference('sup+', [status(thm)], ['12', '13'])).
% 1.60/1.79  thf('15', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i]:
% 1.60/1.79         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 1.60/1.79           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 1.60/1.79      inference('sup+', [status(thm)], ['1', '14'])).
% 1.60/1.79  thf('16', plain,
% 1.60/1.79      (![X8 : $i, X9 : $i]:
% 1.60/1.79         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 1.60/1.79           = (k2_xboole_0 @ X8 @ X9))),
% 1.60/1.79      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.60/1.79  thf('17', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.60/1.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.60/1.79  thf('18', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i]:
% 1.60/1.79         ((k2_xboole_0 @ X1 @ X0)
% 1.60/1.79           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.60/1.79      inference('demod', [status(thm)], ['15', '16', '17'])).
% 1.60/1.79  thf('19', plain,
% 1.60/1.79      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 1.60/1.79      inference('demod', [status(thm)], ['0', '18'])).
% 1.60/1.79  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 1.60/1.79  
% 1.60/1.79  % SZS output end Refutation
% 1.60/1.79  
% 1.60/1.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
