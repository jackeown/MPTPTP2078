%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lXJq7ek179

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:15 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   55 (  58 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  379 ( 399 expanded)
%              Number of equality atoms :   47 (  49 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ( ( k4_xboole_0 @ X6 @ X5 )
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('13',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','19'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lXJq7ek179
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:09:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 378 iterations in 0.141s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(t100_xboole_1, conjecture,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i,B:$i]:
% 0.41/0.59        ( ( k4_xboole_0 @ A @ B ) =
% 0.41/0.59          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.41/0.59         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t47_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      (![X14 : $i, X15 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.41/0.59           = (k4_xboole_0 @ X14 @ X15))),
% 0.41/0.59      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.41/0.59  thf(t98_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (![X23 : $i, X24 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ X23 @ X24)
% 0.41/0.59           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.41/0.59           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['1', '2'])).
% 0.41/0.59  thf(t48_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      (![X16 : $i, X17 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.41/0.59           = (k3_xboole_0 @ X16 @ X17))),
% 0.41/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.59  thf(t36_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.41/0.59      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.41/0.59      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf(l32_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (![X2 : $i, X4 : $i]:
% 0.41/0.59         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.59  thf(t40_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      (![X9 : $i, X10 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 0.41/0.59           = (k4_xboole_0 @ X9 @ X10))),
% 0.41/0.59      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.41/0.59  thf(t32_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.41/0.59       ( ( A ) = ( B ) ) ))).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      (![X5 : $i, X6 : $i]:
% 0.41/0.59         (((X6) = (X5)) | ((k4_xboole_0 @ X6 @ X5) != (k4_xboole_0 @ X5 @ X6)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.41/0.59            != (k4_xboole_0 @ X1 @ X0))
% 0.41/0.59          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.41/0.59      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      (![X2 : $i, X4 : $i]:
% 0.41/0.59         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.59  thf(t41_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.41/0.59       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.41/0.59           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (((k1_xboole_0) != (k4_xboole_0 @ X1 @ X0))
% 0.41/0.59          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['11', '16'])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (((k1_xboole_0) != (k1_xboole_0))
% 0.41/0.59          | ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['8', '17'])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((X1)
% 0.41/0.59           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['3', '19'])).
% 0.41/0.59  thf(t92_xboole_1, axiom,
% 0.41/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.41/0.59  thf('21', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.41/0.59      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.41/0.59  thf(t91_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.41/0.59       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.41/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.41/0.59           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.59           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['21', '22'])).
% 0.41/0.59  thf(commutativity_k5_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.41/0.59  thf(t5_boole, axiom,
% 0.41/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.59  thf('25', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.41/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.41/0.59  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['24', '25'])).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['23', '26'])).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.41/0.59           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['20', '27'])).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.41/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.41/0.59      inference('demod', [status(thm)], ['28', '29'])).
% 0.41/0.59  thf('31', plain,
% 0.41/0.59      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['0', '30'])).
% 0.41/0.59  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.44/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
