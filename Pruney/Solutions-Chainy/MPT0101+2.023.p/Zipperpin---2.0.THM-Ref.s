%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g0vBvhHAYh

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:57 EST 2020

% Result     : Theorem 45.40s
% Output     : Refutation 45.40s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 104 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  485 ( 865 expanded)
%              Number of equality atoms :   47 (  81 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t94_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','38'])).

thf('40',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g0vBvhHAYh
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:47:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 45.40/45.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 45.40/45.58  % Solved by: fo/fo7.sh
% 45.40/45.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 45.40/45.58  % done 17073 iterations in 45.129s
% 45.40/45.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 45.40/45.58  % SZS output start Refutation
% 45.40/45.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 45.40/45.58  thf(sk_A_type, type, sk_A: $i).
% 45.40/45.58  thf(sk_B_type, type, sk_B: $i).
% 45.40/45.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 45.40/45.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 45.40/45.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 45.40/45.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 45.40/45.58  thf(t94_xboole_1, conjecture,
% 45.40/45.58    (![A:$i,B:$i]:
% 45.40/45.58     ( ( k2_xboole_0 @ A @ B ) =
% 45.40/45.58       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 45.40/45.58  thf(zf_stmt_0, negated_conjecture,
% 45.40/45.58    (~( ![A:$i,B:$i]:
% 45.40/45.58        ( ( k2_xboole_0 @ A @ B ) =
% 45.40/45.58          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 45.40/45.58    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 45.40/45.58  thf('0', plain,
% 45.40/45.58      (((k2_xboole_0 @ sk_A @ sk_B)
% 45.40/45.58         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 45.40/45.58             (k3_xboole_0 @ sk_A @ sk_B)))),
% 45.40/45.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.40/45.58  thf(d6_xboole_0, axiom,
% 45.40/45.58    (![A:$i,B:$i]:
% 45.40/45.58     ( ( k5_xboole_0 @ A @ B ) =
% 45.40/45.58       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 45.40/45.58  thf('1', plain,
% 45.40/45.58      (![X2 : $i, X3 : $i]:
% 45.40/45.58         ((k5_xboole_0 @ X2 @ X3)
% 45.40/45.58           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 45.40/45.58      inference('cnf', [status(esa)], [d6_xboole_0])).
% 45.40/45.58  thf(commutativity_k2_xboole_0, axiom,
% 45.40/45.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 45.40/45.58  thf('2', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 45.40/45.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 45.40/45.58  thf('3', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 45.40/45.58           = (k5_xboole_0 @ X1 @ X0))),
% 45.40/45.58      inference('sup+', [status(thm)], ['1', '2'])).
% 45.40/45.58  thf('4', plain,
% 45.40/45.58      (![X2 : $i, X3 : $i]:
% 45.40/45.58         ((k5_xboole_0 @ X2 @ X3)
% 45.40/45.58           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 45.40/45.58      inference('cnf', [status(esa)], [d6_xboole_0])).
% 45.40/45.58  thf('5', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.40/45.58      inference('sup+', [status(thm)], ['3', '4'])).
% 45.40/45.58  thf('6', plain,
% 45.40/45.58      (![X2 : $i, X3 : $i]:
% 45.40/45.58         ((k5_xboole_0 @ X2 @ X3)
% 45.40/45.58           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 45.40/45.58      inference('cnf', [status(esa)], [d6_xboole_0])).
% 45.40/45.58  thf(t79_xboole_1, axiom,
% 45.40/45.58    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 45.40/45.58  thf('7', plain,
% 45.40/45.58      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 45.40/45.58      inference('cnf', [status(esa)], [t79_xboole_1])).
% 45.40/45.58  thf(symmetry_r1_xboole_0, axiom,
% 45.40/45.58    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 45.40/45.58  thf('8', plain,
% 45.40/45.58      (![X4 : $i, X5 : $i]:
% 45.40/45.58         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 45.40/45.58      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 45.40/45.58  thf('9', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 45.40/45.58      inference('sup-', [status(thm)], ['7', '8'])).
% 45.40/45.58  thf(t83_xboole_1, axiom,
% 45.40/45.58    (![A:$i,B:$i]:
% 45.40/45.58     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 45.40/45.58  thf('10', plain,
% 45.40/45.58      (![X17 : $i, X18 : $i]:
% 45.40/45.58         (((k4_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_xboole_0 @ X17 @ X18))),
% 45.40/45.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 45.40/45.58  thf('11', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 45.40/45.58      inference('sup-', [status(thm)], ['9', '10'])).
% 45.40/45.58  thf(t41_xboole_1, axiom,
% 45.40/45.58    (![A:$i,B:$i,C:$i]:
% 45.40/45.58     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 45.40/45.58       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 45.40/45.58  thf('12', plain,
% 45.40/45.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 45.40/45.58         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 45.40/45.58           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 45.40/45.58      inference('cnf', [status(esa)], [t41_xboole_1])).
% 45.40/45.58  thf('13', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.40/45.58         ((k4_xboole_0 @ X0 @ X1)
% 45.40/45.58           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)))),
% 45.40/45.58      inference('sup+', [status(thm)], ['11', '12'])).
% 45.40/45.58  thf('14', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 45.40/45.58           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.40/45.58      inference('sup+', [status(thm)], ['6', '13'])).
% 45.40/45.58  thf(t48_xboole_1, axiom,
% 45.40/45.58    (![A:$i,B:$i]:
% 45.40/45.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 45.40/45.58  thf('15', plain,
% 45.40/45.58      (![X11 : $i, X12 : $i]:
% 45.40/45.58         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 45.40/45.58           = (k3_xboole_0 @ X11 @ X12))),
% 45.40/45.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.40/45.58  thf('16', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 45.40/45.58           = (k3_xboole_0 @ X0 @ X1))),
% 45.40/45.58      inference('sup+', [status(thm)], ['14', '15'])).
% 45.40/45.58  thf('17', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 45.40/45.58           = (k3_xboole_0 @ X1 @ X0))),
% 45.40/45.58      inference('sup+', [status(thm)], ['5', '16'])).
% 45.40/45.58  thf('18', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 45.40/45.58      inference('sup-', [status(thm)], ['9', '10'])).
% 45.40/45.58  thf('19', plain,
% 45.40/45.58      (![X2 : $i, X3 : $i]:
% 45.40/45.58         ((k5_xboole_0 @ X2 @ X3)
% 45.40/45.58           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 45.40/45.58      inference('cnf', [status(esa)], [d6_xboole_0])).
% 45.40/45.58  thf('20', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 45.40/45.58           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 45.40/45.58      inference('sup+', [status(thm)], ['18', '19'])).
% 45.40/45.58  thf(t39_xboole_1, axiom,
% 45.40/45.58    (![A:$i,B:$i]:
% 45.40/45.58     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 45.40/45.58  thf('21', plain,
% 45.40/45.58      (![X6 : $i, X7 : $i]:
% 45.40/45.58         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 45.40/45.58           = (k2_xboole_0 @ X6 @ X7))),
% 45.40/45.58      inference('cnf', [status(esa)], [t39_xboole_1])).
% 45.40/45.58  thf('22', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 45.40/45.58           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 45.40/45.58      inference('demod', [status(thm)], ['20', '21'])).
% 45.40/45.58  thf('23', plain,
% 45.40/45.58      (![X6 : $i, X7 : $i]:
% 45.40/45.58         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 45.40/45.58           = (k2_xboole_0 @ X6 @ X7))),
% 45.40/45.58      inference('cnf', [status(esa)], [t39_xboole_1])).
% 45.40/45.58  thf('24', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 45.40/45.58           = (k2_xboole_0 @ X0 @ X1))),
% 45.40/45.58      inference('sup+', [status(thm)], ['22', '23'])).
% 45.40/45.58  thf('25', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 45.40/45.58           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1))),
% 45.40/45.58      inference('sup+', [status(thm)], ['17', '24'])).
% 45.40/45.58  thf('26', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 45.40/45.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 45.40/45.58  thf('27', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 45.40/45.58           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.40/45.58      inference('demod', [status(thm)], ['25', '26'])).
% 45.40/45.58  thf('28', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.40/45.58      inference('sup+', [status(thm)], ['3', '4'])).
% 45.40/45.58  thf('29', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 45.40/45.58           = (k3_xboole_0 @ X0 @ X1))),
% 45.40/45.58      inference('sup+', [status(thm)], ['14', '15'])).
% 45.40/45.58  thf('30', plain,
% 45.40/45.58      (![X6 : $i, X7 : $i]:
% 45.40/45.58         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 45.40/45.58           = (k2_xboole_0 @ X6 @ X7))),
% 45.40/45.58      inference('cnf', [status(esa)], [t39_xboole_1])).
% 45.40/45.58  thf('31', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 45.40/45.58           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X1))),
% 45.40/45.58      inference('sup+', [status(thm)], ['29', '30'])).
% 45.40/45.58  thf('32', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 45.40/45.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 45.40/45.58  thf('33', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 45.40/45.58           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))),
% 45.40/45.58      inference('demod', [status(thm)], ['31', '32'])).
% 45.40/45.58  thf('34', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.40/45.58      inference('sup+', [status(thm)], ['3', '4'])).
% 45.40/45.58  thf(t93_xboole_1, axiom,
% 45.40/45.58    (![A:$i,B:$i]:
% 45.40/45.58     ( ( k2_xboole_0 @ A @ B ) =
% 45.40/45.58       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 45.40/45.58  thf('35', plain,
% 45.40/45.58      (![X20 : $i, X21 : $i]:
% 45.40/45.58         ((k2_xboole_0 @ X20 @ X21)
% 45.40/45.58           = (k2_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 45.40/45.58              (k3_xboole_0 @ X20 @ X21)))),
% 45.40/45.58      inference('cnf', [status(esa)], [t93_xboole_1])).
% 45.40/45.58  thf('36', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k2_xboole_0 @ X0 @ X1)
% 45.40/45.58           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 45.40/45.58      inference('sup+', [status(thm)], ['34', '35'])).
% 45.40/45.58  thf('37', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k2_xboole_0 @ X0 @ X1)
% 45.40/45.58           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.40/45.58      inference('sup+', [status(thm)], ['33', '36'])).
% 45.40/45.58  thf('38', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k2_xboole_0 @ X1 @ X0)
% 45.40/45.58           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.40/45.58      inference('sup+', [status(thm)], ['28', '37'])).
% 45.40/45.58  thf('39', plain,
% 45.40/45.58      (![X0 : $i, X1 : $i]:
% 45.40/45.58         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 45.40/45.58           = (k2_xboole_0 @ X1 @ X0))),
% 45.40/45.58      inference('demod', [status(thm)], ['27', '38'])).
% 45.40/45.58  thf('40', plain,
% 45.40/45.58      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 45.40/45.58      inference('demod', [status(thm)], ['0', '39'])).
% 45.40/45.58  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 45.40/45.58  
% 45.40/45.58  % SZS output end Refutation
% 45.40/45.58  
% 45.40/45.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
