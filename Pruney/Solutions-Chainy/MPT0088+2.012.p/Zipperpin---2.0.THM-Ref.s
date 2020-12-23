%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jlV3Lpvxgg

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 119 expanded)
%              Number of leaves         :   18 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  465 ( 964 expanded)
%              Number of equality atoms :   47 (  94 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('5',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26','27','36'])).

thf('38',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jlV3Lpvxgg
% 0.13/0.37  % Computer   : n018.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 13:02:42 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.22/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.58  % Solved by: fo/fo7.sh
% 0.22/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.58  % done 268 iterations in 0.113s
% 0.22/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.58  % SZS output start Refutation
% 0.22/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.58  thf(t81_xboole_1, conjecture,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.22/0.58       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.22/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.58        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.22/0.58          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 0.22/0.58    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 0.22/0.58  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf(t39_xboole_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.58  thf('1', plain,
% 0.22/0.58      (![X6 : $i, X7 : $i]:
% 0.22/0.58         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.22/0.58           = (k2_xboole_0 @ X6 @ X7))),
% 0.22/0.58      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.58  thf(t40_xboole_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.22/0.58  thf('2', plain,
% 0.22/0.58      (![X9 : $i, X10 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 0.22/0.58           = (k4_xboole_0 @ X9 @ X10))),
% 0.22/0.58      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.22/0.58  thf('3', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.22/0.58           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.58  thf('4', plain,
% 0.22/0.58      (![X6 : $i, X7 : $i]:
% 0.22/0.58         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.22/0.58           = (k2_xboole_0 @ X6 @ X7))),
% 0.22/0.58      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.58  thf('5', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf(d7_xboole_0, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.22/0.58       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.58  thf('6', plain,
% 0.22/0.58      (![X2 : $i, X3 : $i]:
% 0.22/0.58         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.22/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.58  thf('7', plain,
% 0.22/0.58      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.58  thf(t47_xboole_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.22/0.58  thf('8', plain,
% 0.22/0.58      (![X14 : $i, X15 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.22/0.58           = (k4_xboole_0 @ X14 @ X15))),
% 0.22/0.58      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.22/0.58  thf('9', plain,
% 0.22/0.58      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.22/0.58         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.58  thf(t3_boole, axiom,
% 0.22/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.58  thf('10', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.22/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.58  thf('11', plain,
% 0.22/0.58      (((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.58  thf(t41_xboole_1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.58       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.22/0.58  thf('12', plain,
% 0.22/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.22/0.58           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.22/0.58  thf('13', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ sk_A @ X0)
% 0.22/0.58           = (k4_xboole_0 @ sk_A @ 
% 0.22/0.58              (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.58  thf('14', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ sk_A @ 
% 0.22/0.58           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.22/0.58           = (k4_xboole_0 @ sk_A @ 
% 0.22/0.58              (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['4', '13'])).
% 0.22/0.58  thf('15', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ sk_A @ X0)
% 0.22/0.58           = (k4_xboole_0 @ sk_A @ 
% 0.22/0.58              (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.58  thf('16', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ sk_A @ 
% 0.22/0.58           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.22/0.58           = (k4_xboole_0 @ sk_A @ X0))),
% 0.22/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.58  thf('17', plain,
% 0.22/0.58      (((k4_xboole_0 @ sk_A @ 
% 0.22/0.58         (k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.22/0.58         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['3', '16'])).
% 0.22/0.58  thf('18', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ sk_A @ 
% 0.22/0.58           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.22/0.58           = (k4_xboole_0 @ sk_A @ X0))),
% 0.22/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.58  thf('19', plain,
% 0.22/0.58      (((k4_xboole_0 @ sk_A @ sk_C)
% 0.22/0.58         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))),
% 0.22/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.58  thf(t48_xboole_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.58  thf('20', plain,
% 0.22/0.58      (![X16 : $i, X17 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.22/0.58           = (k3_xboole_0 @ X16 @ X17))),
% 0.22/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.58  thf('21', plain,
% 0.22/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.22/0.58           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.22/0.58  thf('22', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.22/0.58           = (k4_xboole_0 @ X2 @ 
% 0.22/0.58              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.22/0.58      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.58  thf('23', plain,
% 0.22/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.22/0.58           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.22/0.58  thf('24', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.22/0.58           = (k4_xboole_0 @ X2 @ 
% 0.22/0.58              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.22/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.58  thf('25', plain,
% 0.22/0.58      (((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B)
% 0.22/0.58         = (k4_xboole_0 @ sk_A @ 
% 0.22/0.58            (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_C))))),
% 0.22/0.58      inference('sup+', [status(thm)], ['19', '24'])).
% 0.22/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.58  thf('26', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.58  thf('27', plain,
% 0.22/0.58      (![X6 : $i, X7 : $i]:
% 0.22/0.58         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.22/0.58           = (k2_xboole_0 @ X6 @ X7))),
% 0.22/0.58      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.58  thf('28', plain,
% 0.22/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.22/0.58           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.22/0.58  thf('29', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.22/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.58  thf('30', plain,
% 0.22/0.58      (![X16 : $i, X17 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.22/0.58           = (k3_xboole_0 @ X16 @ X17))),
% 0.22/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.58  thf('31', plain,
% 0.22/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['29', '30'])).
% 0.22/0.58  thf(t2_boole, axiom,
% 0.22/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.58  thf('32', plain,
% 0.22/0.58      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.58  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.58  thf('34', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.22/0.58           = (k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['28', '33'])).
% 0.22/0.58  thf('35', plain,
% 0.22/0.58      (![X6 : $i, X7 : $i]:
% 0.22/0.58         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.22/0.58           = (k2_xboole_0 @ X6 @ X7))),
% 0.22/0.58      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.58  thf('36', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.58  thf('37', plain,
% 0.22/0.58      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)) = (k1_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['25', '26', '27', '36'])).
% 0.22/0.58  thf('38', plain,
% 0.22/0.58      (![X2 : $i, X4 : $i]:
% 0.22/0.58         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.22/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.58  thf('39', plain,
% 0.22/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.58        | (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.58  thf('40', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.58      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.58  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.22/0.58  
% 0.22/0.58  % SZS output end Refutation
% 0.22/0.58  
% 0.22/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
