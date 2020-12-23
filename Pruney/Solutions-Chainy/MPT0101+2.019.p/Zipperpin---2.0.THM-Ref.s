%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1zVhIjvlyd

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:57 EST 2020

% Result     : Theorem 8.90s
% Output     : Refutation 8.90s
% Verified   : 
% Statistics : Number of formulae       :   62 (  98 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  525 ( 839 expanded)
%              Number of equality atoms :   52 (  88 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k2_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k2_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','24','25'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','41','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1zVhIjvlyd
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:05:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 8.90/9.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.90/9.09  % Solved by: fo/fo7.sh
% 8.90/9.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.90/9.09  % done 3647 iterations in 8.648s
% 8.90/9.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.90/9.09  % SZS output start Refutation
% 8.90/9.09  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 8.90/9.09  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.90/9.09  thf(sk_A_type, type, sk_A: $i).
% 8.90/9.09  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.90/9.09  thf(sk_B_type, type, sk_B: $i).
% 8.90/9.09  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.90/9.09  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.90/9.09  thf(t94_xboole_1, conjecture,
% 8.90/9.09    (![A:$i,B:$i]:
% 8.90/9.09     ( ( k2_xboole_0 @ A @ B ) =
% 8.90/9.09       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 8.90/9.09  thf(zf_stmt_0, negated_conjecture,
% 8.90/9.09    (~( ![A:$i,B:$i]:
% 8.90/9.09        ( ( k2_xboole_0 @ A @ B ) =
% 8.90/9.09          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 8.90/9.09    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 8.90/9.09  thf('0', plain,
% 8.90/9.09      (((k2_xboole_0 @ sk_A @ sk_B)
% 8.90/9.09         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 8.90/9.09             (k3_xboole_0 @ sk_A @ sk_B)))),
% 8.90/9.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.90/9.09  thf(d6_xboole_0, axiom,
% 8.90/9.09    (![A:$i,B:$i]:
% 8.90/9.09     ( ( k5_xboole_0 @ A @ B ) =
% 8.90/9.09       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 8.90/9.09  thf('1', plain,
% 8.90/9.09      (![X2 : $i, X3 : $i]:
% 8.90/9.09         ((k5_xboole_0 @ X2 @ X3)
% 8.90/9.09           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 8.90/9.09      inference('cnf', [status(esa)], [d6_xboole_0])).
% 8.90/9.09  thf(t51_xboole_1, axiom,
% 8.90/9.09    (![A:$i,B:$i]:
% 8.90/9.09     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 8.90/9.09       ( A ) ))).
% 8.90/9.09  thf('2', plain,
% 8.90/9.09      (![X16 : $i, X17 : $i]:
% 8.90/9.09         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 8.90/9.09           = (X16))),
% 8.90/9.09      inference('cnf', [status(esa)], [t51_xboole_1])).
% 8.90/9.09  thf(t4_xboole_1, axiom,
% 8.90/9.09    (![A:$i,B:$i,C:$i]:
% 8.90/9.09     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 8.90/9.09       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 8.90/9.09  thf('3', plain,
% 8.90/9.09      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.90/9.09         ((k2_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X15)
% 8.90/9.09           = (k2_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 8.90/9.09      inference('cnf', [status(esa)], [t4_xboole_1])).
% 8.90/9.09  thf('4', plain,
% 8.90/9.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.90/9.09         ((k2_xboole_0 @ X0 @ X1)
% 8.90/9.09           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ 
% 8.90/9.09              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)))),
% 8.90/9.09      inference('sup+', [status(thm)], ['2', '3'])).
% 8.90/9.09  thf('5', plain,
% 8.90/9.09      (![X0 : $i, X1 : $i]:
% 8.90/9.09         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 8.90/9.09           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 8.90/9.09      inference('sup+', [status(thm)], ['1', '4'])).
% 8.90/9.09  thf(t39_xboole_1, axiom,
% 8.90/9.09    (![A:$i,B:$i]:
% 8.90/9.09     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 8.90/9.09  thf('6', plain,
% 8.90/9.09      (![X6 : $i, X7 : $i]:
% 8.90/9.09         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 8.90/9.09           = (k2_xboole_0 @ X6 @ X7))),
% 8.90/9.09      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.90/9.10  thf(t48_xboole_1, axiom,
% 8.90/9.10    (![A:$i,B:$i]:
% 8.90/9.10     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 8.90/9.10  thf('7', plain,
% 8.90/9.10      (![X11 : $i, X12 : $i]:
% 8.90/9.10         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 8.90/9.10           = (k3_xboole_0 @ X11 @ X12))),
% 8.90/9.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.90/9.10  thf('8', plain,
% 8.90/9.10      (![X6 : $i, X7 : $i]:
% 8.90/9.10         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 8.90/9.10           = (k2_xboole_0 @ X6 @ X7))),
% 8.90/9.10      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.90/9.10  thf('9', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]:
% 8.90/9.10         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 8.90/9.10           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 8.90/9.10      inference('sup+', [status(thm)], ['7', '8'])).
% 8.90/9.10  thf(commutativity_k2_xboole_0, axiom,
% 8.90/9.10    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 8.90/9.10  thf('10', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.90/9.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.90/9.10  thf('11', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.90/9.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.90/9.10  thf('12', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]:
% 8.90/9.10         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 8.90/9.10           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 8.90/9.10      inference('demod', [status(thm)], ['9', '10', '11'])).
% 8.90/9.10  thf('13', plain,
% 8.90/9.10      (![X16 : $i, X17 : $i]:
% 8.90/9.10         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 8.90/9.10           = (X16))),
% 8.90/9.10      inference('cnf', [status(esa)], [t51_xboole_1])).
% 8.90/9.10  thf('14', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]:
% 8.90/9.10         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 8.90/9.10      inference('sup+', [status(thm)], ['12', '13'])).
% 8.90/9.10  thf('15', plain,
% 8.90/9.10      (![X6 : $i, X7 : $i]:
% 8.90/9.10         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 8.90/9.10           = (k2_xboole_0 @ X6 @ X7))),
% 8.90/9.10      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.90/9.10  thf('16', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 8.90/9.10      inference('sup+', [status(thm)], ['14', '15'])).
% 8.90/9.10  thf('17', plain,
% 8.90/9.10      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.90/9.10         ((k2_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X15)
% 8.90/9.10           = (k2_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 8.90/9.10      inference('cnf', [status(esa)], [t4_xboole_1])).
% 8.90/9.10  thf('18', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.90/9.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.90/9.10  thf('19', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.90/9.10         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 8.90/9.10           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.90/9.10      inference('sup+', [status(thm)], ['17', '18'])).
% 8.90/9.10  thf('20', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]:
% 8.90/9.10         ((k2_xboole_0 @ X1 @ X0)
% 8.90/9.10           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 8.90/9.10      inference('sup+', [status(thm)], ['16', '19'])).
% 8.90/9.10  thf('21', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]:
% 8.90/9.10         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)
% 8.90/9.10           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.90/9.10      inference('sup+', [status(thm)], ['6', '20'])).
% 8.90/9.10  thf('22', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.90/9.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.90/9.10  thf('23', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]:
% 8.90/9.10         ((k2_xboole_0 @ X1 @ X0)
% 8.90/9.10           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 8.90/9.10      inference('sup+', [status(thm)], ['16', '19'])).
% 8.90/9.10  thf('24', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]:
% 8.90/9.10         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 8.90/9.10           = (k2_xboole_0 @ X0 @ X1))),
% 8.90/9.10      inference('demod', [status(thm)], ['21', '22', '23'])).
% 8.90/9.10  thf('25', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.90/9.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.90/9.10  thf('26', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]:
% 8.90/9.10         ((k2_xboole_0 @ X0 @ X1)
% 8.90/9.10           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 8.90/9.10      inference('demod', [status(thm)], ['5', '24', '25'])).
% 8.90/9.10  thf(l97_xboole_1, axiom,
% 8.90/9.10    (![A:$i,B:$i]:
% 8.90/9.10     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 8.90/9.10  thf('27', plain,
% 8.90/9.10      (![X4 : $i, X5 : $i]:
% 8.90/9.10         (r1_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ (k5_xboole_0 @ X4 @ X5))),
% 8.90/9.10      inference('cnf', [status(esa)], [l97_xboole_1])).
% 8.90/9.10  thf(t83_xboole_1, axiom,
% 8.90/9.10    (![A:$i,B:$i]:
% 8.90/9.10     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 8.90/9.10  thf('28', plain,
% 8.90/9.10      (![X20 : $i, X21 : $i]:
% 8.90/9.10         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 8.90/9.10      inference('cnf', [status(esa)], [t83_xboole_1])).
% 8.90/9.10  thf('29', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]:
% 8.90/9.10         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 8.90/9.10           = (k3_xboole_0 @ X1 @ X0))),
% 8.90/9.10      inference('sup-', [status(thm)], ['27', '28'])).
% 8.90/9.10  thf('30', plain,
% 8.90/9.10      (![X2 : $i, X3 : $i]:
% 8.90/9.10         ((k5_xboole_0 @ X2 @ X3)
% 8.90/9.10           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 8.90/9.10      inference('cnf', [status(esa)], [d6_xboole_0])).
% 8.90/9.10  thf('31', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]:
% 8.90/9.10         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 8.90/9.10           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 8.90/9.10              (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 8.90/9.10      inference('sup+', [status(thm)], ['29', '30'])).
% 8.90/9.10  thf('32', plain,
% 8.90/9.10      (![X6 : $i, X7 : $i]:
% 8.90/9.10         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 8.90/9.10           = (k2_xboole_0 @ X6 @ X7))),
% 8.90/9.10      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.90/9.10  thf('33', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.90/9.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.90/9.10  thf('34', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]:
% 8.90/9.10         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 8.90/9.10           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 8.90/9.10      inference('demod', [status(thm)], ['31', '32', '33'])).
% 8.90/9.10  thf('35', plain,
% 8.90/9.10      (![X2 : $i, X3 : $i]:
% 8.90/9.10         ((k5_xboole_0 @ X2 @ X3)
% 8.90/9.10           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 8.90/9.10      inference('cnf', [status(esa)], [d6_xboole_0])).
% 8.90/9.10  thf('36', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.90/9.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.90/9.10  thf('37', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]:
% 8.90/9.10         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 8.90/9.10           = (k5_xboole_0 @ X1 @ X0))),
% 8.90/9.10      inference('sup+', [status(thm)], ['35', '36'])).
% 8.90/9.10  thf('38', plain,
% 8.90/9.10      (![X2 : $i, X3 : $i]:
% 8.90/9.10         ((k5_xboole_0 @ X2 @ X3)
% 8.90/9.10           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 8.90/9.10      inference('cnf', [status(esa)], [d6_xboole_0])).
% 8.90/9.10  thf('39', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 8.90/9.10      inference('sup+', [status(thm)], ['37', '38'])).
% 8.90/9.10  thf('40', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]:
% 8.90/9.10         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 8.90/9.10           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 8.90/9.10      inference('demod', [status(thm)], ['34', '39'])).
% 8.90/9.10  thf('41', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]:
% 8.90/9.10         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 8.90/9.10           = (k2_xboole_0 @ X1 @ X0))),
% 8.90/9.10      inference('sup+', [status(thm)], ['26', '40'])).
% 8.90/9.10  thf('42', plain,
% 8.90/9.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.90/9.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.90/9.10  thf('43', plain,
% 8.90/9.10      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 8.90/9.10      inference('demod', [status(thm)], ['0', '41', '42'])).
% 8.90/9.10  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 8.90/9.10  
% 8.90/9.10  % SZS output end Refutation
% 8.90/9.10  
% 8.90/9.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
