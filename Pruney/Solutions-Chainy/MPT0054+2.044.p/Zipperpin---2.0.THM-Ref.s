%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y13B4eMZI7

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:13 EST 2020

% Result     : Theorem 4.73s
% Output     : Refutation 4.73s
% Verified   : 
% Statistics : Number of formulae       :   60 (  84 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  492 ( 688 expanded)
%              Number of equality atoms :   51 (  73 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t47_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t47_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
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
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t24_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k2_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k2_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k2_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y13B4eMZI7
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.73/4.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.73/4.96  % Solved by: fo/fo7.sh
% 4.73/4.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.73/4.96  % done 3871 iterations in 4.480s
% 4.73/4.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.73/4.96  % SZS output start Refutation
% 4.73/4.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.73/4.96  thf(sk_A_type, type, sk_A: $i).
% 4.73/4.96  thf(sk_B_type, type, sk_B: $i).
% 4.73/4.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.73/4.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.73/4.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.73/4.96  thf(t47_xboole_1, conjecture,
% 4.73/4.96    (![A:$i,B:$i]:
% 4.73/4.96     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.73/4.96  thf(zf_stmt_0, negated_conjecture,
% 4.73/4.96    (~( ![A:$i,B:$i]:
% 4.73/4.96        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 4.73/4.96          ( k4_xboole_0 @ A @ B ) ) )),
% 4.73/4.96    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 4.73/4.96  thf('0', plain,
% 4.73/4.96      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 4.73/4.96         != (k4_xboole_0 @ sk_A @ sk_B))),
% 4.73/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.73/4.96  thf(commutativity_k3_xboole_0, axiom,
% 4.73/4.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.73/4.96  thf('1', plain,
% 4.73/4.96      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.73/4.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.73/4.96  thf('2', plain,
% 4.73/4.96      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 4.73/4.96         != (k4_xboole_0 @ sk_A @ sk_B))),
% 4.73/4.96      inference('demod', [status(thm)], ['0', '1'])).
% 4.73/4.96  thf(t39_xboole_1, axiom,
% 4.73/4.96    (![A:$i,B:$i]:
% 4.73/4.96     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.73/4.96  thf('3', plain,
% 4.73/4.96      (![X13 : $i, X14 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 4.73/4.96           = (k2_xboole_0 @ X13 @ X14))),
% 4.73/4.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.73/4.96  thf(commutativity_k2_xboole_0, axiom,
% 4.73/4.96    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.73/4.96  thf('4', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.73/4.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.73/4.96  thf(t24_xboole_1, axiom,
% 4.73/4.96    (![A:$i,B:$i,C:$i]:
% 4.73/4.96     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 4.73/4.96       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 4.73/4.96  thf('5', plain,
% 4.73/4.96      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 4.73/4.96           = (k3_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k2_xboole_0 @ X6 @ X8)))),
% 4.73/4.96      inference('cnf', [status(esa)], [t24_xboole_1])).
% 4.73/4.96  thf('6', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 4.73/4.96           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 4.73/4.96      inference('sup+', [status(thm)], ['4', '5'])).
% 4.73/4.96  thf('7', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X2))
% 4.73/4.96           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 4.73/4.96              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 4.73/4.96      inference('sup+', [status(thm)], ['3', '6'])).
% 4.73/4.96  thf('8', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.73/4.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.73/4.96  thf('9', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 4.73/4.96           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 4.73/4.96      inference('sup+', [status(thm)], ['4', '5'])).
% 4.73/4.96  thf('10', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 4.73/4.96           = (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 4.73/4.96      inference('sup+', [status(thm)], ['8', '9'])).
% 4.73/4.96  thf('11', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))
% 4.73/4.96           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 4.73/4.96      inference('sup+', [status(thm)], ['7', '10'])).
% 4.73/4.96  thf(t36_xboole_1, axiom,
% 4.73/4.96    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.73/4.96  thf('12', plain,
% 4.73/4.96      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 4.73/4.96      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.73/4.96  thf(t28_xboole_1, axiom,
% 4.73/4.96    (![A:$i,B:$i]:
% 4.73/4.96     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.73/4.96  thf('13', plain,
% 4.73/4.96      (![X9 : $i, X10 : $i]:
% 4.73/4.96         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 4.73/4.96      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.73/4.96  thf('14', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i]:
% 4.73/4.96         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 4.73/4.96           = (k4_xboole_0 @ X0 @ X1))),
% 4.73/4.96      inference('sup-', [status(thm)], ['12', '13'])).
% 4.73/4.96  thf('15', plain,
% 4.73/4.96      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.73/4.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.73/4.96  thf('16', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i]:
% 4.73/4.96         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.73/4.96           = (k4_xboole_0 @ X0 @ X1))),
% 4.73/4.96      inference('demod', [status(thm)], ['14', '15'])).
% 4.73/4.96  thf(t22_xboole_1, axiom,
% 4.73/4.96    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 4.73/4.96  thf('17', plain,
% 4.73/4.96      (![X4 : $i, X5 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)) = (X4))),
% 4.73/4.96      inference('cnf', [status(esa)], [t22_xboole_1])).
% 4.73/4.96  thf('18', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 4.73/4.96      inference('sup+', [status(thm)], ['16', '17'])).
% 4.73/4.96  thf('19', plain,
% 4.73/4.96      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 4.73/4.96           = (k3_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k2_xboole_0 @ X6 @ X8)))),
% 4.73/4.96      inference('cnf', [status(esa)], [t24_xboole_1])).
% 4.73/4.96  thf('20', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 4.73/4.96           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X0))),
% 4.73/4.96      inference('sup+', [status(thm)], ['18', '19'])).
% 4.73/4.96  thf('21', plain,
% 4.73/4.96      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.73/4.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.73/4.96  thf('22', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 4.73/4.96           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X2)))),
% 4.73/4.96      inference('demod', [status(thm)], ['20', '21'])).
% 4.73/4.96  thf('23', plain,
% 4.73/4.96      (![X13 : $i, X14 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 4.73/4.96           = (k2_xboole_0 @ X13 @ X14))),
% 4.73/4.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.73/4.96  thf('24', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 4.73/4.96      inference('sup+', [status(thm)], ['16', '17'])).
% 4.73/4.96  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 4.73/4.96      inference('sup+', [status(thm)], ['23', '24'])).
% 4.73/4.96  thf('26', plain,
% 4.73/4.96      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 4.73/4.96           = (k3_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k2_xboole_0 @ X6 @ X8)))),
% 4.73/4.96      inference('cnf', [status(esa)], [t24_xboole_1])).
% 4.73/4.96  thf('27', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 4.73/4.96           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 4.73/4.96      inference('sup+', [status(thm)], ['25', '26'])).
% 4.73/4.96  thf('28', plain,
% 4.73/4.96      (![X4 : $i, X5 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)) = (X4))),
% 4.73/4.96      inference('cnf', [status(esa)], [t22_xboole_1])).
% 4.73/4.96  thf('29', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i]:
% 4.73/4.96         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 4.73/4.96      inference('demod', [status(thm)], ['27', '28'])).
% 4.73/4.96  thf('30', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 4.73/4.96           = (X0))),
% 4.73/4.96      inference('demod', [status(thm)], ['22', '29'])).
% 4.73/4.96  thf('31', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.73/4.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.73/4.96  thf('32', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i]:
% 4.73/4.96         ((X0)
% 4.73/4.96           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 4.73/4.96      inference('demod', [status(thm)], ['11', '30', '31'])).
% 4.73/4.96  thf('33', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.73/4.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.73/4.96  thf(t40_xboole_1, axiom,
% 4.73/4.96    (![A:$i,B:$i]:
% 4.73/4.96     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.73/4.96  thf('34', plain,
% 4.73/4.96      (![X15 : $i, X16 : $i]:
% 4.73/4.96         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 4.73/4.96           = (k4_xboole_0 @ X15 @ X16))),
% 4.73/4.96      inference('cnf', [status(esa)], [t40_xboole_1])).
% 4.73/4.96  thf('35', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i]:
% 4.73/4.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 4.73/4.96           = (k4_xboole_0 @ X0 @ X1))),
% 4.73/4.96      inference('sup+', [status(thm)], ['33', '34'])).
% 4.73/4.96  thf('36', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i]:
% 4.73/4.96         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 4.73/4.96           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 4.73/4.96      inference('sup+', [status(thm)], ['32', '35'])).
% 4.73/4.96  thf('37', plain,
% 4.73/4.96      (![X4 : $i, X5 : $i]:
% 4.73/4.96         ((k2_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)) = (X4))),
% 4.73/4.96      inference('cnf', [status(esa)], [t22_xboole_1])).
% 4.73/4.96  thf(t41_xboole_1, axiom,
% 4.73/4.96    (![A:$i,B:$i,C:$i]:
% 4.73/4.96     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 4.73/4.96       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 4.73/4.96  thf('38', plain,
% 4.73/4.96      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.73/4.96         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 4.73/4.96           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 4.73/4.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.73/4.96  thf('39', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.73/4.96         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 4.73/4.96           = (k4_xboole_0 @ X2 @ X0))),
% 4.73/4.96      inference('sup+', [status(thm)], ['37', '38'])).
% 4.73/4.96  thf('40', plain,
% 4.73/4.96      (![X0 : $i, X1 : $i]:
% 4.73/4.96         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 4.73/4.96           = (k4_xboole_0 @ X0 @ X1))),
% 4.73/4.96      inference('demod', [status(thm)], ['36', '39'])).
% 4.73/4.96  thf('41', plain,
% 4.73/4.96      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 4.73/4.96      inference('demod', [status(thm)], ['2', '40'])).
% 4.73/4.96  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 4.73/4.96  
% 4.73/4.96  % SZS output end Refutation
% 4.73/4.96  
% 4.73/4.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
