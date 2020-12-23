%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.egQTKbPZog

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:16 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   67 (  90 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  461 ( 645 expanded)
%              Number of equality atoms :   50 (  71 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t76_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
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
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('35',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['24','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['23','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['3','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.egQTKbPZog
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:57:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.66/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.88  % Solved by: fo/fo7.sh
% 0.66/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.88  % done 924 iterations in 0.429s
% 0.66/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.88  % SZS output start Refutation
% 0.66/0.88  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.66/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.66/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.88  thf(t76_xboole_1, conjecture,
% 0.66/0.88    (![A:$i,B:$i,C:$i]:
% 0.66/0.88     ( ( r1_xboole_0 @ A @ B ) =>
% 0.66/0.88       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 0.66/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.88    (~( ![A:$i,B:$i,C:$i]:
% 0.66/0.88        ( ( r1_xboole_0 @ A @ B ) =>
% 0.66/0.88          ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )),
% 0.66/0.88    inference('cnf.neg', [status(esa)], [t76_xboole_1])).
% 0.66/0.88  thf('0', plain,
% 0.66/0.88      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.66/0.88          (k3_xboole_0 @ sk_C @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf(commutativity_k3_xboole_0, axiom,
% 0.66/0.88    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.66/0.88  thf('1', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.88  thf('2', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.88  thf('3', plain,
% 0.66/0.88      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 0.66/0.88          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.66/0.88      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.66/0.88  thf(t48_xboole_1, axiom,
% 0.66/0.88    (![A:$i,B:$i]:
% 0.66/0.88     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.66/0.88  thf('4', plain,
% 0.66/0.88      (![X9 : $i, X10 : $i]:
% 0.66/0.88         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.66/0.88           = (k3_xboole_0 @ X9 @ X10))),
% 0.66/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.88  thf('5', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf(d7_xboole_0, axiom,
% 0.66/0.88    (![A:$i,B:$i]:
% 0.66/0.88     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.66/0.88       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.66/0.88  thf('6', plain,
% 0.66/0.88      (![X2 : $i, X3 : $i]:
% 0.66/0.88         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.66/0.88      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.66/0.88  thf('7', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.66/0.88      inference('sup-', [status(thm)], ['5', '6'])).
% 0.66/0.88  thf(t49_xboole_1, axiom,
% 0.66/0.88    (![A:$i,B:$i,C:$i]:
% 0.66/0.88     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.66/0.88       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.66/0.88  thf('8', plain,
% 0.66/0.88      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.66/0.88         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.66/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.66/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.66/0.88  thf('9', plain,
% 0.66/0.88      (![X0 : $i]:
% 0.66/0.88         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.66/0.88           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.66/0.88      inference('sup+', [status(thm)], ['7', '8'])).
% 0.66/0.88  thf('10', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.88  thf(t2_boole, axiom,
% 0.66/0.88    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.66/0.88  thf('11', plain,
% 0.66/0.88      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.66/0.88      inference('cnf', [status(esa)], [t2_boole])).
% 0.66/0.88  thf('12', plain,
% 0.66/0.88      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.66/0.88      inference('sup+', [status(thm)], ['10', '11'])).
% 0.66/0.88  thf(t47_xboole_1, axiom,
% 0.66/0.88    (![A:$i,B:$i]:
% 0.66/0.88     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.66/0.88  thf('13', plain,
% 0.66/0.88      (![X7 : $i, X8 : $i]:
% 0.66/0.88         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.66/0.88           = (k4_xboole_0 @ X7 @ X8))),
% 0.66/0.88      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.66/0.88  thf('14', plain,
% 0.66/0.88      (![X0 : $i]:
% 0.66/0.88         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.66/0.88           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.66/0.88      inference('sup+', [status(thm)], ['12', '13'])).
% 0.66/0.88  thf(t3_boole, axiom,
% 0.66/0.88    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.66/0.88  thf('15', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.66/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.66/0.88  thf('16', plain,
% 0.66/0.88      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.66/0.88      inference('demod', [status(thm)], ['14', '15'])).
% 0.66/0.88  thf('17', plain,
% 0.66/0.88      (![X0 : $i]:
% 0.66/0.88         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) = (k1_xboole_0))),
% 0.66/0.88      inference('demod', [status(thm)], ['9', '16'])).
% 0.66/0.88  thf('18', plain,
% 0.66/0.88      (![X0 : $i]:
% 0.66/0.88         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) = (k1_xboole_0))),
% 0.66/0.88      inference('sup+', [status(thm)], ['4', '17'])).
% 0.66/0.88  thf('19', plain,
% 0.66/0.88      (![X7 : $i, X8 : $i]:
% 0.66/0.88         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.66/0.88           = (k4_xboole_0 @ X7 @ X8))),
% 0.66/0.88      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.66/0.88  thf('20', plain,
% 0.66/0.88      (![X0 : $i]:
% 0.66/0.88         ((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.66/0.88           = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.66/0.88      inference('sup+', [status(thm)], ['18', '19'])).
% 0.66/0.88  thf('21', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.66/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.66/0.88  thf('22', plain,
% 0.66/0.88      (![X0 : $i]: ((sk_A) = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.66/0.88      inference('demod', [status(thm)], ['20', '21'])).
% 0.66/0.88  thf('23', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.88  thf('24', plain,
% 0.66/0.88      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.66/0.88         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.66/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.66/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.66/0.88  thf('25', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.88  thf('26', plain,
% 0.66/0.88      (![X7 : $i, X8 : $i]:
% 0.66/0.88         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.66/0.88           = (k4_xboole_0 @ X7 @ X8))),
% 0.66/0.88      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.66/0.88  thf('27', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]:
% 0.66/0.88         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.66/0.88           = (k4_xboole_0 @ X0 @ X1))),
% 0.66/0.88      inference('sup+', [status(thm)], ['25', '26'])).
% 0.66/0.88  thf('28', plain,
% 0.66/0.88      (![X7 : $i, X8 : $i]:
% 0.66/0.88         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.66/0.88           = (k4_xboole_0 @ X7 @ X8))),
% 0.66/0.88      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.66/0.88  thf('29', plain,
% 0.66/0.88      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.66/0.88         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.66/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.66/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.66/0.88  thf('30', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.88         ((k3_xboole_0 @ X2 @ 
% 0.66/0.88           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 0.66/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.66/0.88      inference('sup+', [status(thm)], ['28', '29'])).
% 0.66/0.88  thf('31', plain,
% 0.66/0.88      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.66/0.88         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.66/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.66/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.66/0.88  thf('32', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.88         ((k3_xboole_0 @ X2 @ 
% 0.66/0.88           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 0.66/0.88           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.66/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.66/0.88  thf('33', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]:
% 0.66/0.88         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 0.66/0.88           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.66/0.88      inference('sup+', [status(thm)], ['27', '32'])).
% 0.66/0.88  thf('34', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]:
% 0.66/0.88         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.66/0.88           = (k4_xboole_0 @ X0 @ X1))),
% 0.66/0.88      inference('sup+', [status(thm)], ['25', '26'])).
% 0.66/0.88  thf('35', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.66/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.66/0.88  thf('36', plain,
% 0.66/0.88      (![X9 : $i, X10 : $i]:
% 0.66/0.88         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.66/0.88           = (k3_xboole_0 @ X9 @ X10))),
% 0.66/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.88  thf('37', plain,
% 0.66/0.88      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.66/0.88      inference('sup+', [status(thm)], ['35', '36'])).
% 0.66/0.88  thf('38', plain,
% 0.66/0.88      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.66/0.88      inference('cnf', [status(esa)], [t2_boole])).
% 0.66/0.88  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.66/0.88      inference('demod', [status(thm)], ['37', '38'])).
% 0.66/0.88  thf('40', plain,
% 0.66/0.88      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.66/0.88      inference('cnf', [status(esa)], [t2_boole])).
% 0.66/0.88  thf('41', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]:
% 0.66/0.88         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.66/0.88      inference('demod', [status(thm)], ['33', '34', '39', '40'])).
% 0.66/0.88  thf('42', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.88  thf('43', plain,
% 0.66/0.88      (![X2 : $i, X4 : $i]:
% 0.66/0.88         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.66/0.88      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.66/0.88  thf('44', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]:
% 0.66/0.88         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.66/0.88      inference('sup-', [status(thm)], ['42', '43'])).
% 0.66/0.88  thf('45', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]:
% 0.66/0.88         (((k1_xboole_0) != (k1_xboole_0))
% 0.66/0.88          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.66/0.88      inference('sup-', [status(thm)], ['41', '44'])).
% 0.66/0.88  thf('46', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.66/0.88      inference('simplify', [status(thm)], ['45'])).
% 0.66/0.88  thf('47', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.88         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 0.66/0.88      inference('sup+', [status(thm)], ['24', '46'])).
% 0.66/0.88  thf('48', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.88         (r1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X1)),
% 0.66/0.88      inference('sup+', [status(thm)], ['23', '47'])).
% 0.66/0.88  thf('49', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]:
% 0.66/0.88         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_B @ X0))),
% 0.66/0.88      inference('sup+', [status(thm)], ['22', '48'])).
% 0.66/0.88  thf('50', plain, ($false), inference('demod', [status(thm)], ['3', '49'])).
% 0.66/0.88  
% 0.66/0.88  % SZS output end Refutation
% 0.66/0.88  
% 0.66/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
