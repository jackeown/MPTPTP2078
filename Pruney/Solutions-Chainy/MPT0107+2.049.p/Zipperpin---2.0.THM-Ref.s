%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1lgHqFxVOl

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 100 expanded)
%              Number of leaves         :   17 (  38 expanded)
%              Depth                    :   17
%              Number of atoms          :  464 ( 749 expanded)
%              Number of equality atoms :   55 (  92 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) )
      = ( k4_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('16',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('20',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['1','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) )
      = ( k4_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1lgHqFxVOl
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:26:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 189 iterations in 0.110s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(t100_xboole_1, conjecture,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i,B:$i]:
% 0.22/0.57        ( ( k4_xboole_0 @ A @ B ) =
% 0.22/0.57          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.22/0.57  thf('0', plain,
% 0.22/0.57      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.22/0.57         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(t48_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      (![X5 : $i, X6 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.22/0.57           = (k3_xboole_0 @ X5 @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      (![X5 : $i, X6 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.22/0.57           = (k3_xboole_0 @ X5 @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      (![X5 : $i, X6 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.22/0.57           = (k3_xboole_0 @ X5 @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.57           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.57  thf(t47_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      (![X3 : $i, X4 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4))
% 0.22/0.57           = (k4_xboole_0 @ X3 @ X4))),
% 0.22/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X1 @ X0)
% 0.22/0.57           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.57  thf(t94_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k2_xboole_0 @ A @ B ) =
% 0.22/0.57       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i]:
% 0.22/0.57         ((k2_xboole_0 @ X12 @ X13)
% 0.22/0.57           = (k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ 
% 0.22/0.57              (k3_xboole_0 @ X12 @ X13)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.22/0.57  thf(t91_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.57       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.22/0.57  thf('8', plain,
% 0.22/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.22/0.57           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.57  thf('9', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i]:
% 0.22/0.57         ((k2_xboole_0 @ X12 @ X13)
% 0.22/0.57           = (k5_xboole_0 @ X12 @ 
% 0.22/0.57              (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X12 @ X13))))),
% 0.22/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.57  thf('10', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.22/0.57           = (k5_xboole_0 @ X1 @ 
% 0.22/0.57              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))))),
% 0.22/0.57      inference('sup+', [status(thm)], ['6', '9'])).
% 0.22/0.57  thf(t92_xboole_1, axiom,
% 0.22/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.57  thf('11', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.22/0.57           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.22/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.57  thf(t5_boole, axiom,
% 0.22/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.57  thf('13', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.22/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.57  thf('14', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 0.22/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.57  thf(t98_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      (![X14 : $i, X15 : $i]:
% 0.22/0.57         ((k2_xboole_0 @ X14 @ X15)
% 0.22/0.57           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.57  thf('16', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.22/0.57           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.57           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['16', '17'])).
% 0.22/0.57  thf(commutativity_k5_xboole_0, axiom,
% 0.22/0.57    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.22/0.57  thf('19', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.22/0.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.57  thf('20', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.22/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.57  thf('21', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.57      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['18', '21'])).
% 0.22/0.57  thf('23', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.57           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['15', '22'])).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.22/0.57           = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.57      inference('sup+', [status(thm)], ['14', '23'])).
% 0.22/0.57  thf('25', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.57  thf('26', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.22/0.57      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.57  thf('27', plain,
% 0.22/0.57      (![X5 : $i, X6 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.22/0.57           = (k3_xboole_0 @ X5 @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 0.22/0.57           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.22/0.57      inference('sup+', [status(thm)], ['26', '27'])).
% 0.22/0.57  thf(t3_boole, axiom,
% 0.22/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.57  thf('29', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.22/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.57  thf('30', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.57           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.22/0.57      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i]:
% 0.22/0.57         ((k2_xboole_0 @ X12 @ X13)
% 0.22/0.57           = (k5_xboole_0 @ X12 @ 
% 0.22/0.57              (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X12 @ X13))))),
% 0.22/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.22/0.57           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.22/0.57              (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.22/0.57      inference('sup+', [status(thm)], ['30', '31'])).
% 0.22/0.57  thf('33', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.22/0.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['18', '21'])).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['33', '34'])).
% 0.22/0.57  thf('36', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.22/0.57      inference('demod', [status(thm)], ['32', '35'])).
% 0.22/0.57  thf('37', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.22/0.57      inference('sup+', [status(thm)], ['1', '36'])).
% 0.22/0.57  thf('38', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.57           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['15', '22'])).
% 0.22/0.57  thf('39', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.22/0.57           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.22/0.57      inference('sup+', [status(thm)], ['37', '38'])).
% 0.22/0.57  thf('40', plain,
% 0.22/0.57      (![X3 : $i, X4 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4))
% 0.22/0.57           = (k4_xboole_0 @ X3 @ X4))),
% 0.22/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.22/0.57  thf('41', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.22/0.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.57  thf('42', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.57      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.22/0.57  thf('43', plain,
% 0.22/0.57      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('demod', [status(thm)], ['0', '42'])).
% 0.22/0.57  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.42/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
