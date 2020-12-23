%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pZQQhjwuOR

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:14 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 159 expanded)
%              Number of leaves         :   16 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  481 (1118 expanded)
%              Number of equality atoms :   62 ( 151 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','24'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X6 )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['16','40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','46','49'])).

thf('51',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','50'])).

thf('52',plain,(
    $false ),
    inference(simplify,[status(thm)],['51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pZQQhjwuOR
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:31:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 334 iterations in 0.170s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(t100_xboole_1, conjecture,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i,B:$i]:
% 0.37/0.61        ( ( k4_xboole_0 @ A @ B ) =
% 0.37/0.61          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.37/0.61         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.37/0.61         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.37/0.61      inference('demod', [status(thm)], ['0', '1'])).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf(t47_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.37/0.61           = (k4_xboole_0 @ X7 @ X8))),
% 0.37/0.61      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.61           = (k4_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.61  thf(d6_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k5_xboole_0 @ A @ B ) =
% 0.37/0.61       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      (![X2 : $i, X3 : $i]:
% 0.37/0.61         ((k5_xboole_0 @ X2 @ X3)
% 0.37/0.61           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.37/0.61  thf('7', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.37/0.61           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.37/0.61              (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.61  thf('8', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf(t48_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.37/0.61           = (k3_xboole_0 @ X9 @ X10))),
% 0.37/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.37/0.61           = (k3_xboole_0 @ X9 @ X10))),
% 0.37/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.61  thf('11', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.37/0.61           = (k3_xboole_0 @ X9 @ X10))),
% 0.37/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.61           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['10', '11'])).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.37/0.61           = (k4_xboole_0 @ X7 @ X8))),
% 0.37/0.61      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.37/0.61           = (k4_xboole_0 @ X1 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['12', '13'])).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.61           = (k4_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.37/0.61           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.61  thf(t3_boole, axiom,
% 0.37/0.61    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.61  thf('17', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.37/0.61           = (k3_xboole_0 @ X9 @ X10))),
% 0.37/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.61  thf('19', plain,
% 0.37/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['17', '18'])).
% 0.37/0.61  thf('20', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.37/0.61           = (k3_xboole_0 @ X9 @ X10))),
% 0.37/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.61  thf(t4_boole, axiom,
% 0.37/0.61    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.61  thf('21', plain,
% 0.37/0.61      (![X11 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [t4_boole])).
% 0.37/0.61  thf('22', plain,
% 0.37/0.61      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['20', '21'])).
% 0.37/0.61  thf('23', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.61  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['19', '24'])).
% 0.37/0.61  thf(t98_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      (![X12 : $i, X13 : $i]:
% 0.37/0.61         ((k2_xboole_0 @ X12 @ X13)
% 0.37/0.61           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.37/0.61  thf('27', plain,
% 0.37/0.61      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['25', '26'])).
% 0.37/0.61  thf('28', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      (![X2 : $i, X3 : $i]:
% 0.37/0.61         ((k5_xboole_0 @ X2 @ X3)
% 0.37/0.61           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.37/0.61           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['28', '29'])).
% 0.37/0.61  thf('31', plain,
% 0.37/0.61      (![X11 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [t4_boole])).
% 0.37/0.61  thf('32', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['30', '31'])).
% 0.37/0.61  thf(t40_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.61  thf('33', plain,
% 0.37/0.61      (![X5 : $i, X6 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X6)
% 0.37/0.61           = (k4_xboole_0 @ X5 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.37/0.61  thf('34', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.37/0.61           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['32', '33'])).
% 0.37/0.61  thf('35', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.61  thf('36', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.61  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.61      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.37/0.61  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.61      inference('demod', [status(thm)], ['27', '37'])).
% 0.37/0.61  thf('39', plain,
% 0.37/0.61      (![X2 : $i, X3 : $i]:
% 0.37/0.61         ((k5_xboole_0 @ X2 @ X3)
% 0.37/0.61           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.37/0.61  thf('40', plain,
% 0.37/0.61      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['38', '39'])).
% 0.37/0.61  thf('41', plain,
% 0.37/0.61      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['38', '39'])).
% 0.37/0.61  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['19', '24'])).
% 0.37/0.61  thf('43', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['41', '42'])).
% 0.37/0.61  thf('44', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.37/0.61      inference('demod', [status(thm)], ['16', '40', '43'])).
% 0.37/0.61  thf('45', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['9', '44'])).
% 0.37/0.61  thf('46', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['8', '45'])).
% 0.37/0.61  thf('47', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['30', '31'])).
% 0.37/0.61  thf('48', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.61      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.37/0.61  thf('49', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.37/0.62  thf('50', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.37/0.62           = (k4_xboole_0 @ X1 @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['7', '46', '49'])).
% 0.37/0.62  thf('51', plain,
% 0.37/0.62      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.62      inference('demod', [status(thm)], ['2', '50'])).
% 0.37/0.62  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
