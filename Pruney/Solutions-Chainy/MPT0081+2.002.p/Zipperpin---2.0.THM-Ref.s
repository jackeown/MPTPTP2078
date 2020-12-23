%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GmDCyFrjYo

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 139 expanded)
%              Number of leaves         :   17 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  475 (1026 expanded)
%              Number of equality atoms :   55 ( 121 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t74_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t74_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
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

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['6','11'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['15','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['14','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['1','25'])).

thf('27',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['41','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GmDCyFrjYo
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:46:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 193 iterations in 0.082s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(t74_xboole_1, conjecture,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.21/0.54          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.54        ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.21/0.54             ( r1_xboole_0 @ A @ B ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t74_xboole_1])).
% 0.21/0.54  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t48_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.21/0.54           = (k3_xboole_0 @ X9 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.54  thf('2', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d7_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.54       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i]:
% 0.21/0.54         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.54  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.54  thf(t51_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.21/0.54       ( A ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k4_xboole_0 @ X11 @ X12))
% 0.21/0.54           = (X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.21/0.54      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf(t2_boole, axiom,
% 0.21/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k4_xboole_0 @ X11 @ X12))
% 0.21/0.54           = (X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf(t3_boole, axiom,
% 0.21/0.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.54  thf('10', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.54  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('12', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['6', '11'])).
% 0.21/0.54  thf(t52_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.21/0.54       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.54           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 0.21/0.54              (k3_xboole_0 @ X13 @ X15)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.21/0.54           = (k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.21/0.54           = (k3_xboole_0 @ X9 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.21/0.54           = (k3_xboole_0 @ X9 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.54  thf(t39_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X6 : $i, X7 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.21/0.54           = (k2_xboole_0 @ X6 @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.54           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.21/0.54           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k4_xboole_0 @ X11 @ X12))
% 0.21/0.54           = (X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['15', '23'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) = (sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['14', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) = (sk_A))),
% 0.21/0.54      inference('sup+', [status(thm)], ['1', '25'])).
% 0.21/0.54  thf('27', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.21/0.54           = (k3_xboole_0 @ X9 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.54  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.21/0.54           = (k3_xboole_0 @ X9 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.54  thf('34', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.54  thf('35', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.54           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 0.21/0.54              (k3_xboole_0 @ X13 @ X15)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X2 @ X1))
% 0.21/0.54           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.21/0.54           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['35', '38'])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.21/0.54           = (k3_xboole_0 @ X9 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X0 @ X0)
% 0.21/0.54           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (![X2 : $i, X4 : $i]:
% 0.21/0.54         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.54          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.21/0.54      inference('sup+', [status(thm)], ['41', '49'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['26', '50'])).
% 0.21/0.54  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
