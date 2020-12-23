%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uCNq4LrYpB

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:54 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   63 (  84 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  460 ( 605 expanded)
%              Number of equality atoms :   55 (  76 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X32 @ X33 ) @ X34 )
      = ( k5_xboole_0 @ X32 @ ( k5_xboole_0 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('2',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k3_xboole_0 @ X25 @ X26 ) )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8','11','22','23'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t55_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X30 @ X31 ) @ ( k3_xboole_0 @ X30 @ X31 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X30 @ X31 ) @ ( k4_xboole_0 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t55_xboole_1])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('34',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X30 @ X31 ) @ ( k3_xboole_0 @ X30 @ X31 ) )
      = ( k5_xboole_0 @ X30 @ X31 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('37',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','24','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uCNq4LrYpB
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.71  % Solved by: fo/fo7.sh
% 0.50/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.71  % done 369 iterations in 0.253s
% 0.50/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.71  % SZS output start Refutation
% 0.50/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.50/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.50/0.71  thf(t94_xboole_1, conjecture,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( k2_xboole_0 @ A @ B ) =
% 0.50/0.71       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.50/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.71    (~( ![A:$i,B:$i]:
% 0.50/0.71        ( ( k2_xboole_0 @ A @ B ) =
% 0.50/0.71          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.50/0.71    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 0.50/0.71  thf('0', plain,
% 0.50/0.71      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.50/0.71         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 0.50/0.71             (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(t91_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.50/0.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.50/0.71  thf('1', plain,
% 0.50/0.71      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.50/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X32 @ X33) @ X34)
% 0.50/0.71           = (k5_xboole_0 @ X32 @ (k5_xboole_0 @ X33 @ X34)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.71  thf('2', plain,
% 0.50/0.71      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.50/0.71         != (k5_xboole_0 @ sk_A @ 
% 0.50/0.71             (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))))),
% 0.50/0.71      inference('demod', [status(thm)], ['0', '1'])).
% 0.50/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.50/0.71  thf('3', plain,
% 0.50/0.71      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.50/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.71  thf(t47_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.50/0.71  thf('4', plain,
% 0.50/0.71      (![X25 : $i, X26 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X25 @ (k3_xboole_0 @ X25 @ X26))
% 0.50/0.71           = (k4_xboole_0 @ X25 @ X26))),
% 0.50/0.71      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.50/0.71  thf('5', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.50/0.71           = (k4_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('sup+', [status(thm)], ['3', '4'])).
% 0.50/0.71  thf(d6_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( k5_xboole_0 @ A @ B ) =
% 0.50/0.71       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.50/0.71  thf('6', plain,
% 0.50/0.71      (![X4 : $i, X5 : $i]:
% 0.50/0.71         ((k5_xboole_0 @ X4 @ X5)
% 0.50/0.71           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 0.50/0.71      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.50/0.71  thf('7', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.50/0.71           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.50/0.71              (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['5', '6'])).
% 0.50/0.71  thf(t49_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.50/0.71       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.50/0.71  thf('8', plain,
% 0.50/0.71      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.50/0.71         ((k3_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X29))
% 0.50/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ X29))),
% 0.50/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.50/0.71  thf(idempotence_k2_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.50/0.71  thf('9', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.50/0.71      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.50/0.71  thf(t46_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.50/0.71  thf('10', plain,
% 0.50/0.71      (![X23 : $i, X24 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X23 @ (k2_xboole_0 @ X23 @ X24)) = (k1_xboole_0))),
% 0.50/0.71      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.50/0.71  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.50/0.71  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.50/0.71  thf(t39_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.71  thf('13', plain,
% 0.50/0.71      (![X20 : $i, X21 : $i]:
% 0.50/0.71         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 0.50/0.71           = (k2_xboole_0 @ X20 @ X21))),
% 0.50/0.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.50/0.71  thf('14', plain,
% 0.50/0.71      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['12', '13'])).
% 0.50/0.71  thf('15', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.50/0.71      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.50/0.71  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['14', '15'])).
% 0.50/0.71  thf(commutativity_k2_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.50/0.71  thf('17', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.50/0.71  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['16', '17'])).
% 0.50/0.71  thf(t21_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.50/0.71  thf('19', plain,
% 0.50/0.71      (![X7 : $i, X8 : $i]:
% 0.50/0.71         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (X7))),
% 0.50/0.71      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.50/0.71  thf('20', plain,
% 0.50/0.71      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['18', '19'])).
% 0.50/0.71  thf('21', plain,
% 0.50/0.71      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.50/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.71  thf('22', plain,
% 0.50/0.71      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['20', '21'])).
% 0.50/0.71  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['14', '15'])).
% 0.50/0.71  thf('24', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.50/0.71           = (k4_xboole_0 @ X1 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['7', '8', '11', '22', '23'])).
% 0.50/0.71  thf(t22_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.50/0.71  thf('25', plain,
% 0.50/0.71      (![X9 : $i, X10 : $i]:
% 0.50/0.71         ((k2_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)) = (X9))),
% 0.50/0.71      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.50/0.71  thf('26', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.50/0.71  thf('27', plain,
% 0.50/0.71      (![X23 : $i, X24 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X23 @ (k2_xboole_0 @ X23 @ X24)) = (k1_xboole_0))),
% 0.50/0.71      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.50/0.71  thf('28', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['26', '27'])).
% 0.50/0.71  thf('29', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['25', '28'])).
% 0.50/0.71  thf('30', plain,
% 0.50/0.71      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.50/0.71         ((k3_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X29))
% 0.50/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ X29))),
% 0.50/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.50/0.71  thf('31', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.50/0.71      inference('demod', [status(thm)], ['29', '30'])).
% 0.50/0.71  thf(t55_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) =
% 0.50/0.71       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.50/0.71  thf('32', plain,
% 0.50/0.71      (![X30 : $i, X31 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ (k2_xboole_0 @ X30 @ X31) @ (k3_xboole_0 @ X30 @ X31))
% 0.50/0.71           = (k2_xboole_0 @ (k4_xboole_0 @ X30 @ X31) @ 
% 0.50/0.71              (k4_xboole_0 @ X31 @ X30)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t55_xboole_1])).
% 0.50/0.71  thf('33', plain,
% 0.50/0.71      (![X4 : $i, X5 : $i]:
% 0.50/0.71         ((k5_xboole_0 @ X4 @ X5)
% 0.50/0.71           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 0.50/0.71      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.50/0.71  thf('34', plain,
% 0.50/0.71      (![X30 : $i, X31 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ (k2_xboole_0 @ X30 @ X31) @ (k3_xboole_0 @ X30 @ X31))
% 0.50/0.71           = (k5_xboole_0 @ X30 @ X31))),
% 0.50/0.71      inference('demod', [status(thm)], ['32', '33'])).
% 0.50/0.71  thf('35', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.50/0.71           k1_xboole_0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['31', '34'])).
% 0.50/0.71  thf('36', plain,
% 0.50/0.71      (![X20 : $i, X21 : $i]:
% 0.50/0.71         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 0.50/0.71           = (k2_xboole_0 @ X20 @ X21))),
% 0.50/0.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.50/0.71  thf(t3_boole, axiom,
% 0.50/0.71    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.50/0.71  thf('37', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.50/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.50/0.71  thf('38', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k2_xboole_0 @ X0 @ X1)
% 0.50/0.71           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.50/0.71      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.50/0.71  thf('39', plain,
% 0.50/0.71      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['2', '24', '38'])).
% 0.50/0.71  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 0.50/0.71  
% 0.50/0.71  % SZS output end Refutation
% 0.50/0.71  
% 0.50/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
