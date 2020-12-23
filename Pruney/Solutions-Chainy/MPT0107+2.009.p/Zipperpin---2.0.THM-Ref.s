%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fremqzxQtL

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:11 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 233 expanded)
%              Number of leaves         :   21 (  83 expanded)
%              Depth                    :   16
%              Number of atoms          :  545 (1648 expanded)
%              Number of equality atoms :   70 ( 225 expanded)
%              Maximal formula depth    :    9 (   6 average)

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

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_xboole_0 @ X31 @ X32 )
      = ( k5_xboole_0 @ X31 @ ( k4_xboole_0 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_xboole_0 @ X31 @ X32 )
      = ( k5_xboole_0 @ X31 @ ( k4_xboole_0 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('12',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_xboole_0 @ X31 @ X32 )
      = ( k5_xboole_0 @ X31 @ ( k4_xboole_0 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ ( k3_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('27',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k5_xboole_0 @ X30 @ ( k3_xboole_0 @ X29 @ X30 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','32'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('46',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','32'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fremqzxQtL
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:33:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 462 iterations in 0.211s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(t100_xboole_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i]:
% 0.45/0.65        ( ( k4_xboole_0 @ A @ B ) =
% 0.45/0.65          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.45/0.65         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t47_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X12 : $i, X13 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.45/0.65           = (k4_xboole_0 @ X12 @ X13))),
% 0.45/0.65      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.45/0.65  thf(t98_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X31 : $i, X32 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X31 @ X32)
% 0.45/0.65           = (k5_xboole_0 @ X31 @ (k4_xboole_0 @ X32 @ X31)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.45/0.65           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['1', '2'])).
% 0.45/0.65  thf(commutativity_k2_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.65           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X31 : $i, X32 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X31 @ X32)
% 0.45/0.65           = (k5_xboole_0 @ X31 @ (k4_xboole_0 @ X32 @ X31)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.65  thf(commutativity_k5_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.45/0.65  thf(t5_boole, axiom,
% 0.45/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.65  thf('8', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 0.45/0.66      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.66  thf('9', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['7', '8'])).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['6', '9'])).
% 0.45/0.66  thf(idempotence_k2_xboole_0, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.66  thf('11', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X31 : $i, X32 : $i]:
% 0.45/0.66         ((k2_xboole_0 @ X31 @ X32)
% 0.45/0.66           = (k5_xboole_0 @ X31 @ (k4_xboole_0 @ X32 @ X31)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.66  thf(t92_xboole_1, axiom,
% 0.45/0.66    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.45/0.66  thf('13', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ X28) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.45/0.66  thf(t91_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.66       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 0.45/0.66           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.45/0.66           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['13', '14'])).
% 0.45/0.66  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['7', '8'])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.66           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['12', '17'])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['11', '18'])).
% 0.45/0.66  thf('20', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ X28) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.45/0.66  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['19', '20'])).
% 0.45/0.66  thf(t48_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (![X14 : $i, X15 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.45/0.66           = (k3_xboole_0 @ X14 @ X15))),
% 0.45/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['21', '22'])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['6', '9'])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf(t94_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k2_xboole_0 @ A @ B ) =
% 0.45/0.66       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (![X29 : $i, X30 : $i]:
% 0.45/0.66         ((k2_xboole_0 @ X29 @ X30)
% 0.45/0.66           = (k5_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ 
% 0.45/0.66              (k3_xboole_0 @ X29 @ X30)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 0.45/0.66           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      (![X29 : $i, X30 : $i]:
% 0.45/0.66         ((k2_xboole_0 @ X29 @ X30)
% 0.45/0.66           = (k5_xboole_0 @ X29 @ 
% 0.45/0.66              (k5_xboole_0 @ X30 @ (k3_xboole_0 @ X29 @ X30))))),
% 0.45/0.66      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['25', '28'])).
% 0.45/0.66  thf('30', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.45/0.66  thf('31', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['23', '24', '31'])).
% 0.45/0.66  thf('33', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['10', '32'])).
% 0.45/0.66  thf(t52_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.45/0.66       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.45/0.66           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 0.45/0.66              (k3_xboole_0 @ X21 @ X23)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 0.45/0.66           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['33', '34'])).
% 0.45/0.66  thf('36', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf(t51_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.45/0.66       ( A ) ))).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (![X19 : $i, X20 : $i]:
% 0.45/0.66         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 0.45/0.66           = (X19))),
% 0.45/0.66      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.45/0.66  thf('38', plain,
% 0.45/0.66      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['36', '37'])).
% 0.45/0.66  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['19', '20'])).
% 0.45/0.66  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.45/0.66  thf('41', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.66  thf(t40_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.66  thf('42', plain,
% 0.45/0.66      (![X7 : $i, X8 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 0.45/0.66           = (k4_xboole_0 @ X7 @ X8))),
% 0.45/0.66      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.45/0.66           = (k4_xboole_0 @ X0 @ X1))),
% 0.45/0.66      inference('sup+', [status(thm)], ['41', '42'])).
% 0.45/0.66  thf('44', plain,
% 0.45/0.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['40', '43'])).
% 0.45/0.66  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['19', '20'])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.66  thf('47', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['10', '32'])).
% 0.45/0.66  thf('48', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['35', '46', '47'])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((X1)
% 0.45/0.66           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['5', '48'])).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('51', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.66           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['49', '50'])).
% 0.45/0.66  thf('52', plain,
% 0.45/0.66      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.45/0.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.45/0.66  thf('53', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.66  thf('54', plain,
% 0.45/0.66      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['0', '53'])).
% 0.45/0.66  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
