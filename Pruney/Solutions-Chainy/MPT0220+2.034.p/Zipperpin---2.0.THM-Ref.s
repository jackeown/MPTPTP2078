%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nV68mvgAtN

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:22 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   80 (  98 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  527 ( 661 expanded)
%              Number of equality atoms :   67 (  85 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t14_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t14_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X50: $i,X51: $i] :
      ( r1_tarski @ ( k1_tarski @ X50 ) @ ( k2_tarski @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) @ k1_xboole_0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('31',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['18','49'])).

thf('51',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','52'])).

thf('54',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nV68mvgAtN
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.61  % Solved by: fo/fo7.sh
% 0.35/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.61  % done 413 iterations in 0.165s
% 0.35/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.61  % SZS output start Refutation
% 0.35/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.61  thf(t14_zfmisc_1, conjecture,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.35/0.61       ( k2_tarski @ A @ B ) ))).
% 0.35/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.61    (~( ![A:$i,B:$i]:
% 0.35/0.61        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.35/0.61          ( k2_tarski @ A @ B ) ) )),
% 0.35/0.61    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.35/0.61  thf('0', plain,
% 0.35/0.61      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.35/0.61         != (k2_tarski @ sk_A @ sk_B))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(t12_zfmisc_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.35/0.61  thf('1', plain,
% 0.35/0.61      (![X50 : $i, X51 : $i]:
% 0.35/0.61         (r1_tarski @ (k1_tarski @ X50) @ (k2_tarski @ X50 @ X51))),
% 0.35/0.61      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.35/0.61  thf(l32_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.61  thf('2', plain,
% 0.35/0.61      (![X4 : $i, X6 : $i]:
% 0.35/0.61         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.35/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.35/0.61  thf('3', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.35/0.61           = (k1_xboole_0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.61  thf(t51_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.35/0.61       ( A ) ))).
% 0.35/0.61  thf('4', plain,
% 0.35/0.61      (![X15 : $i, X16 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 0.35/0.61           = (X15))),
% 0.35/0.61      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.35/0.61  thf('5', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ 
% 0.35/0.61           (k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1)) @ 
% 0.35/0.61           k1_xboole_0) = (k1_tarski @ X0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.61  thf(t1_boole, axiom,
% 0.35/0.61    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.61  thf('6', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.35/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.35/0.61  thf('7', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.35/0.61           = (k1_tarski @ X0))),
% 0.35/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.35/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.35/0.61  thf('8', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.35/0.61  thf('9', plain,
% 0.35/0.61      (![X15 : $i, X16 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 0.35/0.61           = (X15))),
% 0.35/0.61      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.35/0.61  thf('10', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.35/0.61           = (X0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['8', '9'])).
% 0.35/0.61  thf(t46_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.35/0.61  thf('11', plain,
% 0.35/0.61      (![X13 : $i, X14 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 0.35/0.61      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.35/0.61  thf('12', plain,
% 0.35/0.61      (![X15 : $i, X16 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 0.35/0.61           = (X15))),
% 0.35/0.61      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.35/0.61  thf('13', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 0.35/0.61           k1_xboole_0) = (X0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['11', '12'])).
% 0.35/0.61  thf('14', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.35/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.35/0.61  thf('15', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 0.35/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.35/0.61  thf('16', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.35/0.61           = (k3_xboole_0 @ X1 @ X0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['10', '15'])).
% 0.35/0.61  thf('17', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.35/0.61  thf('18', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.35/0.61           = (k3_xboole_0 @ X1 @ X0))),
% 0.35/0.61      inference('demod', [status(thm)], ['16', '17'])).
% 0.35/0.61  thf(t100_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.61  thf('19', plain,
% 0.35/0.61      (![X7 : $i, X8 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ X7 @ X8)
% 0.35/0.61           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.61  thf(commutativity_k5_xboole_0, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.35/0.61  thf('20', plain,
% 0.35/0.61      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.35/0.61      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.35/0.61  thf(t22_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.35/0.61  thf('21', plain,
% 0.35/0.61      (![X10 : $i, X11 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.35/0.61      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.35/0.61  thf('22', plain,
% 0.35/0.61      (![X13 : $i, X14 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 0.35/0.61      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.35/0.61  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.35/0.61  thf('24', plain,
% 0.35/0.61      (![X15 : $i, X16 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 0.35/0.61           = (X15))),
% 0.35/0.61      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.35/0.61  thf('25', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0) = (X0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['23', '24'])).
% 0.35/0.61  thf('26', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.35/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.35/0.61  thf('27', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.35/0.61      inference('demod', [status(thm)], ['25', '26'])).
% 0.35/0.61  thf('28', plain,
% 0.35/0.61      (![X7 : $i, X8 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ X7 @ X8)
% 0.35/0.61           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.61  thf('29', plain,
% 0.35/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['27', '28'])).
% 0.35/0.61  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.35/0.61  thf('31', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.35/0.61  thf(t91_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.35/0.61       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.35/0.61  thf('32', plain,
% 0.35/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.35/0.61         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.35/0.61           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.35/0.61  thf('33', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.35/0.61           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.35/0.61      inference('sup+', [status(thm)], ['31', '32'])).
% 0.35/0.61  thf('34', plain,
% 0.35/0.61      (![X7 : $i, X8 : $i]:
% 0.35/0.61         ((k4_xboole_0 @ X7 @ X8)
% 0.35/0.61           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.61  thf(t3_boole, axiom,
% 0.35/0.61    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.61  thf('35', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.35/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.35/0.61  thf(t98_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.35/0.61  thf('36', plain,
% 0.35/0.61      (![X20 : $i, X21 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ X20 @ X21)
% 0.35/0.61           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.35/0.61  thf('37', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['35', '36'])).
% 0.35/0.61  thf('38', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.35/0.61           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['34', '37'])).
% 0.35/0.61  thf('39', plain,
% 0.35/0.61      (![X10 : $i, X11 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.35/0.61      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.35/0.61  thf('40', plain,
% 0.35/0.61      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.35/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.35/0.61  thf('41', plain,
% 0.35/0.61      (![X20 : $i, X21 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ X20 @ X21)
% 0.35/0.61           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.35/0.61  thf('42', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['40', '41'])).
% 0.35/0.61  thf('43', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.35/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.35/0.61  thf('44', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.61      inference('demod', [status(thm)], ['42', '43'])).
% 0.35/0.61  thf('45', plain,
% 0.35/0.61      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.35/0.61      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.35/0.61  thf('46', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['44', '45'])).
% 0.35/0.61  thf('47', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.35/0.61      inference('demod', [status(thm)], ['33', '46'])).
% 0.35/0.61  thf('48', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.35/0.61      inference('sup+', [status(thm)], ['20', '47'])).
% 0.35/0.61  thf('49', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((X1)
% 0.35/0.61           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.35/0.61      inference('sup+', [status(thm)], ['19', '48'])).
% 0.35/0.61  thf('50', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((X0)
% 0.35/0.61           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.35/0.61              (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.35/0.61      inference('sup+', [status(thm)], ['18', '49'])).
% 0.35/0.61  thf('51', plain,
% 0.35/0.61      (![X20 : $i, X21 : $i]:
% 0.35/0.61         ((k2_xboole_0 @ X20 @ X21)
% 0.35/0.61           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.35/0.61  thf('52', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.35/0.61      inference('demod', [status(thm)], ['50', '51'])).
% 0.35/0.61  thf('53', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((k2_tarski @ X0 @ X1)
% 0.35/0.61           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1)))),
% 0.35/0.61      inference('sup+', [status(thm)], ['7', '52'])).
% 0.35/0.61  thf('54', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.35/0.61      inference('demod', [status(thm)], ['0', '53'])).
% 0.35/0.61  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.35/0.61  
% 0.35/0.61  % SZS output end Refutation
% 0.35/0.61  
% 0.35/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
