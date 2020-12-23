%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9blKTwfDXg

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:15 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 150 expanded)
%              Number of leaves         :   19 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :  606 (1119 expanded)
%              Number of equality atoms :   73 ( 142 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t53_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) @ X17 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('31',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','36'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('45',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38','50'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('55',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','56','57'])).

thf('59',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','58'])).

thf('60',plain,(
    $false ),
    inference(simplify,[status(thm)],['59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9blKTwfDXg
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:58:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.47/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.71  % Solved by: fo/fo7.sh
% 0.47/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.71  % done 407 iterations in 0.251s
% 0.47/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.71  % SZS output start Refutation
% 0.47/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.47/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.71  thf(t100_xboole_1, conjecture,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.47/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.71    (~( ![A:$i,B:$i]:
% 0.47/0.71        ( ( k4_xboole_0 @ A @ B ) =
% 0.47/0.71          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.47/0.71    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.47/0.71  thf('0', plain,
% 0.47/0.71      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.47/0.71         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(t47_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.47/0.71  thf('1', plain,
% 0.47/0.71      (![X8 : $i, X9 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.47/0.71           = (k4_xboole_0 @ X8 @ X9))),
% 0.47/0.71      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.47/0.71  thf(d6_xboole_0, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( k5_xboole_0 @ A @ B ) =
% 0.47/0.71       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.47/0.71  thf('2', plain,
% 0.47/0.71      (![X2 : $i, X3 : $i]:
% 0.47/0.71         ((k5_xboole_0 @ X2 @ X3)
% 0.47/0.71           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.47/0.71      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.47/0.71  thf('3', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.47/0.71           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.47/0.71              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.47/0.71      inference('sup+', [status(thm)], ['1', '2'])).
% 0.47/0.71  thf(t3_boole, axiom,
% 0.47/0.71    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.71  thf('4', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.47/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.71  thf(t48_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.71  thf('5', plain,
% 0.47/0.71      (![X10 : $i, X11 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.47/0.71           = (k3_xboole_0 @ X10 @ X11))),
% 0.47/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.71  thf('6', plain,
% 0.47/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['4', '5'])).
% 0.47/0.71  thf(t2_boole, axiom,
% 0.47/0.71    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.71  thf('7', plain,
% 0.47/0.71      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.71      inference('cnf', [status(esa)], [t2_boole])).
% 0.47/0.71  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.71      inference('demod', [status(thm)], ['6', '7'])).
% 0.47/0.71  thf(t49_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i]:
% 0.47/0.71     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.47/0.71       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.47/0.71  thf('9', plain,
% 0.47/0.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.71         ((k3_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 0.47/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14))),
% 0.47/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.47/0.71  thf('10', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k3_xboole_0 @ X1 @ k1_xboole_0)
% 0.47/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.47/0.71  thf('11', plain,
% 0.47/0.71      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.71      inference('cnf', [status(esa)], [t2_boole])).
% 0.47/0.71  thf('12', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.47/0.71      inference('demod', [status(thm)], ['10', '11'])).
% 0.47/0.71  thf(t53_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i]:
% 0.47/0.71     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.47/0.71       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.47/0.71  thf('13', plain,
% 0.47/0.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 0.47/0.71           = (k3_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ 
% 0.47/0.71              (k4_xboole_0 @ X15 @ X17)))),
% 0.47/0.71      inference('cnf', [status(esa)], [t53_xboole_1])).
% 0.47/0.71  thf('14', plain,
% 0.47/0.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.71         ((k3_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 0.47/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14))),
% 0.47/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.47/0.71  thf('15', plain,
% 0.47/0.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 0.47/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X15) @ 
% 0.47/0.71              X17))),
% 0.47/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.47/0.71  thf('16', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['12', '15'])).
% 0.47/0.71  thf('17', plain,
% 0.47/0.71      (![X10 : $i, X11 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.47/0.71           = (k3_xboole_0 @ X10 @ X11))),
% 0.47/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.71  thf('18', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.47/0.71           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.71      inference('sup+', [status(thm)], ['16', '17'])).
% 0.47/0.71  thf('19', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.47/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.71  thf('20', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.71      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.71  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.71      inference('demod', [status(thm)], ['6', '7'])).
% 0.47/0.71  thf('22', plain,
% 0.47/0.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.71         ((k3_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 0.47/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14))),
% 0.47/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.47/0.71  thf('23', plain,
% 0.47/0.71      (![X8 : $i, X9 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.47/0.71           = (k4_xboole_0 @ X8 @ X9))),
% 0.47/0.71      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.47/0.71  thf('24', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 0.47/0.71           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.47/0.71      inference('sup+', [status(thm)], ['22', '23'])).
% 0.47/0.71  thf('25', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.47/0.71           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.47/0.71      inference('sup+', [status(thm)], ['21', '24'])).
% 0.47/0.71  thf('26', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.47/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.71  thf('27', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.47/0.71      inference('demod', [status(thm)], ['10', '11'])).
% 0.47/0.71  thf('28', plain,
% 0.47/0.71      (![X2 : $i, X3 : $i]:
% 0.47/0.71         ((k5_xboole_0 @ X2 @ X3)
% 0.47/0.71           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.47/0.71      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.47/0.71  thf('29', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.47/0.71           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.47/0.71              k1_xboole_0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['27', '28'])).
% 0.47/0.71  thf(t40_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.47/0.71  thf('30', plain,
% 0.47/0.71      (![X6 : $i, X7 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 0.47/0.71           = (k4_xboole_0 @ X6 @ X7))),
% 0.47/0.71      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.47/0.71  thf('31', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.47/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.71  thf('32', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['30', '31'])).
% 0.47/0.71  thf('33', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.47/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.71  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['32', '33'])).
% 0.47/0.71  thf('35', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.47/0.71           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.47/0.71      inference('demod', [status(thm)], ['29', '34'])).
% 0.47/0.71  thf('36', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((X1)
% 0.47/0.71           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.47/0.71      inference('demod', [status(thm)], ['25', '26', '35'])).
% 0.47/0.71  thf('37', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((X0)
% 0.47/0.71           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 0.47/0.71      inference('sup+', [status(thm)], ['20', '36'])).
% 0.47/0.71  thf(commutativity_k5_xboole_0, axiom,
% 0.47/0.71    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.47/0.71  thf('38', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.47/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.47/0.71  thf('39', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['12', '15'])).
% 0.47/0.71  thf('40', plain,
% 0.47/0.71      (![X2 : $i, X3 : $i]:
% 0.47/0.71         ((k5_xboole_0 @ X2 @ X3)
% 0.47/0.71           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.47/0.71      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.47/0.71  thf('41', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.47/0.71           = (k2_xboole_0 @ k1_xboole_0 @ 
% 0.47/0.71              (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 0.47/0.71      inference('sup+', [status(thm)], ['39', '40'])).
% 0.47/0.71  thf('42', plain,
% 0.47/0.71      (![X6 : $i, X7 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 0.47/0.71           = (k4_xboole_0 @ X6 @ X7))),
% 0.47/0.71      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.47/0.71  thf(t98_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.47/0.71  thf('43', plain,
% 0.47/0.71      (![X19 : $i, X20 : $i]:
% 0.47/0.71         ((k2_xboole_0 @ X19 @ X20)
% 0.47/0.71           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.47/0.71      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.47/0.71  thf('44', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.47/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.47/0.71  thf(t5_boole, axiom,
% 0.47/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.71  thf('45', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.47/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.47/0.71  thf('46', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['44', '45'])).
% 0.47/0.71  thf('47', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['43', '46'])).
% 0.47/0.71  thf('48', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.47/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.71  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['47', '48'])).
% 0.47/0.71  thf('50', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.47/0.71           = (k4_xboole_0 @ X1 @ X0))),
% 0.47/0.71      inference('demod', [status(thm)], ['41', '42', '49'])).
% 0.47/0.71  thf('51', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.47/0.71      inference('demod', [status(thm)], ['37', '38', '50'])).
% 0.47/0.71  thf('52', plain,
% 0.47/0.71      (![X10 : $i, X11 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.47/0.71           = (k3_xboole_0 @ X10 @ X11))),
% 0.47/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.71  thf('53', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X0 @ X0)
% 0.47/0.71           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.47/0.71      inference('sup+', [status(thm)], ['51', '52'])).
% 0.47/0.71  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.71      inference('demod', [status(thm)], ['6', '7'])).
% 0.47/0.71  thf('55', plain,
% 0.47/0.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.71         ((k3_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 0.47/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14))),
% 0.47/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.47/0.71  thf('56', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.47/0.71      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.47/0.71  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['32', '33'])).
% 0.47/0.71  thf('58', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.47/0.71           = (k4_xboole_0 @ X1 @ X0))),
% 0.47/0.71      inference('demod', [status(thm)], ['3', '56', '57'])).
% 0.47/0.71  thf('59', plain,
% 0.47/0.71      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)], ['0', '58'])).
% 0.47/0.71  thf('60', plain, ($false), inference('simplify', [status(thm)], ['59'])).
% 0.47/0.71  
% 0.47/0.71  % SZS output end Refutation
% 0.47/0.71  
% 0.55/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
