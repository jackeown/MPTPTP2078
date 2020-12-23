%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nkp3Dy2888

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:57 EST 2020

% Result     : Theorem 10.23s
% Output     : Refutation 10.23s
% Verified   : 
% Statistics : Number of formulae       :  240 (5120 expanded)
%              Number of leaves         :   23 (1842 expanded)
%              Depth                    :   31
%              Number of atoms          : 2131 (40947 expanded)
%              Number of equality atoms :  232 (5112 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ ( k3_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
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

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t54_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17','20'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27','30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17','20'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('46',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('48',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['43','44','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t55_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t55_xboole_1])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('62',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ ( k3_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('67',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('71',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('72',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('76',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74','77'])).

thf('79',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('83',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['80','81','88','89'])).

thf('91',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['70','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','93'])).

thf('95',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('96',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('97',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('103',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('110',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['108','111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['101','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17','20'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95','114','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','120'])).

thf('122',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('123',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('124',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['11','59','121','122','127'])).

thf('129',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t55_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('138',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['136','142'])).

thf('144',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['133','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['132','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95','114','119'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74','77'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('156',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['108','111','112'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['154','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('163',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['161','164'])).

thf('166',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95','114','119'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('173',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['108','111','112'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['178','183','184','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['171','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['170','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['167','168','169','193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95','114','119'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('198',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('207',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['203','204','205','206','207','208','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['196','210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','213'])).

thf('215',plain,(
    $false ),
    inference(simplify,[status(thm)],['214'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nkp3Dy2888
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:22:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 10.23/10.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.23/10.47  % Solved by: fo/fo7.sh
% 10.23/10.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.23/10.47  % done 9647 iterations in 10.005s
% 10.23/10.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.23/10.47  % SZS output start Refutation
% 10.23/10.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 10.23/10.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 10.23/10.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.23/10.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 10.23/10.47  thf(sk_B_type, type, sk_B: $i).
% 10.23/10.47  thf(sk_A_type, type, sk_A: $i).
% 10.23/10.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 10.23/10.47  thf(t94_xboole_1, conjecture,
% 10.23/10.47    (![A:$i,B:$i]:
% 10.23/10.47     ( ( k2_xboole_0 @ A @ B ) =
% 10.23/10.47       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 10.23/10.47  thf(zf_stmt_0, negated_conjecture,
% 10.23/10.47    (~( ![A:$i,B:$i]:
% 10.23/10.47        ( ( k2_xboole_0 @ A @ B ) =
% 10.23/10.47          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 10.23/10.47    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 10.23/10.47  thf('0', plain,
% 10.23/10.47      (((k2_xboole_0 @ sk_A @ sk_B)
% 10.23/10.47         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 10.23/10.47             (k3_xboole_0 @ sk_A @ sk_B)))),
% 10.23/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.47  thf(t93_xboole_1, axiom,
% 10.23/10.47    (![A:$i,B:$i]:
% 10.23/10.47     ( ( k2_xboole_0 @ A @ B ) =
% 10.23/10.47       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 10.23/10.47  thf('1', plain,
% 10.23/10.47      (![X29 : $i, X30 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X29 @ X30)
% 10.23/10.47           = (k2_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ 
% 10.23/10.47              (k3_xboole_0 @ X29 @ X30)))),
% 10.23/10.47      inference('cnf', [status(esa)], [t93_xboole_1])).
% 10.23/10.47  thf(t21_xboole_1, axiom,
% 10.23/10.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 10.23/10.47  thf('2', plain,
% 10.23/10.47      (![X5 : $i, X6 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (X5))),
% 10.23/10.47      inference('cnf', [status(esa)], [t21_xboole_1])).
% 10.23/10.47  thf('3', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k5_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['1', '2'])).
% 10.23/10.47  thf(commutativity_k2_xboole_0, axiom,
% 10.23/10.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 10.23/10.47  thf('4', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf(t40_xboole_1, axiom,
% 10.23/10.47    (![A:$i,B:$i]:
% 10.23/10.47     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 10.23/10.47  thf('5', plain,
% 10.23/10.47      (![X10 : $i, X11 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 10.23/10.47           = (k4_xboole_0 @ X10 @ X11))),
% 10.23/10.47      inference('cnf', [status(esa)], [t40_xboole_1])).
% 10.23/10.47  thf('6', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 10.23/10.47           = (k4_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('sup+', [status(thm)], ['4', '5'])).
% 10.23/10.47  thf(t49_xboole_1, axiom,
% 10.23/10.47    (![A:$i,B:$i,C:$i]:
% 10.23/10.47     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 10.23/10.47       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 10.23/10.47  thf('7', plain,
% 10.23/10.47      (![X19 : $i, X20 : $i, X21 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 10.23/10.47           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 10.23/10.47      inference('cnf', [status(esa)], [t49_xboole_1])).
% 10.23/10.47  thf('8', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['6', '7'])).
% 10.23/10.47  thf('9', plain,
% 10.23/10.47      (![X19 : $i, X20 : $i, X21 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 10.23/10.47           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 10.23/10.47      inference('cnf', [status(esa)], [t49_xboole_1])).
% 10.23/10.47  thf('10', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 10.23/10.47           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['8', '9'])).
% 10.23/10.47  thf('11', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0) @ X1)
% 10.23/10.47           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1))),
% 10.23/10.47      inference('sup+', [status(thm)], ['3', '10'])).
% 10.23/10.47  thf(t1_boole, axiom,
% 10.23/10.47    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 10.23/10.47  thf('12', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 10.23/10.47      inference('cnf', [status(esa)], [t1_boole])).
% 10.23/10.47  thf(t46_xboole_1, axiom,
% 10.23/10.47    (![A:$i,B:$i]:
% 10.23/10.47     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 10.23/10.47  thf('13', plain,
% 10.23/10.47      (![X15 : $i, X16 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (k1_xboole_0))),
% 10.23/10.47      inference('cnf', [status(esa)], [t46_xboole_1])).
% 10.23/10.47  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['12', '13'])).
% 10.23/10.47  thf(t54_xboole_1, axiom,
% 10.23/10.47    (![A:$i,B:$i,C:$i]:
% 10.23/10.47     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 10.23/10.47       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 10.23/10.47  thf('15', plain,
% 10.23/10.47      (![X22 : $i, X23 : $i, X24 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X23 @ X24))
% 10.23/10.47           = (k2_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ 
% 10.23/10.47              (k4_xboole_0 @ X22 @ X24)))),
% 10.23/10.47      inference('cnf', [status(esa)], [t54_xboole_1])).
% 10.23/10.47  thf('16', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['14', '15'])).
% 10.23/10.47  thf('17', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf('18', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf('19', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 10.23/10.47      inference('cnf', [status(esa)], [t1_boole])).
% 10.23/10.47  thf('20', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['18', '19'])).
% 10.23/10.47  thf('21', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('demod', [status(thm)], ['16', '17', '20'])).
% 10.23/10.47  thf(t48_xboole_1, axiom,
% 10.23/10.47    (![A:$i,B:$i]:
% 10.23/10.47     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 10.23/10.47  thf('22', plain,
% 10.23/10.47      (![X17 : $i, X18 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 10.23/10.47           = (k3_xboole_0 @ X17 @ X18))),
% 10.23/10.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 10.23/10.47  thf(d6_xboole_0, axiom,
% 10.23/10.47    (![A:$i,B:$i]:
% 10.23/10.47     ( ( k5_xboole_0 @ A @ B ) =
% 10.23/10.47       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 10.23/10.47  thf('23', plain,
% 10.23/10.47      (![X2 : $i, X3 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X2 @ X3)
% 10.23/10.47           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 10.23/10.47      inference('cnf', [status(esa)], [d6_xboole_0])).
% 10.23/10.47  thf('24', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf('25', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k5_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['23', '24'])).
% 10.23/10.47  thf('26', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 10.23/10.47           (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))
% 10.23/10.47           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 10.23/10.47      inference('sup+', [status(thm)], ['22', '25'])).
% 10.23/10.47  thf(t41_xboole_1, axiom,
% 10.23/10.47    (![A:$i,B:$i,C:$i]:
% 10.23/10.47     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 10.23/10.47       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 10.23/10.47  thf('27', plain,
% 10.23/10.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 10.23/10.47           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 10.23/10.47      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.23/10.47  thf('28', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf('29', plain,
% 10.23/10.47      (![X15 : $i, X16 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (k1_xboole_0))),
% 10.23/10.47      inference('cnf', [status(esa)], [t46_xboole_1])).
% 10.23/10.47  thf('30', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['28', '29'])).
% 10.23/10.47  thf('31', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['18', '19'])).
% 10.23/10.47  thf('33', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X1 @ X0)
% 10.23/10.47           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 10.23/10.47      inference('demod', [status(thm)], ['26', '27', '30', '31', '32'])).
% 10.23/10.47  thf('34', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k5_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['23', '24'])).
% 10.23/10.47  thf('35', plain,
% 10.23/10.47      (![X2 : $i, X3 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X2 @ X3)
% 10.23/10.47           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 10.23/10.47      inference('cnf', [status(esa)], [d6_xboole_0])).
% 10.23/10.47  thf('36', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['34', '35'])).
% 10.23/10.47  thf('37', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X1 @ X0)
% 10.23/10.47           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('demod', [status(thm)], ['33', '36'])).
% 10.23/10.47  thf('38', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 10.23/10.47           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['21', '37'])).
% 10.23/10.47  thf('39', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X1 @ X0)
% 10.23/10.47           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('demod', [status(thm)], ['33', '36'])).
% 10.23/10.47  thf('40', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 10.23/10.47           = (k3_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['38', '39'])).
% 10.23/10.47  thf('41', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('demod', [status(thm)], ['16', '17', '20'])).
% 10.23/10.47  thf(t39_xboole_1, axiom,
% 10.23/10.47    (![A:$i,B:$i]:
% 10.23/10.47     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 10.23/10.47  thf('42', plain,
% 10.23/10.47      (![X8 : $i, X9 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 10.23/10.47           = (k2_xboole_0 @ X8 @ X9))),
% 10.23/10.47      inference('cnf', [status(esa)], [t39_xboole_1])).
% 10.23/10.47  thf('43', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1))),
% 10.23/10.47      inference('sup+', [status(thm)], ['41', '42'])).
% 10.23/10.47  thf('44', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['12', '13'])).
% 10.23/10.47  thf('46', plain,
% 10.23/10.47      (![X19 : $i, X20 : $i, X21 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 10.23/10.47           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 10.23/10.47      inference('cnf', [status(esa)], [t49_xboole_1])).
% 10.23/10.47  thf('47', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X1 @ k1_xboole_0)
% 10.23/10.47           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['45', '46'])).
% 10.23/10.47  thf(t2_boole, axiom,
% 10.23/10.47    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 10.23/10.47  thf('48', plain,
% 10.23/10.47      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 10.23/10.47      inference('cnf', [status(esa)], [t2_boole])).
% 10.23/10.47  thf('49', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['47', '48'])).
% 10.23/10.47  thf('50', plain,
% 10.23/10.47      (![X8 : $i, X9 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 10.23/10.47           = (k2_xboole_0 @ X8 @ X9))),
% 10.23/10.47      inference('cnf', [status(esa)], [t39_xboole_1])).
% 10.23/10.47  thf('51', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 10.23/10.47           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['49', '50'])).
% 10.23/10.47  thf('52', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 10.23/10.47      inference('cnf', [status(esa)], [t1_boole])).
% 10.23/10.47  thf('53', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('demod', [status(thm)], ['51', '52'])).
% 10.23/10.47  thf('54', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (X1))),
% 10.23/10.47      inference('demod', [status(thm)], ['43', '44', '53'])).
% 10.23/10.47  thf('55', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 10.23/10.47           (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1))
% 10.23/10.47           = (k3_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('sup+', [status(thm)], ['40', '54'])).
% 10.23/10.47  thf('56', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['47', '48'])).
% 10.23/10.47  thf('57', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['18', '19'])).
% 10.23/10.47  thf('59', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 10.23/10.47  thf('60', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['34', '35'])).
% 10.23/10.47  thf(t55_xboole_1, axiom,
% 10.23/10.47    (![A:$i,B:$i]:
% 10.23/10.47     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) =
% 10.23/10.47       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 10.23/10.47  thf('61', plain,
% 10.23/10.47      (![X25 : $i, X26 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k2_xboole_0 @ X25 @ X26) @ (k3_xboole_0 @ X25 @ X26))
% 10.23/10.47           = (k2_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ 
% 10.23/10.47              (k4_xboole_0 @ X26 @ X25)))),
% 10.23/10.47      inference('cnf', [status(esa)], [t55_xboole_1])).
% 10.23/10.47  thf(t6_xboole_1, axiom,
% 10.23/10.47    (![A:$i,B:$i]:
% 10.23/10.47     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 10.23/10.47  thf('62', plain,
% 10.23/10.47      (![X27 : $i, X28 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X27 @ (k2_xboole_0 @ X27 @ X28))
% 10.23/10.47           = (k2_xboole_0 @ X27 @ X28))),
% 10.23/10.47      inference('cnf', [status(esa)], [t6_xboole_1])).
% 10.23/10.47  thf('63', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 10.23/10.47           (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))
% 10.23/10.47           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['61', '62'])).
% 10.23/10.47  thf('64', plain,
% 10.23/10.47      (![X2 : $i, X3 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X2 @ X3)
% 10.23/10.47           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 10.23/10.47      inference('cnf', [status(esa)], [d6_xboole_0])).
% 10.23/10.47  thf('65', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 10.23/10.47           (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))
% 10.23/10.47           = (k5_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['63', '64'])).
% 10.23/10.47  thf('66', plain,
% 10.23/10.47      (![X29 : $i, X30 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X29 @ X30)
% 10.23/10.47           = (k2_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ 
% 10.23/10.47              (k3_xboole_0 @ X29 @ X30)))),
% 10.23/10.47      inference('cnf', [status(esa)], [t93_xboole_1])).
% 10.23/10.47  thf('67', plain,
% 10.23/10.47      (![X10 : $i, X11 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 10.23/10.47           = (k4_xboole_0 @ X10 @ X11))),
% 10.23/10.47      inference('cnf', [status(esa)], [t40_xboole_1])).
% 10.23/10.47  thf('68', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['66', '67'])).
% 10.23/10.47  thf('69', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 10.23/10.47           (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))
% 10.23/10.47           = (k5_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['65', '68'])).
% 10.23/10.47  thf('70', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf('71', plain,
% 10.23/10.47      (![X10 : $i, X11 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 10.23/10.47           = (k4_xboole_0 @ X10 @ X11))),
% 10.23/10.47      inference('cnf', [status(esa)], [t40_xboole_1])).
% 10.23/10.47  thf('72', plain,
% 10.23/10.47      (![X17 : $i, X18 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 10.23/10.47           = (k3_xboole_0 @ X17 @ X18))),
% 10.23/10.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 10.23/10.47  thf('73', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['71', '72'])).
% 10.23/10.47  thf('74', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 10.23/10.47  thf('75', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf('76', plain,
% 10.23/10.47      (![X5 : $i, X6 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (X5))),
% 10.23/10.47      inference('cnf', [status(esa)], [t21_xboole_1])).
% 10.23/10.47  thf('77', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['75', '76'])).
% 10.23/10.47  thf('78', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['73', '74', '77'])).
% 10.23/10.47  thf('79', plain,
% 10.23/10.47      (![X2 : $i, X3 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X2 @ X3)
% 10.23/10.47           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 10.23/10.47      inference('cnf', [status(esa)], [d6_xboole_0])).
% 10.23/10.47  thf('80', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k2_xboole_0 @ X0 @ 
% 10.23/10.47              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 10.23/10.47      inference('sup+', [status(thm)], ['78', '79'])).
% 10.23/10.47  thf('81', plain,
% 10.23/10.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 10.23/10.47           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 10.23/10.47      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.23/10.47  thf('82', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['28', '29'])).
% 10.23/10.47  thf('83', plain,
% 10.23/10.47      (![X8 : $i, X9 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 10.23/10.47           = (k2_xboole_0 @ X8 @ X9))),
% 10.23/10.47      inference('cnf', [status(esa)], [t39_xboole_1])).
% 10.23/10.47  thf('84', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 10.23/10.47           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['82', '83'])).
% 10.23/10.47  thf('85', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf('86', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['18', '19'])).
% 10.23/10.47  thf('87', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf('88', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X1 @ X0)
% 10.23/10.47           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 10.23/10.47  thf('89', plain,
% 10.23/10.47      (![X15 : $i, X16 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (k1_xboole_0))),
% 10.23/10.47      inference('cnf', [status(esa)], [t46_xboole_1])).
% 10.23/10.47  thf('90', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 10.23/10.47      inference('demod', [status(thm)], ['80', '81', '88', '89'])).
% 10.23/10.47  thf('91', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 10.23/10.47      inference('cnf', [status(esa)], [t1_boole])).
% 10.23/10.47  thf('92', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['90', '91'])).
% 10.23/10.47  thf('93', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 10.23/10.47           = (X1))),
% 10.23/10.47      inference('sup+', [status(thm)], ['70', '92'])).
% 10.23/10.47  thf('94', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 10.23/10.47           (k4_xboole_0 @ 
% 10.23/10.47            (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 10.23/10.47            (k4_xboole_0 @ X1 @ X0)))
% 10.23/10.47           = (k4_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['69', '93'])).
% 10.23/10.47  thf('95', plain,
% 10.23/10.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 10.23/10.47           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 10.23/10.47      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.23/10.47  thf('96', plain,
% 10.23/10.47      (![X17 : $i, X18 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 10.23/10.47           = (k3_xboole_0 @ X17 @ X18))),
% 10.23/10.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 10.23/10.47  thf('97', plain,
% 10.23/10.47      (![X8 : $i, X9 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 10.23/10.47           = (k2_xboole_0 @ X8 @ X9))),
% 10.23/10.47      inference('cnf', [status(esa)], [t39_xboole_1])).
% 10.23/10.47  thf('98', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 10.23/10.47      inference('sup+', [status(thm)], ['96', '97'])).
% 10.23/10.47  thf('99', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf('100', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf('101', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('demod', [status(thm)], ['98', '99', '100'])).
% 10.23/10.47  thf('102', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['18', '19'])).
% 10.23/10.47  thf('103', plain,
% 10.23/10.47      (![X8 : $i, X9 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 10.23/10.47           = (k2_xboole_0 @ X8 @ X9))),
% 10.23/10.47      inference('cnf', [status(esa)], [t39_xboole_1])).
% 10.23/10.47  thf('104', plain,
% 10.23/10.47      (![X0 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['102', '103'])).
% 10.23/10.47  thf('105', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['18', '19'])).
% 10.23/10.47  thf('106', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['104', '105'])).
% 10.23/10.47  thf('107', plain,
% 10.23/10.47      (![X22 : $i, X23 : $i, X24 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X23 @ X24))
% 10.23/10.47           = (k2_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ 
% 10.23/10.47              (k4_xboole_0 @ X22 @ X24)))),
% 10.23/10.47      inference('cnf', [status(esa)], [t54_xboole_1])).
% 10.23/10.47  thf('108', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X1))
% 10.23/10.47           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['106', '107'])).
% 10.23/10.47  thf('109', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['18', '19'])).
% 10.23/10.47  thf('110', plain,
% 10.23/10.47      (![X5 : $i, X6 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (X5))),
% 10.23/10.47      inference('cnf', [status(esa)], [t21_xboole_1])).
% 10.23/10.47  thf('111', plain,
% 10.23/10.47      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['109', '110'])).
% 10.23/10.47  thf('112', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['104', '105'])).
% 10.23/10.47  thf('113', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 10.23/10.47      inference('demod', [status(thm)], ['108', '111', '112'])).
% 10.23/10.47  thf('114', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (X1))),
% 10.23/10.47      inference('demod', [status(thm)], ['101', '113'])).
% 10.23/10.47  thf('115', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('demod', [status(thm)], ['51', '52'])).
% 10.23/10.47  thf('116', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['90', '91'])).
% 10.23/10.47  thf('117', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 10.23/10.47           = (k3_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['115', '116'])).
% 10.23/10.47  thf('118', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('demod', [status(thm)], ['16', '17', '20'])).
% 10.23/10.47  thf('119', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 10.23/10.47           = (k3_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['117', '118'])).
% 10.23/10.47  thf('120', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['94', '95', '114', '119'])).
% 10.23/10.47  thf('121', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('sup+', [status(thm)], ['60', '120'])).
% 10.23/10.47  thf('122', plain,
% 10.23/10.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 10.23/10.47           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 10.23/10.47      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.23/10.47  thf('123', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 10.23/10.47      inference('cnf', [status(esa)], [t1_boole])).
% 10.23/10.47  thf('124', plain,
% 10.23/10.47      (![X27 : $i, X28 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X27 @ (k2_xboole_0 @ X27 @ X28))
% 10.23/10.47           = (k2_xboole_0 @ X27 @ X28))),
% 10.23/10.47      inference('cnf', [status(esa)], [t6_xboole_1])).
% 10.23/10.47  thf('125', plain,
% 10.23/10.47      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['123', '124'])).
% 10.23/10.47  thf('126', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 10.23/10.47      inference('cnf', [status(esa)], [t1_boole])).
% 10.23/10.47  thf('127', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['125', '126'])).
% 10.23/10.47  thf('128', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X0 @ X1)
% 10.23/10.47           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1))),
% 10.23/10.47      inference('demod', [status(thm)], ['11', '59', '121', '122', '127'])).
% 10.23/10.47  thf('129', plain,
% 10.23/10.47      (![X8 : $i, X9 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 10.23/10.47           = (k2_xboole_0 @ X8 @ X9))),
% 10.23/10.47      inference('cnf', [status(esa)], [t39_xboole_1])).
% 10.23/10.47  thf('130', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['128', '129'])).
% 10.23/10.47  thf('131', plain,
% 10.23/10.47      (![X8 : $i, X9 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 10.23/10.47           = (k2_xboole_0 @ X8 @ X9))),
% 10.23/10.47      inference('cnf', [status(esa)], [t39_xboole_1])).
% 10.23/10.47  thf('132', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k2_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['130', '131'])).
% 10.23/10.47  thf('133', plain,
% 10.23/10.47      (![X25 : $i, X26 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k2_xboole_0 @ X25 @ X26) @ (k3_xboole_0 @ X25 @ X26))
% 10.23/10.47           = (k2_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ 
% 10.23/10.47              (k4_xboole_0 @ X26 @ X25)))),
% 10.23/10.47      inference('cnf', [status(esa)], [t55_xboole_1])).
% 10.23/10.47  thf('134', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf('135', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X1 @ X0)
% 10.23/10.47           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 10.23/10.47  thf('136', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X0 @ X1)
% 10.23/10.47           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['134', '135'])).
% 10.23/10.47  thf('137', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['28', '29'])).
% 10.23/10.47  thf('138', plain,
% 10.23/10.47      (![X2 : $i, X3 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X2 @ X3)
% 10.23/10.47           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 10.23/10.47      inference('cnf', [status(esa)], [d6_xboole_0])).
% 10.23/10.47  thf('139', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k2_xboole_0 @ k1_xboole_0 @ 
% 10.23/10.47              (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['137', '138'])).
% 10.23/10.47  thf('140', plain,
% 10.23/10.47      (![X10 : $i, X11 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 10.23/10.47           = (k4_xboole_0 @ X10 @ X11))),
% 10.23/10.47      inference('cnf', [status(esa)], [t40_xboole_1])).
% 10.23/10.47  thf('141', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['18', '19'])).
% 10.23/10.47  thf('142', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['139', '140', '141'])).
% 10.23/10.47  thf('143', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['136', '142'])).
% 10.23/10.47  thf('144', plain,
% 10.23/10.47      (![X15 : $i, X16 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (k1_xboole_0))),
% 10.23/10.47      inference('cnf', [status(esa)], [t46_xboole_1])).
% 10.23/10.47  thf('145', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k1_xboole_0))),
% 10.23/10.47      inference('demod', [status(thm)], ['143', '144'])).
% 10.23/10.47  thf('146', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ 
% 10.23/10.47           (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 10.23/10.47           (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))
% 10.23/10.47           = (k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['133', '145'])).
% 10.23/10.47  thf('147', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k5_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['23', '24'])).
% 10.23/10.47  thf('148', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['34', '35'])).
% 10.23/10.47  thf('149', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 10.23/10.47           (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))
% 10.23/10.47           = (k1_xboole_0))),
% 10.23/10.47      inference('demod', [status(thm)], ['146', '147', '148'])).
% 10.23/10.47  thf('150', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 10.23/10.47           (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 10.23/10.47            (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))))
% 10.23/10.47           = (k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['132', '149'])).
% 10.23/10.47  thf('151', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['94', '95', '114', '119'])).
% 10.23/10.47  thf('152', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['73', '74', '77'])).
% 10.23/10.47  thf('153', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['34', '35'])).
% 10.23/10.47  thf('154', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))
% 10.23/10.47           = (k1_xboole_0))),
% 10.23/10.47      inference('demod', [status(thm)], ['150', '151', '152', '153'])).
% 10.23/10.47  thf('155', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k5_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['23', '24'])).
% 10.23/10.47  thf('156', plain,
% 10.23/10.47      (![X10 : $i, X11 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 10.23/10.47           = (k4_xboole_0 @ X10 @ X11))),
% 10.23/10.47      inference('cnf', [status(esa)], [t40_xboole_1])).
% 10.23/10.47  thf('157', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['155', '156'])).
% 10.23/10.47  thf('158', plain,
% 10.23/10.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 10.23/10.47           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 10.23/10.47      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.23/10.47  thf('159', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 10.23/10.47      inference('demod', [status(thm)], ['108', '111', '112'])).
% 10.23/10.47  thf('160', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('demod', [status(thm)], ['157', '158', '159'])).
% 10.23/10.47  thf('161', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ k1_xboole_0 @ 
% 10.23/10.47           (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))))
% 10.23/10.47           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)) @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['154', '160'])).
% 10.23/10.47  thf('162', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['18', '19'])).
% 10.23/10.47  thf('163', plain,
% 10.23/10.47      (![X15 : $i, X16 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (k1_xboole_0))),
% 10.23/10.47      inference('cnf', [status(esa)], [t46_xboole_1])).
% 10.23/10.47  thf('164', plain,
% 10.23/10.47      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['162', '163'])).
% 10.23/10.47  thf('165', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k1_xboole_0)
% 10.23/10.47           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)) @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['161', '164'])).
% 10.23/10.47  thf('166', plain,
% 10.23/10.47      (![X17 : $i, X18 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 10.23/10.47           = (k3_xboole_0 @ X17 @ X18))),
% 10.23/10.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 10.23/10.47  thf('167', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 10.23/10.47           k1_xboole_0)
% 10.23/10.47           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)) @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['165', '166'])).
% 10.23/10.47  thf('168', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['104', '105'])).
% 10.23/10.47  thf('169', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 10.23/10.47  thf('170', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))
% 10.23/10.47           = (k1_xboole_0))),
% 10.23/10.47      inference('demod', [status(thm)], ['150', '151', '152', '153'])).
% 10.23/10.47  thf('171', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['94', '95', '114', '119'])).
% 10.23/10.47  thf('172', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['12', '13'])).
% 10.23/10.47  thf('173', plain,
% 10.23/10.47      (![X22 : $i, X23 : $i, X24 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X23 @ X24))
% 10.23/10.47           = (k2_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ 
% 10.23/10.47              (k4_xboole_0 @ X22 @ X24)))),
% 10.23/10.47      inference('cnf', [status(esa)], [t54_xboole_1])).
% 10.23/10.47  thf('174', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['172', '173'])).
% 10.23/10.47  thf('175', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['18', '19'])).
% 10.23/10.47  thf('176', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['174', '175'])).
% 10.23/10.47  thf('177', plain,
% 10.23/10.47      (![X2 : $i, X3 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X2 @ X3)
% 10.23/10.47           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 10.23/10.47      inference('cnf', [status(esa)], [d6_xboole_0])).
% 10.23/10.47  thf('178', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 10.23/10.47              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['176', '177'])).
% 10.23/10.47  thf('179', plain,
% 10.23/10.47      (![X17 : $i, X18 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 10.23/10.47           = (k3_xboole_0 @ X17 @ X18))),
% 10.23/10.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 10.23/10.47  thf('180', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 10.23/10.47      inference('demod', [status(thm)], ['108', '111', '112'])).
% 10.23/10.47  thf('181', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((X1) = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['179', '180'])).
% 10.23/10.47  thf('182', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['28', '29'])).
% 10.23/10.47  thf('183', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['181', '182'])).
% 10.23/10.47  thf('184', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.23/10.47  thf('185', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['18', '19'])).
% 10.23/10.47  thf('186', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['178', '183', '184', '185'])).
% 10.23/10.47  thf('187', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['171', '186'])).
% 10.23/10.47  thf('188', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 10.23/10.47           = (k3_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['117', '118'])).
% 10.23/10.47  thf('189', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X0 @ X1)
% 10.23/10.47           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('demod', [status(thm)], ['187', '188'])).
% 10.23/10.47  thf('190', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)) @ X0)
% 10.23/10.47           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['170', '189'])).
% 10.23/10.47  thf('191', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 10.23/10.47      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 10.23/10.47  thf('192', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['104', '105'])).
% 10.23/10.47  thf('193', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))
% 10.23/10.47           = (X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['190', '191', '192'])).
% 10.23/10.47  thf('194', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)) = (X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['167', '168', '169', '193'])).
% 10.23/10.47  thf('195', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['94', '95', '114', '119'])).
% 10.23/10.47  thf('196', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X1 @ X0)
% 10.23/10.47           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['194', '195'])).
% 10.23/10.47  thf('197', plain,
% 10.23/10.47      (![X10 : $i, X11 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 10.23/10.47           = (k4_xboole_0 @ X10 @ X11))),
% 10.23/10.47      inference('cnf', [status(esa)], [t40_xboole_1])).
% 10.23/10.47  thf('198', plain,
% 10.23/10.47      (![X8 : $i, X9 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 10.23/10.47           = (k2_xboole_0 @ X8 @ X9))),
% 10.23/10.47      inference('cnf', [status(esa)], [t39_xboole_1])).
% 10.23/10.47  thf('199', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['197', '198'])).
% 10.23/10.47  thf('200', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X1 @ X0)
% 10.23/10.47           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 10.23/10.47  thf('201', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k2_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['199', '200'])).
% 10.23/10.47  thf('202', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['66', '67'])).
% 10.23/10.47  thf('203', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 10.23/10.47           (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 10.23/10.47           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 10.23/10.47              (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 10.23/10.47      inference('sup+', [status(thm)], ['201', '202'])).
% 10.23/10.47  thf('204', plain,
% 10.23/10.47      (![X19 : $i, X20 : $i, X21 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 10.23/10.47           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 10.23/10.47      inference('cnf', [status(esa)], [t49_xboole_1])).
% 10.23/10.47  thf('205', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['181', '182'])).
% 10.23/10.47  thf('206', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['104', '105'])).
% 10.23/10.47  thf('207', plain,
% 10.23/10.47      (![X19 : $i, X20 : $i, X21 : $i]:
% 10.23/10.47         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 10.23/10.47           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 10.23/10.47      inference('cnf', [status(esa)], [t49_xboole_1])).
% 10.23/10.47  thf('208', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['181', '182'])).
% 10.23/10.47  thf('209', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 10.23/10.47      inference('demod', [status(thm)], ['104', '105'])).
% 10.23/10.47  thf('210', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X1 @ X0)
% 10.23/10.47           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('demod', [status(thm)],
% 10.23/10.47                ['203', '204', '205', '206', '207', '208', '209'])).
% 10.23/10.47  thf('211', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('sup+', [status(thm)], ['196', '210'])).
% 10.23/10.47  thf('212', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 10.23/10.47           = (k2_xboole_0 @ X1 @ X0))),
% 10.23/10.47      inference('sup+', [status(thm)], ['130', '131'])).
% 10.23/10.47  thf('213', plain,
% 10.23/10.47      (![X0 : $i, X1 : $i]:
% 10.23/10.47         ((k2_xboole_0 @ X1 @ X0)
% 10.23/10.47           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 10.23/10.47      inference('demod', [status(thm)], ['211', '212'])).
% 10.23/10.47  thf('214', plain,
% 10.23/10.47      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 10.23/10.47      inference('demod', [status(thm)], ['0', '213'])).
% 10.23/10.47  thf('215', plain, ($false), inference('simplify', [status(thm)], ['214'])).
% 10.23/10.47  
% 10.23/10.47  % SZS output end Refutation
% 10.23/10.47  
% 10.23/10.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
