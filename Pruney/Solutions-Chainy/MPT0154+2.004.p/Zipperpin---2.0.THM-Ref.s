%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pLDe3C04GB

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:22 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 820 expanded)
%              Number of leaves         :   21 ( 281 expanded)
%              Depth                    :   26
%              Number of atoms          :  695 (5509 expanded)
%              Number of equality atoms :   91 ( 809 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t70_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_enumset1 @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t70_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('32',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','33'])).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','33'])).

thf('51',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','53','56','57'])).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','63'])).

thf('65',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','68'])).

thf('70',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('72',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('78',plain,(
    ( k2_tarski @ sk_B @ sk_A )
 != ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','76','77'])).

thf('79',plain,(
    $false ),
    inference(simplify,[status(thm)],['78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pLDe3C04GB
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:35:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.36/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.59  % Solved by: fo/fo7.sh
% 0.36/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.59  % done 423 iterations in 0.148s
% 0.36/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.59  % SZS output start Refutation
% 0.36/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(t70_enumset1, conjecture,
% 0.36/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.36/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.59    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.36/0.59    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.36/0.59  thf('0', plain,
% 0.36/0.59      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(t41_enumset1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( k2_tarski @ A @ B ) =
% 0.36/0.59       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.36/0.59  thf('1', plain,
% 0.36/0.59      (![X19 : $i, X20 : $i]:
% 0.36/0.59         ((k2_tarski @ X19 @ X20)
% 0.36/0.59           = (k2_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X20)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.36/0.59  thf(commutativity_k2_xboole_0, axiom,
% 0.36/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.36/0.59  thf('2', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.59  thf('3', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.36/0.59           = (k2_tarski @ X1 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['1', '2'])).
% 0.36/0.59  thf('4', plain,
% 0.36/0.59      (![X19 : $i, X20 : $i]:
% 0.36/0.59         ((k2_tarski @ X19 @ X20)
% 0.36/0.59           = (k2_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X20)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.36/0.59  thf('5', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['3', '4'])).
% 0.36/0.59  thf('6', plain,
% 0.36/0.59      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_B @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['0', '5'])).
% 0.36/0.59  thf('7', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['3', '4'])).
% 0.36/0.59  thf('8', plain,
% 0.36/0.59      (![X19 : $i, X20 : $i]:
% 0.36/0.59         ((k2_tarski @ X19 @ X20)
% 0.36/0.59           = (k2_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X20)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.36/0.59  thf(t41_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.59       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.59  thf('9', plain,
% 0.36/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.36/0.59           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.59  thf(t48_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.59  thf('10', plain,
% 0.36/0.59      (![X12 : $i, X13 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.36/0.59           = (k3_xboole_0 @ X12 @ X13))),
% 0.36/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.59  thf('11', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.36/0.59           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.36/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.36/0.59  thf('12', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.59  thf(t1_boole, axiom,
% 0.36/0.59    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.59  thf('13', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.36/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.36/0.59  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.36/0.59  thf(t22_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.36/0.59  thf('15', plain,
% 0.36/0.59      (![X7 : $i, X8 : $i]:
% 0.36/0.59         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 0.36/0.59      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.36/0.59  thf('16', plain,
% 0.36/0.59      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.59  thf('17', plain,
% 0.36/0.59      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.36/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.59  thf('18', plain,
% 0.36/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.36/0.59  thf(t100_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.59  thf('19', plain,
% 0.36/0.59      (![X4 : $i, X5 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X4 @ X5)
% 0.36/0.59           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.59  thf('20', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.36/0.59  thf('21', plain,
% 0.36/0.59      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.59  thf('22', plain,
% 0.36/0.59      (![X4 : $i, X5 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X4 @ X5)
% 0.36/0.59           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.59  thf('23', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.59           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['21', '22'])).
% 0.36/0.59  thf(t98_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.36/0.59  thf('24', plain,
% 0.36/0.59      (![X17 : $i, X18 : $i]:
% 0.36/0.59         ((k2_xboole_0 @ X17 @ X18)
% 0.36/0.59           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.59  thf('25', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.36/0.59           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.36/0.59      inference('sup+', [status(thm)], ['23', '24'])).
% 0.36/0.59  thf('26', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.36/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.36/0.59  thf('27', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((X0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.36/0.59      inference('demod', [status(thm)], ['25', '26'])).
% 0.36/0.59  thf('28', plain,
% 0.36/0.59      (![X12 : $i, X13 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.36/0.59           = (k3_xboole_0 @ X12 @ X13))),
% 0.36/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.59  thf('29', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.59           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['21', '22'])).
% 0.36/0.59  thf('30', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.59           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['28', '29'])).
% 0.36/0.59  thf('31', plain,
% 0.36/0.59      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.59  thf('32', plain,
% 0.36/0.59      (((k1_xboole_0) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.36/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.36/0.59  thf('33', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.59      inference('demod', [status(thm)], ['27', '32'])).
% 0.36/0.59  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['20', '33'])).
% 0.36/0.59  thf('35', plain,
% 0.36/0.59      (![X12 : $i, X13 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.36/0.59           = (k3_xboole_0 @ X12 @ X13))),
% 0.36/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.59  thf('36', plain,
% 0.36/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['34', '35'])).
% 0.36/0.59  thf('37', plain,
% 0.36/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.36/0.59  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.59      inference('demod', [status(thm)], ['36', '37'])).
% 0.36/0.59  thf('39', plain,
% 0.36/0.59      (![X17 : $i, X18 : $i]:
% 0.36/0.59         ((k2_xboole_0 @ X17 @ X18)
% 0.36/0.59           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.59  thf('40', plain,
% 0.36/0.59      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['38', '39'])).
% 0.36/0.59  thf('41', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.59      inference('demod', [status(thm)], ['27', '32'])).
% 0.36/0.59  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.59  thf('43', plain,
% 0.36/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.36/0.59           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.59  thf('44', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.36/0.59           = (k4_xboole_0 @ X1 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['42', '43'])).
% 0.36/0.59  thf('45', plain,
% 0.36/0.59      (![X12 : $i, X13 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.36/0.59           = (k3_xboole_0 @ X12 @ X13))),
% 0.36/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.59  thf('46', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.59           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['44', '45'])).
% 0.36/0.59  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.59      inference('demod', [status(thm)], ['36', '37'])).
% 0.36/0.59  thf('48', plain,
% 0.36/0.59      (![X12 : $i, X13 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.36/0.59           = (k3_xboole_0 @ X12 @ X13))),
% 0.36/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.59  thf('49', plain,
% 0.36/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['47', '48'])).
% 0.36/0.59  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['20', '33'])).
% 0.36/0.59  thf('51', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['49', '50'])).
% 0.36/0.59  thf('52', plain,
% 0.36/0.59      (![X4 : $i, X5 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X4 @ X5)
% 0.36/0.59           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.59  thf('53', plain,
% 0.36/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['51', '52'])).
% 0.36/0.59  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.59      inference('demod', [status(thm)], ['36', '37'])).
% 0.36/0.59  thf('55', plain,
% 0.36/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['51', '52'])).
% 0.36/0.59  thf('56', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.59      inference('demod', [status(thm)], ['54', '55'])).
% 0.36/0.59  thf('57', plain,
% 0.36/0.59      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.36/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.59  thf('58', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.36/0.59      inference('demod', [status(thm)], ['46', '53', '56', '57'])).
% 0.36/0.59  thf('59', plain,
% 0.36/0.59      (![X4 : $i, X5 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X4 @ X5)
% 0.36/0.59           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.59  thf('60', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.59           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['58', '59'])).
% 0.36/0.59  thf('61', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.59      inference('demod', [status(thm)], ['27', '32'])).
% 0.36/0.59  thf('62', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['60', '61'])).
% 0.36/0.59  thf('63', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['11', '62'])).
% 0.36/0.59  thf('64', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.36/0.59           = (k1_tarski @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['8', '63'])).
% 0.36/0.59  thf('65', plain,
% 0.36/0.59      (![X4 : $i, X5 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X4 @ X5)
% 0.36/0.59           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.59  thf('66', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.36/0.59           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.36/0.59      inference('sup+', [status(thm)], ['64', '65'])).
% 0.36/0.59  thf('67', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.59      inference('demod', [status(thm)], ['54', '55'])).
% 0.36/0.59  thf('68', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.36/0.59           = (k1_xboole_0))),
% 0.36/0.59      inference('demod', [status(thm)], ['66', '67'])).
% 0.36/0.59  thf('69', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.36/0.59           = (k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['7', '68'])).
% 0.36/0.59  thf('70', plain,
% 0.36/0.59      (![X17 : $i, X18 : $i]:
% 0.36/0.59         ((k2_xboole_0 @ X17 @ X18)
% 0.36/0.59           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.59  thf('71', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.36/0.59           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['69', '70'])).
% 0.36/0.59  thf(t42_enumset1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.36/0.59       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.36/0.59  thf('72', plain,
% 0.36/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.59         ((k1_enumset1 @ X21 @ X22 @ X23)
% 0.36/0.59           = (k2_xboole_0 @ (k1_tarski @ X21) @ (k2_tarski @ X22 @ X23)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.36/0.59  thf('73', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.59  thf('74', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 0.36/0.59           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['72', '73'])).
% 0.36/0.59  thf('75', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.59      inference('demod', [status(thm)], ['27', '32'])).
% 0.36/0.59  thf('76', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k1_enumset1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['71', '74', '75'])).
% 0.36/0.59  thf('77', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['3', '4'])).
% 0.36/0.59  thf('78', plain, (((k2_tarski @ sk_B @ sk_A) != (k2_tarski @ sk_B @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['6', '76', '77'])).
% 0.36/0.59  thf('79', plain, ($false), inference('simplify', [status(thm)], ['78'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
