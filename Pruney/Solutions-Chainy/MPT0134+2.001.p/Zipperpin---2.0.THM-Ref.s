%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kt6lgGFLQD

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:59 EST 2020

% Result     : Theorem 39.88s
% Output     : Refutation 39.88s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 154 expanded)
%              Number of leaves         :   18 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  845 (1751 expanded)
%              Number of equality atoms :   66 ( 142 expanded)
%              Maximal formula depth    :   14 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t50_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_enumset1 @ A @ B @ C @ D @ E )
        = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_enumset1])).

thf('0',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k2_xboole_0 @ ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_tarski @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_E ) @ ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('4',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_E @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X4 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X4 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_E @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['4','16'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('22',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X4 @ X3 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X4 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X2 @ X3 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_E @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','37'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('41',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X4 @ X3 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33','34'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['38','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kt6lgGFLQD
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 39.88/40.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 39.88/40.08  % Solved by: fo/fo7.sh
% 39.88/40.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 39.88/40.08  % done 6819 iterations in 39.629s
% 39.88/40.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 39.88/40.08  % SZS output start Refutation
% 39.88/40.08  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 39.88/40.08  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 39.88/40.08  thf(sk_E_type, type, sk_E: $i).
% 39.88/40.08  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 39.88/40.08  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 39.88/40.08  thf(sk_A_type, type, sk_A: $i).
% 39.88/40.08  thf(sk_C_type, type, sk_C: $i).
% 39.88/40.08  thf(sk_D_type, type, sk_D: $i).
% 39.88/40.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 39.88/40.08  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 39.88/40.08  thf(sk_B_type, type, sk_B: $i).
% 39.88/40.08  thf(t50_enumset1, conjecture,
% 39.88/40.08    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 39.88/40.08     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 39.88/40.08       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 39.88/40.08  thf(zf_stmt_0, negated_conjecture,
% 39.88/40.08    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 39.88/40.08        ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 39.88/40.08          ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )),
% 39.88/40.08    inference('cnf.neg', [status(esa)], [t50_enumset1])).
% 39.88/40.08  thf('0', plain,
% 39.88/40.08      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 39.88/40.08         != (k2_xboole_0 @ (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 39.88/40.08             (k1_tarski @ sk_E)))),
% 39.88/40.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.88/40.08  thf(commutativity_k2_xboole_0, axiom,
% 39.88/40.08    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 39.88/40.08  thf('1', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 39.88/40.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 39.88/40.08  thf('2', plain,
% 39.88/40.08      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 39.88/40.08         != (k2_xboole_0 @ (k1_tarski @ sk_E) @ 
% 39.88/40.08             (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 39.88/40.08      inference('demod', [status(thm)], ['0', '1'])).
% 39.88/40.08  thf(t47_enumset1, axiom,
% 39.88/40.08    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 39.88/40.08     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 39.88/40.08       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 39.88/40.08  thf('3', plain,
% 39.88/40.08      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 39.88/40.08         ((k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X14) @ 
% 39.88/40.08              (k2_enumset1 @ X15 @ X16 @ X17 @ X18)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t47_enumset1])).
% 39.88/40.08  thf('4', plain,
% 39.88/40.08      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 39.88/40.08         != (k3_enumset1 @ sk_E @ sk_A @ sk_B @ sk_C @ sk_D))),
% 39.88/40.08      inference('demod', [status(thm)], ['2', '3'])).
% 39.88/40.08  thf(t44_enumset1, axiom,
% 39.88/40.08    (![A:$i,B:$i,C:$i,D:$i]:
% 39.88/40.08     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 39.88/40.08       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 39.88/40.08  thf('5', plain,
% 39.88/40.08      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 39.88/40.08         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t44_enumset1])).
% 39.88/40.08  thf('6', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 39.88/40.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 39.88/40.08  thf('7', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 39.88/40.08           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 39.88/40.08      inference('sup+', [status(thm)], ['5', '6'])).
% 39.88/40.08  thf('8', plain,
% 39.88/40.08      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 39.88/40.08         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t44_enumset1])).
% 39.88/40.08  thf(t4_xboole_1, axiom,
% 39.88/40.08    (![A:$i,B:$i,C:$i]:
% 39.88/40.08     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 39.88/40.08       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 39.88/40.08  thf('9', plain,
% 39.88/40.08      (![X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 39.88/40.08           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t4_xboole_1])).
% 39.88/40.08  thf('10', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 39.88/40.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 39.88/40.08  thf('11', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 39.88/40.08           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 39.88/40.08      inference('sup+', [status(thm)], ['9', '10'])).
% 39.88/40.08  thf('12', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 39.88/40.08              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 39.88/40.08      inference('sup+', [status(thm)], ['8', '11'])).
% 39.88/40.08  thf('13', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k2_enumset1 @ X4 @ X2 @ X1 @ X0))
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 39.88/40.08              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 39.88/40.08      inference('sup+', [status(thm)], ['7', '12'])).
% 39.88/40.08  thf('14', plain,
% 39.88/40.08      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 39.88/40.08         ((k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X14) @ 
% 39.88/40.08              (k2_enumset1 @ X15 @ X16 @ X17 @ X18)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t47_enumset1])).
% 39.88/40.08  thf('15', plain,
% 39.88/40.08      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 39.88/40.08         ((k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X14) @ 
% 39.88/40.08              (k2_enumset1 @ X15 @ X16 @ X17 @ X18)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t47_enumset1])).
% 39.88/40.08  thf('16', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k3_enumset1 @ X3 @ X4 @ X2 @ X1 @ X0)
% 39.88/40.08           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 39.88/40.08      inference('demod', [status(thm)], ['13', '14', '15'])).
% 39.88/40.08  thf('17', plain,
% 39.88/40.08      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 39.88/40.08         != (k3_enumset1 @ sk_A @ sk_E @ sk_B @ sk_C @ sk_D))),
% 39.88/40.08      inference('demod', [status(thm)], ['4', '16'])).
% 39.88/40.08  thf(t42_enumset1, axiom,
% 39.88/40.08    (![A:$i,B:$i,C:$i]:
% 39.88/40.08     ( ( k1_enumset1 @ A @ B @ C ) =
% 39.88/40.08       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 39.88/40.08  thf('18', plain,
% 39.88/40.08      (![X7 : $i, X8 : $i, X9 : $i]:
% 39.88/40.08         ((k1_enumset1 @ X7 @ X8 @ X9)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t42_enumset1])).
% 39.88/40.08  thf('19', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 39.88/40.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 39.88/40.08  thf('20', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 39.88/40.08           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 39.88/40.08      inference('sup+', [status(thm)], ['18', '19'])).
% 39.88/40.08  thf('21', plain,
% 39.88/40.08      (![X7 : $i, X8 : $i, X9 : $i]:
% 39.88/40.08         ((k1_enumset1 @ X7 @ X8 @ X9)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t42_enumset1])).
% 39.88/40.08  thf('22', plain,
% 39.88/40.08      (![X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 39.88/40.08           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t4_xboole_1])).
% 39.88/40.08  thf('23', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 39.88/40.08              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 39.88/40.08      inference('sup+', [status(thm)], ['21', '22'])).
% 39.88/40.08  thf('24', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X1 @ X0) @ (k1_tarski @ X2))
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 39.88/40.08      inference('sup+', [status(thm)], ['20', '23'])).
% 39.88/40.08  thf('25', plain,
% 39.88/40.08      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 39.88/40.08         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t44_enumset1])).
% 39.88/40.08  thf('26', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X1 @ X0) @ (k1_tarski @ X2))
% 39.88/40.08           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 39.88/40.08      inference('demod', [status(thm)], ['24', '25'])).
% 39.88/40.08  thf('27', plain,
% 39.88/40.08      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 39.88/40.08         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t44_enumset1])).
% 39.88/40.08  thf('28', plain,
% 39.88/40.08      (![X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 39.88/40.08           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t4_xboole_1])).
% 39.88/40.08  thf('29', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 39.88/40.08              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 39.88/40.08      inference('sup+', [status(thm)], ['27', '28'])).
% 39.88/40.08  thf('30', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X1 @ X0) @ (k1_tarski @ X2))
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 39.88/40.08              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 39.88/40.08      inference('sup+', [status(thm)], ['26', '29'])).
% 39.88/40.08  thf('31', plain,
% 39.88/40.08      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 39.88/40.08         ((k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X14) @ 
% 39.88/40.08              (k2_enumset1 @ X15 @ X16 @ X17 @ X18)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t47_enumset1])).
% 39.88/40.08  thf('32', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 39.88/40.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 39.88/40.08  thf('33', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ (k1_tarski @ X4))
% 39.88/40.08           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 39.88/40.08      inference('sup+', [status(thm)], ['31', '32'])).
% 39.88/40.08  thf('34', plain,
% 39.88/40.08      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 39.88/40.08         ((k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X14) @ 
% 39.88/40.08              (k2_enumset1 @ X15 @ X16 @ X17 @ X18)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t47_enumset1])).
% 39.88/40.08  thf('35', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k3_enumset1 @ X2 @ X4 @ X3 @ X1 @ X0)
% 39.88/40.08           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 39.88/40.08      inference('demod', [status(thm)], ['30', '33', '34'])).
% 39.88/40.08  thf('36', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k3_enumset1 @ X3 @ X4 @ X2 @ X1 @ X0)
% 39.88/40.08           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 39.88/40.08      inference('demod', [status(thm)], ['13', '14', '15'])).
% 39.88/40.08  thf('37', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k3_enumset1 @ X4 @ X2 @ X3 @ X1 @ X0)
% 39.88/40.08           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 39.88/40.08      inference('sup+', [status(thm)], ['35', '36'])).
% 39.88/40.08  thf('38', plain,
% 39.88/40.08      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 39.88/40.08         != (k3_enumset1 @ sk_A @ sk_B @ sk_E @ sk_C @ sk_D))),
% 39.88/40.08      inference('demod', [status(thm)], ['17', '37'])).
% 39.88/40.08  thf(t41_enumset1, axiom,
% 39.88/40.08    (![A:$i,B:$i]:
% 39.88/40.08     ( ( k2_tarski @ A @ B ) =
% 39.88/40.08       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 39.88/40.08  thf('39', plain,
% 39.88/40.08      (![X5 : $i, X6 : $i]:
% 39.88/40.08         ((k2_tarski @ X5 @ X6)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t41_enumset1])).
% 39.88/40.08  thf('40', plain,
% 39.88/40.08      (![X5 : $i, X6 : $i]:
% 39.88/40.08         ((k2_tarski @ X5 @ X6)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t41_enumset1])).
% 39.88/40.08  thf('41', plain,
% 39.88/40.08      (![X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 39.88/40.08           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t4_xboole_1])).
% 39.88/40.08  thf('42', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 39.88/40.08              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 39.88/40.08      inference('sup+', [status(thm)], ['40', '41'])).
% 39.88/40.08  thf('43', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 39.88/40.08      inference('sup+', [status(thm)], ['39', '42'])).
% 39.88/40.08  thf('44', plain,
% 39.88/40.08      (![X7 : $i, X8 : $i, X9 : $i]:
% 39.88/40.08         ((k1_enumset1 @ X7 @ X8 @ X9)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t42_enumset1])).
% 39.88/40.08  thf('45', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 39.88/40.08           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 39.88/40.08      inference('demod', [status(thm)], ['43', '44'])).
% 39.88/40.08  thf('46', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 39.88/40.08              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 39.88/40.08      inference('sup+', [status(thm)], ['21', '22'])).
% 39.88/40.08  thf('47', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 39.88/40.08      inference('sup+', [status(thm)], ['45', '46'])).
% 39.88/40.08  thf('48', plain,
% 39.88/40.08      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 39.88/40.08         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t44_enumset1])).
% 39.88/40.08  thf('49', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 39.88/40.08           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 39.88/40.08      inference('demod', [status(thm)], ['47', '48'])).
% 39.88/40.08  thf('50', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 39.88/40.08              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 39.88/40.08      inference('sup+', [status(thm)], ['27', '28'])).
% 39.88/40.08  thf('51', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 39.88/40.08              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 39.88/40.08      inference('sup+', [status(thm)], ['49', '50'])).
% 39.88/40.08  thf('52', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ (k1_tarski @ X4))
% 39.88/40.08           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 39.88/40.08      inference('sup+', [status(thm)], ['31', '32'])).
% 39.88/40.08  thf('53', plain,
% 39.88/40.08      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 39.88/40.08         ((k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)
% 39.88/40.08           = (k2_xboole_0 @ (k1_tarski @ X14) @ 
% 39.88/40.08              (k2_enumset1 @ X15 @ X16 @ X17 @ X18)))),
% 39.88/40.08      inference('cnf', [status(esa)], [t47_enumset1])).
% 39.88/40.08  thf('54', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1)
% 39.88/40.08           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 39.88/40.08      inference('demod', [status(thm)], ['51', '52', '53'])).
% 39.88/40.08  thf('55', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k3_enumset1 @ X2 @ X4 @ X3 @ X1 @ X0)
% 39.88/40.08           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 39.88/40.08      inference('demod', [status(thm)], ['30', '33', '34'])).
% 39.88/40.08  thf('56', plain,
% 39.88/40.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 39.88/40.08         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 39.88/40.08           = (k3_enumset1 @ X4 @ X3 @ X0 @ X2 @ X1))),
% 39.88/40.08      inference('sup+', [status(thm)], ['54', '55'])).
% 39.88/40.08  thf('57', plain,
% 39.88/40.08      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 39.88/40.08         != (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 39.88/40.08      inference('demod', [status(thm)], ['38', '56'])).
% 39.88/40.08  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 39.88/40.08  
% 39.88/40.08  % SZS output end Refutation
% 39.88/40.08  
% 39.88/40.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
