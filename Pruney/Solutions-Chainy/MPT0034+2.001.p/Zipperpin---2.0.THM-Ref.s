%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6CzEm84KRN

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:54 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 507 expanded)
%              Number of leaves         :   16 ( 179 expanded)
%              Depth                    :   15
%              Number of atoms          :  660 (3575 expanded)
%              Number of equality atoms :   70 ( 401 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t27_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t24_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ X0 )
      = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_D @ X0 ) @ sk_C )
      = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','46'])).

thf('48',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('49',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('51',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_D @ ( k3_xboole_0 @ X0 @ sk_C ) )
      = ( k3_xboole_0 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('56',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('58',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('64',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('68',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ X1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['54','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('74',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['0','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6CzEm84KRN
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:35:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.07/1.27  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.07/1.27  % Solved by: fo/fo7.sh
% 1.07/1.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.27  % done 1659 iterations in 0.824s
% 1.07/1.27  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.07/1.27  % SZS output start Refutation
% 1.07/1.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.27  thf(sk_D_type, type, sk_D: $i).
% 1.07/1.27  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.07/1.27  thf(sk_C_type, type, sk_C: $i).
% 1.07/1.27  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.07/1.27  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.27  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.27  thf(t27_xboole_1, conjecture,
% 1.07/1.27    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.27     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 1.07/1.27       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ))).
% 1.07/1.27  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.27    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.27        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 1.07/1.27          ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )),
% 1.07/1.27    inference('cnf.neg', [status(esa)], [t27_xboole_1])).
% 1.07/1.27  thf('0', plain,
% 1.07/1.27      (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ (k3_xboole_0 @ sk_B @ sk_D))),
% 1.07/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.27  thf('1', plain, ((r1_tarski @ sk_C @ sk_D)),
% 1.07/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.27  thf(t12_xboole_1, axiom,
% 1.07/1.27    (![A:$i,B:$i]:
% 1.07/1.27     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.07/1.27  thf('2', plain,
% 1.07/1.27      (![X3 : $i, X4 : $i]:
% 1.07/1.27         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 1.07/1.27      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.07/1.27  thf('3', plain, (((k2_xboole_0 @ sk_C @ sk_D) = (sk_D))),
% 1.07/1.27      inference('sup-', [status(thm)], ['1', '2'])).
% 1.07/1.27  thf(t17_xboole_1, axiom,
% 1.07/1.27    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.07/1.27  thf('4', plain,
% 1.07/1.27      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 1.07/1.27      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.07/1.27  thf('5', plain,
% 1.07/1.27      (![X3 : $i, X4 : $i]:
% 1.07/1.27         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 1.07/1.27      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.07/1.27  thf('6', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.07/1.27      inference('sup-', [status(thm)], ['4', '5'])).
% 1.07/1.27  thf(commutativity_k2_xboole_0, axiom,
% 1.07/1.27    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.07/1.27  thf('7', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.07/1.27      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.07/1.27  thf('8', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 1.07/1.27      inference('demod', [status(thm)], ['6', '7'])).
% 1.07/1.27  thf(t24_xboole_1, axiom,
% 1.07/1.27    (![A:$i,B:$i,C:$i]:
% 1.07/1.27     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 1.07/1.27       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 1.07/1.27  thf('9', plain,
% 1.07/1.27      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.07/1.27         ((k2_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15))
% 1.07/1.27           = (k3_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ 
% 1.07/1.27              (k2_xboole_0 @ X13 @ X15)))),
% 1.07/1.27      inference('cnf', [status(esa)], [t24_xboole_1])).
% 1.07/1.27  thf('10', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.27         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1))
% 1.07/1.27           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.07/1.27      inference('sup+', [status(thm)], ['8', '9'])).
% 1.07/1.27  thf(t16_xboole_1, axiom,
% 1.07/1.27    (![A:$i,B:$i,C:$i]:
% 1.07/1.27     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.07/1.27       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.07/1.27  thf('11', plain,
% 1.07/1.27      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 1.07/1.27           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.07/1.27      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.07/1.27  thf('12', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 1.07/1.27      inference('demod', [status(thm)], ['6', '7'])).
% 1.07/1.27  thf('13', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.07/1.27      inference('demod', [status(thm)], ['10', '11', '12'])).
% 1.07/1.27  thf('14', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ sk_D))),
% 1.07/1.27      inference('sup+', [status(thm)], ['3', '13'])).
% 1.07/1.27  thf('15', plain,
% 1.07/1.27      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 1.07/1.27           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.07/1.27      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.07/1.27  thf('16', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ sk_C @ X0)
% 1.07/1.27           = (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_D @ X0)))),
% 1.07/1.27      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.27  thf(idempotence_k2_xboole_0, axiom,
% 1.07/1.27    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.07/1.27  thf('17', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 1.07/1.27      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.07/1.27  thf('18', plain,
% 1.07/1.27      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.07/1.27         ((k2_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15))
% 1.07/1.27           = (k3_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ 
% 1.07/1.27              (k2_xboole_0 @ X13 @ X15)))),
% 1.07/1.27      inference('cnf', [status(esa)], [t24_xboole_1])).
% 1.07/1.27  thf('19', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.07/1.27           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 1.07/1.27      inference('sup+', [status(thm)], ['17', '18'])).
% 1.07/1.27  thf('20', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.07/1.27      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.07/1.27  thf(t2_boole, axiom,
% 1.07/1.27    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.07/1.27  thf('21', plain,
% 1.07/1.27      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 1.07/1.27      inference('cnf', [status(esa)], [t2_boole])).
% 1.07/1.27  thf('22', plain,
% 1.07/1.27      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 1.07/1.27      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.07/1.27  thf('23', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.07/1.27      inference('sup+', [status(thm)], ['21', '22'])).
% 1.07/1.27  thf('24', plain,
% 1.07/1.27      (![X3 : $i, X4 : $i]:
% 1.07/1.27         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 1.07/1.27      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.07/1.27  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.07/1.27      inference('sup-', [status(thm)], ['23', '24'])).
% 1.07/1.27  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.07/1.27      inference('sup+', [status(thm)], ['20', '25'])).
% 1.07/1.27  thf('27', plain,
% 1.07/1.27      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.07/1.27         ((k2_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15))
% 1.07/1.27           = (k3_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ 
% 1.07/1.27              (k2_xboole_0 @ X13 @ X15)))),
% 1.07/1.27      inference('cnf', [status(esa)], [t24_xboole_1])).
% 1.07/1.27  thf('28', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ k1_xboole_0))
% 1.07/1.27           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 1.07/1.27      inference('sup+', [status(thm)], ['26', '27'])).
% 1.07/1.27  thf('29', plain,
% 1.07/1.27      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 1.07/1.27      inference('cnf', [status(esa)], [t2_boole])).
% 1.07/1.27  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.07/1.27      inference('sup+', [status(thm)], ['20', '25'])).
% 1.07/1.27  thf('31', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 1.07/1.27      inference('demod', [status(thm)], ['28', '29', '30'])).
% 1.07/1.27  thf('32', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.27      inference('sup+', [status(thm)], ['19', '31'])).
% 1.07/1.27  thf('33', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.07/1.27      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.07/1.27  thf('34', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 1.07/1.27      inference('demod', [status(thm)], ['28', '29', '30'])).
% 1.07/1.27  thf('35', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.07/1.27      inference('sup+', [status(thm)], ['33', '34'])).
% 1.07/1.27  thf('36', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ X1 @ X0)
% 1.07/1.27           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.27      inference('sup+', [status(thm)], ['32', '35'])).
% 1.07/1.27  thf('37', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 1.07/1.27      inference('demod', [status(thm)], ['6', '7'])).
% 1.07/1.27  thf('38', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.07/1.27      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.07/1.27  thf('39', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.07/1.27      inference('demod', [status(thm)], ['10', '11', '12'])).
% 1.07/1.27  thf('40', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.07/1.27      inference('sup+', [status(thm)], ['38', '39'])).
% 1.07/1.27  thf('41', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ X0 @ X1)
% 1.07/1.27           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 1.07/1.27      inference('sup+', [status(thm)], ['37', '40'])).
% 1.07/1.27  thf('42', plain,
% 1.07/1.27      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 1.07/1.27           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.07/1.27      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.07/1.27  thf('43', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ X0 @ X1)
% 1.07/1.27           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.27      inference('demod', [status(thm)], ['41', '42'])).
% 1.07/1.27  thf('44', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 1.07/1.27      inference('sup+', [status(thm)], ['36', '43'])).
% 1.07/1.27  thf('45', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ X1 @ X0)
% 1.07/1.27           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.27      inference('sup+', [status(thm)], ['32', '35'])).
% 1.07/1.27  thf('46', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ X0 @ X1)
% 1.07/1.27           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.27      inference('sup+', [status(thm)], ['44', '45'])).
% 1.07/1.27  thf('47', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ (k3_xboole_0 @ sk_D @ X0) @ sk_C)
% 1.07/1.27           = (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_C @ X0)))),
% 1.07/1.27      inference('sup+', [status(thm)], ['16', '46'])).
% 1.07/1.27  thf('48', plain,
% 1.07/1.27      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 1.07/1.27           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.07/1.27      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.07/1.27  thf('49', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 1.07/1.27      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.07/1.27  thf('50', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 1.07/1.27      inference('demod', [status(thm)], ['28', '29', '30'])).
% 1.07/1.27  thf('51', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.07/1.27      inference('sup+', [status(thm)], ['49', '50'])).
% 1.07/1.27  thf('52', plain,
% 1.07/1.27      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 1.07/1.27           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.07/1.27      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.07/1.27  thf('53', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ X0 @ X1)
% 1.07/1.27           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.07/1.27      inference('sup+', [status(thm)], ['51', '52'])).
% 1.07/1.27  thf('54', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ sk_D @ (k3_xboole_0 @ X0 @ sk_C))
% 1.07/1.27           = (k3_xboole_0 @ sk_C @ X0))),
% 1.07/1.27      inference('demod', [status(thm)], ['47', '48', '53'])).
% 1.07/1.27  thf('55', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.07/1.27      inference('sup+', [status(thm)], ['20', '25'])).
% 1.07/1.27  thf('56', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.07/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.27  thf('57', plain,
% 1.07/1.27      (![X3 : $i, X4 : $i]:
% 1.07/1.27         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 1.07/1.27      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.07/1.27  thf('58', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 1.07/1.27      inference('sup-', [status(thm)], ['56', '57'])).
% 1.07/1.27  thf('59', plain,
% 1.07/1.27      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.07/1.27         ((k2_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15))
% 1.07/1.27           = (k3_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ 
% 1.07/1.27              (k2_xboole_0 @ X13 @ X15)))),
% 1.07/1.27      inference('cnf', [status(esa)], [t24_xboole_1])).
% 1.07/1.27  thf('60', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         ((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 1.07/1.27           = (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.07/1.27      inference('sup+', [status(thm)], ['58', '59'])).
% 1.07/1.27  thf('61', plain,
% 1.07/1.27      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ k1_xboole_0))
% 1.07/1.27         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.07/1.27      inference('sup+', [status(thm)], ['55', '60'])).
% 1.07/1.27  thf('62', plain,
% 1.07/1.27      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 1.07/1.27      inference('cnf', [status(esa)], [t2_boole])).
% 1.07/1.27  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.07/1.27      inference('sup+', [status(thm)], ['20', '25'])).
% 1.07/1.27  thf('64', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.07/1.27      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.07/1.27  thf('65', plain,
% 1.07/1.27      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 1.07/1.27           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.07/1.27      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.07/1.27  thf('66', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ sk_A @ X0)
% 1.07/1.27           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 1.07/1.27      inference('sup+', [status(thm)], ['64', '65'])).
% 1.07/1.27  thf('67', plain,
% 1.07/1.27      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.07/1.27         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 1.07/1.27           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.07/1.27      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.07/1.27  thf('68', plain,
% 1.07/1.27      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 1.07/1.27      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.07/1.27  thf('69', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.27         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.07/1.27          (k3_xboole_0 @ X2 @ X1))),
% 1.07/1.27      inference('sup+', [status(thm)], ['67', '68'])).
% 1.07/1.27  thf('70', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         (r1_tarski @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ sk_A @ X0)) @ 
% 1.07/1.27          (k3_xboole_0 @ X1 @ sk_B))),
% 1.07/1.27      inference('sup+', [status(thm)], ['66', '69'])).
% 1.07/1.27  thf('71', plain,
% 1.07/1.27      ((r1_tarski @ (k3_xboole_0 @ sk_C @ sk_A) @ (k3_xboole_0 @ sk_D @ sk_B))),
% 1.07/1.27      inference('sup+', [status(thm)], ['54', '70'])).
% 1.07/1.27  thf('72', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 1.07/1.27      inference('sup+', [status(thm)], ['36', '43'])).
% 1.07/1.27  thf('73', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 1.07/1.27      inference('sup+', [status(thm)], ['36', '43'])).
% 1.07/1.27  thf('74', plain,
% 1.07/1.27      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ (k3_xboole_0 @ sk_B @ sk_D))),
% 1.07/1.27      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.07/1.27  thf('75', plain, ($false), inference('demod', [status(thm)], ['0', '74'])).
% 1.07/1.27  
% 1.07/1.27  % SZS output end Refutation
% 1.07/1.27  
% 1.07/1.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
