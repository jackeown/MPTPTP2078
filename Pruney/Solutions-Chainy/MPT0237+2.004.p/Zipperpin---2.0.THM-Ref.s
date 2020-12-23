%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EtKagTO4Hi

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:59 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  157 (1468 expanded)
%              Number of leaves         :   32 ( 510 expanded)
%              Depth                    :   26
%              Number of atoms          : 1217 (11298 expanded)
%              Number of equality atoms :  150 (1466 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t32_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X63: $i,X64: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X63 ) @ ( k1_tarski @ X64 ) )
        = ( k2_tarski @ X63 @ X64 ) )
      | ( X63 = X64 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('5',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['3','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X6 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','54'])).

thf('56',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('57',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X6 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','54'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','63'])).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('66',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','72'])).

thf('74',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('75',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['73','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','70','71'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['23','80'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('82',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('83',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( r2_hidden @ X24 @ X28 )
      | ( X28
       != ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('84',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X24 @ ( k1_enumset1 @ X27 @ X26 @ X25 ) )
      | ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['82','84'])).

thf('86',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X19 )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('87',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ~ ( zip_tseitin_0 @ X19 @ X21 @ X22 @ X19 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('89',plain,(
    ! [X59: $i,X60: $i] :
      ( ( ( k3_xboole_0 @ X60 @ ( k1_tarski @ X59 ) )
        = ( k1_tarski @ X59 ) )
      | ~ ( r2_hidden @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('92',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('93',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X6 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('101',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['91','108'])).

thf('110',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['90','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['81','114'])).

thf('116',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('117',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','54'])).

thf('120',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['117'])).

thf('121',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('122',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','118','119','120','121'])).

thf('123',plain,(
    $false ),
    inference(simplify,[status(thm)],['122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EtKagTO4Hi
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:20:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.45/1.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.45/1.64  % Solved by: fo/fo7.sh
% 1.45/1.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.45/1.64  % done 1843 iterations in 1.198s
% 1.45/1.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.45/1.64  % SZS output start Refutation
% 1.45/1.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.45/1.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.45/1.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.45/1.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.45/1.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.45/1.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.45/1.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.45/1.64  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.45/1.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.45/1.64  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.45/1.64  thf(sk_B_type, type, sk_B: $i).
% 1.45/1.64  thf(sk_A_type, type, sk_A: $i).
% 1.45/1.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.45/1.64  thf(t32_zfmisc_1, conjecture,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 1.45/1.64       ( k2_tarski @ A @ B ) ))).
% 1.45/1.64  thf(zf_stmt_0, negated_conjecture,
% 1.45/1.64    (~( ![A:$i,B:$i]:
% 1.45/1.64        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 1.45/1.64          ( k2_tarski @ A @ B ) ) )),
% 1.45/1.64    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 1.45/1.64  thf('0', plain,
% 1.45/1.64      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 1.45/1.64         != (k2_tarski @ sk_A @ sk_B))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf(l51_zfmisc_1, axiom,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.45/1.64  thf('1', plain,
% 1.45/1.64      (![X61 : $i, X62 : $i]:
% 1.45/1.64         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 1.45/1.64      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.45/1.64  thf('2', plain,
% 1.45/1.64      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.45/1.64         != (k2_tarski @ sk_A @ sk_B))),
% 1.45/1.64      inference('demod', [status(thm)], ['0', '1'])).
% 1.45/1.64  thf(t29_zfmisc_1, axiom,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( ( A ) != ( B ) ) =>
% 1.45/1.64       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.45/1.64         ( k2_tarski @ A @ B ) ) ))).
% 1.45/1.64  thf('3', plain,
% 1.45/1.64      (![X63 : $i, X64 : $i]:
% 1.45/1.64         (((k5_xboole_0 @ (k1_tarski @ X63) @ (k1_tarski @ X64))
% 1.45/1.64            = (k2_tarski @ X63 @ X64))
% 1.45/1.64          | ((X63) = (X64)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 1.45/1.64  thf(t69_enumset1, axiom,
% 1.45/1.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.45/1.64  thf('4', plain, (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 1.45/1.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.45/1.64  thf('5', plain,
% 1.45/1.64      (![X61 : $i, X62 : $i]:
% 1.45/1.64         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 1.45/1.64      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.45/1.64  thf('6', plain,
% 1.45/1.64      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['4', '5'])).
% 1.45/1.64  thf(t21_xboole_1, axiom,
% 1.45/1.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.45/1.64  thf('7', plain,
% 1.45/1.64      (![X9 : $i, X10 : $i]:
% 1.45/1.64         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 1.45/1.64      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.45/1.64  thf('8', plain,
% 1.45/1.64      (![X0 : $i]: ((k3_xboole_0 @ X0 @ (k3_tarski @ (k1_tarski @ X0))) = (X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['6', '7'])).
% 1.45/1.64  thf(t100_xboole_1, axiom,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.45/1.64  thf('9', plain,
% 1.45/1.64      (![X4 : $i, X5 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X4 @ X5)
% 1.45/1.64           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.45/1.64  thf('10', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X0 @ (k3_tarski @ (k1_tarski @ X0)))
% 1.45/1.64           = (k5_xboole_0 @ X0 @ X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['8', '9'])).
% 1.45/1.64  thf('11', plain,
% 1.45/1.64      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['4', '5'])).
% 1.45/1.64  thf(t46_xboole_1, axiom,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.45/1.64  thf('12', plain,
% 1.45/1.64      (![X11 : $i, X12 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.45/1.64  thf('13', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X0 @ (k3_tarski @ (k1_tarski @ X0))) = (k1_xboole_0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['11', '12'])).
% 1.45/1.64  thf('14', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['10', '13'])).
% 1.45/1.64  thf(t91_xboole_1, axiom,
% 1.45/1.64    (![A:$i,B:$i,C:$i]:
% 1.45/1.64     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.45/1.64       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.45/1.64  thf('15', plain,
% 1.45/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.45/1.64         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.45/1.64           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.45/1.64  thf('16', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.45/1.64           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['14', '15'])).
% 1.45/1.64  thf(commutativity_k5_xboole_0, axiom,
% 1.45/1.64    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.45/1.64  thf('17', plain,
% 1.45/1.64      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.45/1.64  thf(t5_boole, axiom,
% 1.45/1.64    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.45/1.64  thf('18', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.45/1.64      inference('cnf', [status(esa)], [t5_boole])).
% 1.45/1.64  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['17', '18'])).
% 1.45/1.64  thf('20', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.45/1.64      inference('demod', [status(thm)], ['16', '19'])).
% 1.45/1.64  thf('21', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         (((k1_tarski @ X0)
% 1.45/1.64            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))
% 1.45/1.64          | ((X1) = (X0)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['3', '20'])).
% 1.45/1.64  thf('22', plain,
% 1.45/1.64      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.45/1.64  thf('23', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         (((k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 1.45/1.64            = (k1_tarski @ X0))
% 1.45/1.64          | ((X1) = (X0)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['21', '22'])).
% 1.45/1.64  thf('24', plain,
% 1.45/1.64      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.45/1.64  thf('25', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.45/1.64      inference('demod', [status(thm)], ['16', '19'])).
% 1.45/1.64  thf('26', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['24', '25'])).
% 1.45/1.64  thf('27', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.45/1.64      inference('cnf', [status(esa)], [t5_boole])).
% 1.45/1.64  thf(t94_xboole_1, axiom,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( k2_xboole_0 @ A @ B ) =
% 1.45/1.64       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.45/1.64  thf('28', plain,
% 1.45/1.64      (![X17 : $i, X18 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X17 @ X18)
% 1.45/1.64           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 1.45/1.64              (k3_xboole_0 @ X17 @ X18)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.45/1.64  thf('29', plain,
% 1.45/1.64      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.45/1.64  thf('30', plain,
% 1.45/1.64      (![X17 : $i, X18 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X17 @ X18)
% 1.45/1.64           = (k5_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ 
% 1.45/1.64              (k5_xboole_0 @ X17 @ X18)))),
% 1.45/1.64      inference('demod', [status(thm)], ['28', '29'])).
% 1.45/1.64  thf('31', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 1.45/1.64           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['27', '30'])).
% 1.45/1.64  thf('32', plain,
% 1.45/1.64      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.45/1.64  thf('33', plain,
% 1.45/1.64      (![X4 : $i, X5 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X4 @ X5)
% 1.45/1.64           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.45/1.64  thf('34', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.45/1.64      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.45/1.64  thf('35', plain,
% 1.45/1.64      (![X9 : $i, X10 : $i]:
% 1.45/1.64         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 1.45/1.64      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.45/1.64  thf('36', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['34', '35'])).
% 1.45/1.64  thf(t112_xboole_1, axiom,
% 1.45/1.64    (![A:$i,B:$i,C:$i]:
% 1.45/1.64     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 1.45/1.64       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.45/1.64  thf('37', plain,
% 1.45/1.64      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.45/1.64         ((k5_xboole_0 @ (k3_xboole_0 @ X6 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 1.45/1.64           = (k3_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8))),
% 1.45/1.64      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.45/1.64  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['10', '13'])).
% 1.45/1.64  thf('39', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['37', '38'])).
% 1.45/1.64  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['10', '13'])).
% 1.45/1.64  thf('41', plain,
% 1.45/1.64      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.45/1.64      inference('demod', [status(thm)], ['39', '40'])).
% 1.45/1.64  thf(commutativity_k3_xboole_0, axiom,
% 1.45/1.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.45/1.64  thf('42', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.45/1.64  thf('43', plain,
% 1.45/1.64      (![X4 : $i, X5 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X4 @ X5)
% 1.45/1.64           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.45/1.64  thf('44', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X0 @ X1)
% 1.45/1.64           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['42', '43'])).
% 1.45/1.64  thf('45', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['41', '44'])).
% 1.45/1.64  thf('46', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.45/1.64      inference('cnf', [status(esa)], [t5_boole])).
% 1.45/1.64  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['45', '46'])).
% 1.45/1.64  thf('48', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.45/1.64      inference('demod', [status(thm)], ['36', '47'])).
% 1.45/1.64  thf('49', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['10', '13'])).
% 1.45/1.64  thf('50', plain,
% 1.45/1.64      (![X17 : $i, X18 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X17 @ X18)
% 1.45/1.64           = (k5_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ 
% 1.45/1.64              (k5_xboole_0 @ X17 @ X18)))),
% 1.45/1.64      inference('demod', [status(thm)], ['28', '29'])).
% 1.45/1.64  thf('51', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X0 @ X0)
% 1.45/1.64           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['49', '50'])).
% 1.45/1.64  thf('52', plain,
% 1.45/1.64      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.45/1.64  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['17', '18'])).
% 1.45/1.64  thf('54', plain,
% 1.45/1.64      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.45/1.64      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.45/1.64  thf('55', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['48', '54'])).
% 1.45/1.64  thf('56', plain,
% 1.45/1.64      (![X9 : $i, X10 : $i]:
% 1.45/1.64         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 1.45/1.64      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.45/1.64  thf('57', plain,
% 1.45/1.64      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.45/1.64         ((k5_xboole_0 @ (k3_xboole_0 @ X6 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 1.45/1.64           = (k3_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8))),
% 1.45/1.64      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.45/1.64  thf('58', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.64         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))
% 1.45/1.64           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X0 @ X1)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['56', '57'])).
% 1.45/1.64  thf('59', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.45/1.64           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X0)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['55', '58'])).
% 1.45/1.64  thf('60', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X0 @ X1)
% 1.45/1.64           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['42', '43'])).
% 1.45/1.64  thf('61', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['48', '54'])).
% 1.45/1.64  thf('62', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.45/1.64  thf('63', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X0 @ X1)
% 1.45/1.64           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.45/1.64      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 1.45/1.64  thf('64', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1))
% 1.45/1.64           = (k3_xboole_0 @ X1 @ X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['26', '63'])).
% 1.45/1.64  thf('65', plain,
% 1.45/1.64      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.45/1.64  thf('66', plain,
% 1.45/1.64      (![X17 : $i, X18 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X17 @ X18)
% 1.45/1.64           = (k5_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ 
% 1.45/1.64              (k5_xboole_0 @ X17 @ X18)))),
% 1.45/1.64      inference('demod', [status(thm)], ['28', '29'])).
% 1.45/1.64  thf('67', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X0 @ X1)
% 1.45/1.64           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['65', '66'])).
% 1.45/1.64  thf('68', plain,
% 1.45/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.45/1.64         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.45/1.64           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.45/1.64  thf('69', plain,
% 1.45/1.64      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.45/1.64  thf('70', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.64         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.45/1.64           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['68', '69'])).
% 1.45/1.64  thf('71', plain,
% 1.45/1.64      (![X4 : $i, X5 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X4 @ X5)
% 1.45/1.64           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.45/1.64  thf('72', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X0 @ X1)
% 1.45/1.64           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.45/1.64      inference('demod', [status(thm)], ['67', '70', '71'])).
% 1.45/1.64  thf('73', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1))
% 1.45/1.64           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['64', '72'])).
% 1.45/1.64  thf('74', plain,
% 1.45/1.64      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.45/1.64  thf('75', plain,
% 1.45/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.45/1.64         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.45/1.64           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.45/1.64  thf('76', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.64         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 1.45/1.64           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['74', '75'])).
% 1.45/1.64  thf('77', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X0 @ X1)
% 1.45/1.64           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['42', '43'])).
% 1.45/1.64  thf('78', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1))
% 1.45/1.64           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.45/1.64      inference('demod', [status(thm)], ['73', '76', '77'])).
% 1.45/1.64  thf('79', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X0 @ X1)
% 1.45/1.64           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.45/1.64      inference('demod', [status(thm)], ['67', '70', '71'])).
% 1.45/1.64  thf('80', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1))
% 1.45/1.64           = (k2_xboole_0 @ X0 @ X1))),
% 1.45/1.64      inference('demod', [status(thm)], ['78', '79'])).
% 1.45/1.64  thf('81', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.45/1.64            = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1)))
% 1.45/1.64          | ((X1) = (X0)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['23', '80'])).
% 1.45/1.64  thf(t70_enumset1, axiom,
% 1.45/1.64    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.45/1.64  thf('82', plain,
% 1.45/1.64      (![X32 : $i, X33 : $i]:
% 1.45/1.64         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 1.45/1.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.45/1.64  thf(d1_enumset1, axiom,
% 1.45/1.64    (![A:$i,B:$i,C:$i,D:$i]:
% 1.45/1.64     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.45/1.64       ( ![E:$i]:
% 1.45/1.64         ( ( r2_hidden @ E @ D ) <=>
% 1.45/1.64           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.45/1.64  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.45/1.64  thf(zf_stmt_2, axiom,
% 1.45/1.64    (![E:$i,C:$i,B:$i,A:$i]:
% 1.45/1.64     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.45/1.64       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.45/1.64  thf(zf_stmt_3, axiom,
% 1.45/1.64    (![A:$i,B:$i,C:$i,D:$i]:
% 1.45/1.64     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.45/1.64       ( ![E:$i]:
% 1.45/1.64         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.45/1.64  thf('83', plain,
% 1.45/1.64      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.45/1.64         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 1.45/1.64          | (r2_hidden @ X24 @ X28)
% 1.45/1.64          | ((X28) != (k1_enumset1 @ X27 @ X26 @ X25)))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.45/1.64  thf('84', plain,
% 1.45/1.64      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.45/1.64         ((r2_hidden @ X24 @ (k1_enumset1 @ X27 @ X26 @ X25))
% 1.45/1.64          | (zip_tseitin_0 @ X24 @ X25 @ X26 @ X27))),
% 1.45/1.64      inference('simplify', [status(thm)], ['83'])).
% 1.45/1.64  thf('85', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.64         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.45/1.64          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.45/1.64      inference('sup+', [status(thm)], ['82', '84'])).
% 1.45/1.64  thf('86', plain,
% 1.45/1.64      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.45/1.64         (((X20) != (X19)) | ~ (zip_tseitin_0 @ X20 @ X21 @ X22 @ X19))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.45/1.64  thf('87', plain,
% 1.45/1.64      (![X19 : $i, X21 : $i, X22 : $i]:
% 1.45/1.64         ~ (zip_tseitin_0 @ X19 @ X21 @ X22 @ X19)),
% 1.45/1.64      inference('simplify', [status(thm)], ['86'])).
% 1.45/1.64  thf('88', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.45/1.64      inference('sup-', [status(thm)], ['85', '87'])).
% 1.45/1.64  thf(l31_zfmisc_1, axiom,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( r2_hidden @ A @ B ) =>
% 1.45/1.64       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 1.45/1.64  thf('89', plain,
% 1.45/1.64      (![X59 : $i, X60 : $i]:
% 1.45/1.64         (((k3_xboole_0 @ X60 @ (k1_tarski @ X59)) = (k1_tarski @ X59))
% 1.45/1.64          | ~ (r2_hidden @ X59 @ X60))),
% 1.45/1.64      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 1.45/1.64  thf('90', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k3_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 1.45/1.64           = (k1_tarski @ X1))),
% 1.45/1.64      inference('sup-', [status(thm)], ['88', '89'])).
% 1.45/1.64  thf('91', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.45/1.64  thf('92', plain,
% 1.45/1.64      (![X4 : $i, X5 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X4 @ X5)
% 1.45/1.64           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.45/1.64  thf('93', plain,
% 1.45/1.64      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.45/1.64         ((k5_xboole_0 @ (k3_xboole_0 @ X6 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 1.45/1.64           = (k3_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8))),
% 1.45/1.64      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.45/1.64  thf('94', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.45/1.64           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['92', '93'])).
% 1.45/1.64  thf('95', plain,
% 1.45/1.64      (![X4 : $i, X5 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X4 @ X5)
% 1.45/1.64           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.45/1.64  thf('96', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.45/1.64  thf('97', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.45/1.64           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.45/1.64      inference('demod', [status(thm)], ['94', '95', '96'])).
% 1.45/1.64  thf('98', plain,
% 1.45/1.64      (![X17 : $i, X18 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X17 @ X18)
% 1.45/1.64           = (k5_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ 
% 1.45/1.64              (k5_xboole_0 @ X17 @ X18)))),
% 1.45/1.64      inference('demod', [status(thm)], ['28', '29'])).
% 1.45/1.64  thf('99', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.64         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.45/1.64           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['68', '69'])).
% 1.45/1.64  thf('100', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X0 @ X1)
% 1.45/1.64           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['42', '43'])).
% 1.45/1.64  thf('101', plain,
% 1.45/1.64      (![X17 : $i, X18 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X17 @ X18)
% 1.45/1.64           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 1.45/1.64      inference('demod', [status(thm)], ['98', '99', '100'])).
% 1.45/1.64  thf('102', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.45/1.64      inference('demod', [status(thm)], ['16', '19'])).
% 1.45/1.64  thf('103', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X0 @ X1)
% 1.45/1.64           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.45/1.64      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 1.45/1.64  thf('104', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 1.45/1.64           = (k3_xboole_0 @ X1 @ X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['102', '103'])).
% 1.45/1.64  thf('105', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.45/1.64           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['101', '104'])).
% 1.45/1.64  thf('106', plain,
% 1.45/1.64      (![X11 : $i, X12 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.45/1.64  thf('107', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.45/1.64      inference('demod', [status(thm)], ['105', '106'])).
% 1.45/1.64  thf('108', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.45/1.64      inference('demod', [status(thm)], ['97', '107'])).
% 1.45/1.64  thf('109', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['91', '108'])).
% 1.45/1.64  thf('110', plain,
% 1.45/1.64      (![X17 : $i, X18 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X17 @ X18)
% 1.45/1.64           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 1.45/1.64      inference('demod', [status(thm)], ['98', '99', '100'])).
% 1.45/1.64  thf('111', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.45/1.64           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['109', '110'])).
% 1.45/1.64  thf('112', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.45/1.64      inference('cnf', [status(esa)], [t5_boole])).
% 1.45/1.64  thf('113', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 1.45/1.64      inference('demod', [status(thm)], ['111', '112'])).
% 1.45/1.64  thf('114', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))
% 1.45/1.64           = (k2_tarski @ X0 @ X1))),
% 1.45/1.64      inference('sup+', [status(thm)], ['90', '113'])).
% 1.45/1.64  thf('115', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.45/1.64            = (k2_tarski @ X1 @ X0))
% 1.45/1.64          | ((X1) = (X0)))),
% 1.45/1.64      inference('demod', [status(thm)], ['81', '114'])).
% 1.45/1.64  thf('116', plain,
% 1.45/1.64      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.45/1.64         != (k2_tarski @ sk_A @ sk_B))),
% 1.45/1.64      inference('demod', [status(thm)], ['0', '1'])).
% 1.45/1.64  thf('117', plain,
% 1.45/1.64      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 1.45/1.64        | ((sk_A) = (sk_B)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['115', '116'])).
% 1.45/1.64  thf('118', plain, (((sk_A) = (sk_B))),
% 1.45/1.64      inference('simplify', [status(thm)], ['117'])).
% 1.45/1.64  thf('119', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['48', '54'])).
% 1.45/1.64  thf('120', plain, (((sk_A) = (sk_B))),
% 1.45/1.64      inference('simplify', [status(thm)], ['117'])).
% 1.45/1.64  thf('121', plain,
% 1.45/1.64      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 1.45/1.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.45/1.64  thf('122', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 1.45/1.64      inference('demod', [status(thm)], ['2', '118', '119', '120', '121'])).
% 1.45/1.64  thf('123', plain, ($false), inference('simplify', [status(thm)], ['122'])).
% 1.45/1.64  
% 1.45/1.64  % SZS output end Refutation
% 1.45/1.64  
% 1.45/1.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
