%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DeplE1xbK0

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:33 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 219 expanded)
%              Number of leaves         :   20 (  80 expanded)
%              Depth                    :   17
%              Number of atoms          :  766 (1629 expanded)
%              Number of equality atoms :   85 ( 180 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t63_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

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
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['19','20','25'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('40',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('45',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','52'])).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','55'])).

thf('57',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = sk_C ),
    inference('sup+',[status(thm)],['26','66'])).

thf('68',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('70',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('72',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_A ) )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_C )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['67','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('82',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','55'])).

thf('84',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['82','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['0','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DeplE1xbK0
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:36:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 438 iterations in 0.163s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.62  thf(t63_xboole_1, conjecture,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.39/0.62       ( r1_xboole_0 @ A @ C ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.62        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.39/0.62          ( r1_xboole_0 @ A @ C ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.39/0.62  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('1', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(d7_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.39/0.62       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      (![X4 : $i, X5 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.62  thf('3', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.62  thf(t48_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      (![X18 : $i, X19 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.39/0.62           = (k3_xboole_0 @ X18 @ X19))),
% 0.39/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      (![X18 : $i, X19 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.39/0.62           = (k3_xboole_0 @ X18 @ X19))),
% 0.39/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.62           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['4', '5'])).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 0.39/0.62         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['3', '6'])).
% 0.39/0.62  thf(t3_boole, axiom,
% 0.39/0.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.62  thf('8', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.62  thf('9', plain,
% 0.39/0.62      (((sk_B) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.39/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.62  thf('10', plain,
% 0.39/0.62      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      (![X18 : $i, X19 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.39/0.62           = (k3_xboole_0 @ X18 @ X19))),
% 0.39/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.62  thf(t36_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.39/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.62  thf('13', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.39/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.62  thf('14', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.39/0.62      inference('sup+', [status(thm)], ['10', '13'])).
% 0.39/0.62  thf(t12_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i]:
% 0.39/0.62         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.62  thf(commutativity_k2_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.62  thf('18', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['16', '17'])).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_B)
% 0.39/0.62         = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.39/0.62      inference('sup+', [status(thm)], ['9', '18'])).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.62  thf('21', plain,
% 0.39/0.62      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.39/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.62  thf('22', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i]:
% 0.39/0.62         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.62  thf('23', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.62  thf('24', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.62  thf('25', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.62  thf('26', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.39/0.62      inference('demod', [status(thm)], ['19', '20', '25'])).
% 0.39/0.62  thf(t41_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.62       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.62  thf('27', plain,
% 0.39/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.39/0.62           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.62  thf(t39_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.62  thf('28', plain,
% 0.39/0.62      (![X12 : $i, X13 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.39/0.62           = (k2_xboole_0 @ X12 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.62  thf('29', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.39/0.62           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['27', '28'])).
% 0.39/0.62  thf('30', plain,
% 0.39/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.39/0.62           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.62  thf('31', plain,
% 0.39/0.62      (![X18 : $i, X19 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.39/0.62           = (k3_xboole_0 @ X18 @ X19))),
% 0.39/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X2 @ 
% 0.39/0.62           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 0.39/0.62           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['30', '31'])).
% 0.39/0.62  thf('33', plain,
% 0.39/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.39/0.62           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.62  thf('34', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X2 @ 
% 0.39/0.62           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 0.39/0.62           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['32', '33'])).
% 0.39/0.62  thf('35', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.39/0.62           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['29', '34'])).
% 0.39/0.62  thf('36', plain,
% 0.39/0.62      (![X12 : $i, X13 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.39/0.62           = (k2_xboole_0 @ X12 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.62  thf('37', plain,
% 0.39/0.62      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.62  thf('38', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))
% 0.39/0.62           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.39/0.62  thf('39', plain,
% 0.39/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.39/0.62           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.62  thf('40', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.62  thf('41', plain,
% 0.39/0.62      (![X18 : $i, X19 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.39/0.62           = (k3_xboole_0 @ X18 @ X19))),
% 0.39/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.62  thf('42', plain,
% 0.39/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['40', '41'])).
% 0.39/0.62  thf('43', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.62  thf('44', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.62  thf(t1_boole, axiom,
% 0.39/0.62    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.62  thf('45', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.39/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.62  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['44', '45'])).
% 0.39/0.62  thf('47', plain,
% 0.39/0.62      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['43', '46'])).
% 0.39/0.62  thf('48', plain,
% 0.39/0.62      (![X18 : $i, X19 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.39/0.62           = (k3_xboole_0 @ X18 @ X19))),
% 0.39/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.62  thf('49', plain,
% 0.39/0.62      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['47', '48'])).
% 0.39/0.62  thf('50', plain,
% 0.39/0.62      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['49', '50'])).
% 0.39/0.62  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.62      inference('demod', [status(thm)], ['42', '51'])).
% 0.39/0.62  thf('53', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.39/0.62           = (k1_xboole_0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['39', '52'])).
% 0.39/0.62  thf('54', plain,
% 0.39/0.62      (![X12 : $i, X13 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.39/0.62           = (k2_xboole_0 @ X12 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.62  thf('55', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.39/0.62      inference('demod', [status(thm)], ['53', '54'])).
% 0.39/0.62  thf('56', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['38', '55'])).
% 0.39/0.62  thf('57', plain,
% 0.39/0.62      (![X18 : $i, X19 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.39/0.62           = (k3_xboole_0 @ X18 @ X19))),
% 0.39/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.62  thf('58', plain,
% 0.39/0.62      (![X12 : $i, X13 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.39/0.62           = (k2_xboole_0 @ X12 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.62  thf('59', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.62           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['57', '58'])).
% 0.39/0.62  thf('60', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.62  thf('61', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.62  thf('62', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.62  thf('63', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.39/0.62           = (X1))),
% 0.39/0.62      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.39/0.62  thf('64', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ k1_xboole_0 @ 
% 0.39/0.62           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))) = (X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['56', '63'])).
% 0.39/0.62  thf('65', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['44', '45'])).
% 0.39/0.62  thf('66', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['64', '65'])).
% 0.39/0.62  thf('67', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (sk_C))),
% 0.39/0.62      inference('sup+', [status(thm)], ['26', '66'])).
% 0.39/0.62  thf('68', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('69', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i]:
% 0.39/0.62         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.62  thf('70', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.39/0.62  thf('71', plain,
% 0.39/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.39/0.62           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.62  thf('72', plain,
% 0.39/0.62      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.39/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.62  thf('73', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 0.39/0.62          (k4_xboole_0 @ X2 @ X1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['71', '72'])).
% 0.39/0.62  thf('74', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_A))),
% 0.39/0.62      inference('sup+', [status(thm)], ['70', '73'])).
% 0.39/0.62  thf('75', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i]:
% 0.39/0.62         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.62  thf('76', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_A))
% 0.39/0.62           = (k4_xboole_0 @ X0 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['74', '75'])).
% 0.39/0.62  thf('77', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.62  thf('78', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B))
% 0.39/0.62           = (k4_xboole_0 @ X0 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['76', '77'])).
% 0.39/0.62  thf('79', plain,
% 0.39/0.62      (((k2_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_C)
% 0.39/0.62         = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.39/0.62      inference('sup+', [status(thm)], ['67', '78'])).
% 0.39/0.62  thf('80', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.62  thf('81', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.62  thf('82', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.39/0.62  thf('83', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['38', '55'])).
% 0.39/0.62  thf('84', plain,
% 0.39/0.62      (![X4 : $i, X6 : $i]:
% 0.39/0.62         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.62  thf('85', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.62          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['83', '84'])).
% 0.39/0.62  thf('86', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['85'])).
% 0.39/0.62  thf('87', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.39/0.62      inference('sup+', [status(thm)], ['82', '86'])).
% 0.39/0.62  thf('88', plain, ($false), inference('demod', [status(thm)], ['0', '87'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.39/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
