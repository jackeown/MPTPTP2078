%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JBnukSDGzR

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:57 EST 2020

% Result     : Theorem 2.74s
% Output     : Refutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  164 (1109 expanded)
%              Number of leaves         :   22 ( 378 expanded)
%              Depth                    :   20
%              Number of atoms          : 1157 (8763 expanded)
%              Number of equality atoms :  146 (1062 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
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

thf('2',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('22',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = sk_C ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

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
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['26','44'])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['17','45'])).

thf('47',plain,(
    r1_tarski @ sk_A @ sk_D ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('51',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_D ) @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('54',plain,
    ( ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('56',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('59',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('61',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('63',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('70',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('74',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = sk_B ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('76',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('78',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference('sup+',[status(thm)],['76','77'])).

thf('80',plain,
    ( sk_D
    = ( k3_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['67','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('83',plain,(
    sk_D = sk_A ),
    inference(demod,[status(thm)],['51','80','81','82'])).

thf('84',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['2','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('86',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('87',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','94'])).

thf('96',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['74','75'])).

thf('97',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_D ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_D ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    sk_D = sk_A ),
    inference(demod,[status(thm)],['51','80','81','82'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_A ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['84','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_A ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('107',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('109',plain,
    ( ( k2_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('112',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('113',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('114',plain,(
    r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('116',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('118',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('121',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['22','25'])).

thf('123',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_B ) )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['121','124'])).

thf('126',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('127',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('128',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['22','25'])).

thf('129',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['125','126','127','128'])).

thf('130',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['129','136'])).

thf('138',plain,(
    sk_C = sk_B ),
    inference(demod,[status(thm)],['109','110','111','137'])).

thf('139',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['138','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JBnukSDGzR
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.74/2.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.74/2.95  % Solved by: fo/fo7.sh
% 2.74/2.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.74/2.95  % done 3144 iterations in 2.498s
% 2.74/2.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.74/2.95  % SZS output start Refutation
% 2.74/2.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.74/2.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.74/2.95  thf(sk_D_type, type, sk_D: $i).
% 2.74/2.95  thf(sk_C_type, type, sk_C: $i).
% 2.74/2.95  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.74/2.95  thf(sk_A_type, type, sk_A: $i).
% 2.74/2.95  thf(sk_B_type, type, sk_B: $i).
% 2.74/2.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.74/2.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.74/2.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.74/2.95  thf(t72_xboole_1, conjecture,
% 2.74/2.95    (![A:$i,B:$i,C:$i,D:$i]:
% 2.74/2.95     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 2.74/2.95         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 2.74/2.95       ( ( C ) = ( B ) ) ))).
% 2.74/2.95  thf(zf_stmt_0, negated_conjecture,
% 2.74/2.95    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.74/2.95        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 2.74/2.95            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 2.74/2.95          ( ( C ) = ( B ) ) ) )),
% 2.74/2.95    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 2.74/2.95  thf('0', plain,
% 2.74/2.95      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 2.74/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.95  thf(commutativity_k2_xboole_0, axiom,
% 2.74/2.95    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.74/2.95  thf('1', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.74/2.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.74/2.95  thf('2', plain,
% 2.74/2.95      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 2.74/2.95      inference('demod', [status(thm)], ['0', '1'])).
% 2.74/2.95  thf(t41_xboole_1, axiom,
% 2.74/2.95    (![A:$i,B:$i,C:$i]:
% 2.74/2.95     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 2.74/2.95       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.74/2.95  thf('3', plain,
% 2.74/2.95      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.74/2.95           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.74/2.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.74/2.95  thf(t1_boole, axiom,
% 2.74/2.95    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.74/2.95  thf('4', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.74/2.95      inference('cnf', [status(esa)], [t1_boole])).
% 2.74/2.95  thf(t7_xboole_1, axiom,
% 2.74/2.95    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.74/2.95  thf('5', plain,
% 2.74/2.95      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 2.74/2.95      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.74/2.95  thf('6', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.74/2.95      inference('sup+', [status(thm)], ['4', '5'])).
% 2.74/2.95  thf(l32_xboole_1, axiom,
% 2.74/2.95    (![A:$i,B:$i]:
% 2.74/2.95     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.74/2.95  thf('7', plain,
% 2.74/2.95      (![X7 : $i, X9 : $i]:
% 2.74/2.95         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 2.74/2.95      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.74/2.95  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.74/2.95      inference('sup-', [status(thm)], ['6', '7'])).
% 2.74/2.95  thf('9', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 2.74/2.95           = (k1_xboole_0))),
% 2.74/2.95      inference('sup+', [status(thm)], ['3', '8'])).
% 2.74/2.95  thf(t39_xboole_1, axiom,
% 2.74/2.95    (![A:$i,B:$i]:
% 2.74/2.95     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.74/2.95  thf('10', plain,
% 2.74/2.95      (![X12 : $i, X13 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 2.74/2.95           = (k2_xboole_0 @ X12 @ X13))),
% 2.74/2.95      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.74/2.95  thf('11', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 2.74/2.95      inference('demod', [status(thm)], ['9', '10'])).
% 2.74/2.95  thf('12', plain,
% 2.74/2.95      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 2.74/2.95      inference('demod', [status(thm)], ['0', '1'])).
% 2.74/2.95  thf('13', plain,
% 2.74/2.95      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.74/2.95           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.74/2.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.74/2.95  thf('14', plain,
% 2.74/2.95      (![X7 : $i, X8 : $i]:
% 2.74/2.95         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 2.74/2.95      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.74/2.95  thf('15', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.95         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 2.74/2.95          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 2.74/2.95      inference('sup-', [status(thm)], ['13', '14'])).
% 2.74/2.95  thf('16', plain,
% 2.74/2.95      (![X0 : $i]:
% 2.74/2.95         (((k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)) != (k1_xboole_0))
% 2.74/2.95          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 2.74/2.95      inference('sup-', [status(thm)], ['12', '15'])).
% 2.74/2.95  thf('17', plain,
% 2.74/2.95      ((((k1_xboole_0) != (k1_xboole_0))
% 2.74/2.95        | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_D))),
% 2.74/2.95      inference('sup-', [status(thm)], ['11', '16'])).
% 2.74/2.95  thf('18', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 2.74/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.95  thf(d7_xboole_0, axiom,
% 2.74/2.95    (![A:$i,B:$i]:
% 2.74/2.95     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.74/2.95       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.74/2.95  thf('19', plain,
% 2.74/2.95      (![X4 : $i, X5 : $i]:
% 2.74/2.95         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 2.74/2.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.74/2.95  thf('20', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 2.74/2.95      inference('sup-', [status(thm)], ['18', '19'])).
% 2.74/2.95  thf(t51_xboole_1, axiom,
% 2.74/2.95    (![A:$i,B:$i]:
% 2.74/2.95     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 2.74/2.95       ( A ) ))).
% 2.74/2.95  thf('21', plain,
% 2.74/2.95      (![X20 : $i, X21 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 2.74/2.95           = (X20))),
% 2.74/2.95      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.74/2.95  thf('22', plain,
% 2.74/2.95      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A)) = (sk_C))),
% 2.74/2.95      inference('sup+', [status(thm)], ['20', '21'])).
% 2.74/2.95  thf('23', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.74/2.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.74/2.95  thf('24', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.74/2.95      inference('cnf', [status(esa)], [t1_boole])).
% 2.74/2.95  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.74/2.95      inference('sup+', [status(thm)], ['23', '24'])).
% 2.74/2.95  thf('26', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 2.74/2.95      inference('demod', [status(thm)], ['22', '25'])).
% 2.74/2.95  thf('27', plain,
% 2.74/2.95      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.74/2.95           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.74/2.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.74/2.95  thf('28', plain,
% 2.74/2.95      (![X12 : $i, X13 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 2.74/2.95           = (k2_xboole_0 @ X12 @ X13))),
% 2.74/2.95      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.74/2.95  thf('29', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 2.74/2.95           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 2.74/2.95      inference('sup+', [status(thm)], ['27', '28'])).
% 2.74/2.95  thf('30', plain,
% 2.74/2.95      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.74/2.95           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.74/2.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.74/2.95  thf(t48_xboole_1, axiom,
% 2.74/2.95    (![A:$i,B:$i]:
% 2.74/2.95     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.74/2.95  thf('31', plain,
% 2.74/2.95      (![X18 : $i, X19 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.74/2.95           = (k3_xboole_0 @ X18 @ X19))),
% 2.74/2.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.74/2.95  thf('32', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X2 @ 
% 2.74/2.95           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 2.74/2.95           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 2.74/2.95      inference('sup+', [status(thm)], ['30', '31'])).
% 2.74/2.95  thf('33', plain,
% 2.74/2.95      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.74/2.95           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.74/2.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.74/2.95  thf('34', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X2 @ 
% 2.74/2.95           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 2.74/2.95           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 2.74/2.95      inference('demod', [status(thm)], ['32', '33'])).
% 2.74/2.95  thf('35', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 2.74/2.95           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 2.74/2.95      inference('sup+', [status(thm)], ['29', '34'])).
% 2.74/2.95  thf('36', plain,
% 2.74/2.95      (![X12 : $i, X13 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 2.74/2.95           = (k2_xboole_0 @ X12 @ X13))),
% 2.74/2.95      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.74/2.95  thf(commutativity_k3_xboole_0, axiom,
% 2.74/2.95    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.74/2.95  thf('37', plain,
% 2.74/2.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.74/2.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.74/2.95  thf('38', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))
% 2.74/2.95           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.74/2.95      inference('demod', [status(thm)], ['35', '36', '37'])).
% 2.74/2.95  thf('39', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 2.74/2.95      inference('demod', [status(thm)], ['9', '10'])).
% 2.74/2.95  thf('40', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.74/2.95      inference('demod', [status(thm)], ['38', '39'])).
% 2.74/2.95  thf('41', plain,
% 2.74/2.95      (![X20 : $i, X21 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 2.74/2.95           = (X20))),
% 2.74/2.95      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.74/2.95  thf('42', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ k1_xboole_0 @ 
% 2.74/2.95           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))) = (X0))),
% 2.74/2.95      inference('sup+', [status(thm)], ['40', '41'])).
% 2.74/2.95  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.74/2.95      inference('sup+', [status(thm)], ['23', '24'])).
% 2.74/2.95  thf('44', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 2.74/2.95      inference('demod', [status(thm)], ['42', '43'])).
% 2.74/2.95  thf('45', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 2.74/2.95      inference('sup+', [status(thm)], ['26', '44'])).
% 2.74/2.95  thf('46', plain,
% 2.74/2.95      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_D))),
% 2.74/2.95      inference('demod', [status(thm)], ['17', '45'])).
% 2.74/2.95  thf('47', plain, ((r1_tarski @ sk_A @ sk_D)),
% 2.74/2.95      inference('simplify', [status(thm)], ['46'])).
% 2.74/2.95  thf('48', plain,
% 2.74/2.95      (![X7 : $i, X9 : $i]:
% 2.74/2.95         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 2.74/2.95      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.74/2.95  thf('49', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 2.74/2.95      inference('sup-', [status(thm)], ['47', '48'])).
% 2.74/2.95  thf('50', plain,
% 2.74/2.95      (![X20 : $i, X21 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 2.74/2.95           = (X20))),
% 2.74/2.95      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.74/2.95  thf('51', plain,
% 2.74/2.95      (((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_D) @ k1_xboole_0) = (sk_A))),
% 2.74/2.95      inference('sup+', [status(thm)], ['49', '50'])).
% 2.74/2.95  thf('52', plain,
% 2.74/2.95      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 2.74/2.95      inference('demod', [status(thm)], ['0', '1'])).
% 2.74/2.95  thf('53', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 2.74/2.95      inference('demod', [status(thm)], ['9', '10'])).
% 2.74/2.95  thf('54', plain,
% 2.74/2.95      (((k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 2.74/2.95      inference('sup+', [status(thm)], ['52', '53'])).
% 2.74/2.95  thf('55', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 2.74/2.95           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 2.74/2.95      inference('sup+', [status(thm)], ['27', '28'])).
% 2.74/2.95  thf('56', plain,
% 2.74/2.95      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 2.74/2.95         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)))),
% 2.74/2.95      inference('sup+', [status(thm)], ['54', '55'])).
% 2.74/2.95  thf('57', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.74/2.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.74/2.95  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.74/2.95      inference('sup+', [status(thm)], ['23', '24'])).
% 2.74/2.95  thf('59', plain,
% 2.74/2.95      (((sk_A) = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)))),
% 2.74/2.95      inference('demod', [status(thm)], ['56', '57', '58'])).
% 2.74/2.95  thf('60', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 2.74/2.95      inference('demod', [status(thm)], ['9', '10'])).
% 2.74/2.95  thf('61', plain,
% 2.74/2.95      (![X18 : $i, X19 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.74/2.95           = (k3_xboole_0 @ X18 @ X19))),
% 2.74/2.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.74/2.95  thf('62', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 2.74/2.95           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.74/2.95      inference('sup+', [status(thm)], ['60', '61'])).
% 2.74/2.95  thf(t3_boole, axiom,
% 2.74/2.95    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.74/2.95  thf('63', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 2.74/2.95      inference('cnf', [status(esa)], [t3_boole])).
% 2.74/2.95  thf('64', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.74/2.95      inference('demod', [status(thm)], ['62', '63'])).
% 2.74/2.95  thf('65', plain,
% 2.74/2.95      (((k4_xboole_0 @ sk_D @ sk_B)
% 2.74/2.95         = (k3_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A))),
% 2.74/2.95      inference('sup+', [status(thm)], ['59', '64'])).
% 2.74/2.95  thf('66', plain,
% 2.74/2.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.74/2.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.74/2.95  thf('67', plain,
% 2.74/2.95      (((k4_xboole_0 @ sk_D @ sk_B)
% 2.74/2.95         = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)))),
% 2.74/2.95      inference('demod', [status(thm)], ['65', '66'])).
% 2.74/2.95  thf('68', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 2.74/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.95  thf('69', plain,
% 2.74/2.95      (![X4 : $i, X5 : $i]:
% 2.74/2.95         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 2.74/2.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.74/2.95  thf('70', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 2.74/2.95      inference('sup-', [status(thm)], ['68', '69'])).
% 2.74/2.95  thf('71', plain,
% 2.74/2.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.74/2.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.74/2.95  thf('72', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 2.74/2.95      inference('demod', [status(thm)], ['70', '71'])).
% 2.74/2.95  thf('73', plain,
% 2.74/2.95      (![X20 : $i, X21 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 2.74/2.95           = (X20))),
% 2.74/2.95      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.74/2.95  thf('74', plain,
% 2.74/2.95      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_D)) = (sk_B))),
% 2.74/2.95      inference('sup+', [status(thm)], ['72', '73'])).
% 2.74/2.95  thf('75', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.74/2.95      inference('sup+', [status(thm)], ['23', '24'])).
% 2.74/2.95  thf('76', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 2.74/2.95      inference('demod', [status(thm)], ['74', '75'])).
% 2.74/2.95  thf('77', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 2.74/2.95      inference('demod', [status(thm)], ['42', '43'])).
% 2.74/2.95  thf('78', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 2.74/2.95      inference('sup+', [status(thm)], ['76', '77'])).
% 2.74/2.95  thf('79', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 2.74/2.95      inference('sup+', [status(thm)], ['76', '77'])).
% 2.74/2.95  thf('80', plain, (((sk_D) = (k3_xboole_0 @ sk_A @ sk_D))),
% 2.74/2.95      inference('demod', [status(thm)], ['67', '78', '79'])).
% 2.74/2.95  thf('81', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.74/2.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.74/2.95  thf('82', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.74/2.95      inference('sup+', [status(thm)], ['23', '24'])).
% 2.74/2.95  thf('83', plain, (((sk_D) = (sk_A))),
% 2.74/2.95      inference('demod', [status(thm)], ['51', '80', '81', '82'])).
% 2.74/2.95  thf('84', plain,
% 2.74/2.95      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_A))),
% 2.74/2.95      inference('demod', [status(thm)], ['2', '83'])).
% 2.74/2.95  thf('85', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.74/2.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.74/2.95  thf('86', plain,
% 2.74/2.95      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 2.74/2.95      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.74/2.95  thf('87', plain,
% 2.74/2.95      (![X7 : $i, X9 : $i]:
% 2.74/2.95         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 2.74/2.95      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.74/2.95  thf('88', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.74/2.95      inference('sup-', [status(thm)], ['86', '87'])).
% 2.74/2.95  thf('89', plain,
% 2.74/2.95      (![X12 : $i, X13 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 2.74/2.95           = (k2_xboole_0 @ X12 @ X13))),
% 2.74/2.95      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.74/2.95  thf('90', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 2.74/2.95           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 2.74/2.95      inference('sup+', [status(thm)], ['88', '89'])).
% 2.74/2.95  thf('91', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.74/2.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.74/2.95  thf('92', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.74/2.95      inference('sup+', [status(thm)], ['23', '24'])).
% 2.74/2.95  thf('93', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.74/2.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.74/2.95  thf('94', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ X0 @ X1)
% 2.74/2.95           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 2.74/2.95      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 2.74/2.95  thf('95', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ X0 @ X1)
% 2.74/2.95           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.74/2.95      inference('sup+', [status(thm)], ['85', '94'])).
% 2.74/2.95  thf('96', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 2.74/2.95      inference('demod', [status(thm)], ['74', '75'])).
% 2.74/2.95  thf('97', plain,
% 2.74/2.95      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.74/2.95           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.74/2.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.74/2.95  thf('98', plain,
% 2.74/2.95      (![X0 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ sk_B @ X0)
% 2.74/2.95           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_D @ X0)))),
% 2.74/2.95      inference('sup+', [status(thm)], ['96', '97'])).
% 2.74/2.95  thf('99', plain,
% 2.74/2.95      (![X0 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_D))
% 2.74/2.95           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_D @ X0)))),
% 2.74/2.95      inference('sup+', [status(thm)], ['95', '98'])).
% 2.74/2.95  thf('100', plain,
% 2.74/2.95      (![X0 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ sk_B @ X0)
% 2.74/2.95           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_D @ X0)))),
% 2.74/2.95      inference('sup+', [status(thm)], ['96', '97'])).
% 2.74/2.95  thf('101', plain,
% 2.74/2.95      (![X0 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_D))
% 2.74/2.95           = (k4_xboole_0 @ sk_B @ X0))),
% 2.74/2.95      inference('demod', [status(thm)], ['99', '100'])).
% 2.74/2.95  thf('102', plain, (((sk_D) = (sk_A))),
% 2.74/2.95      inference('demod', [status(thm)], ['51', '80', '81', '82'])).
% 2.74/2.95  thf('103', plain,
% 2.74/2.95      (![X0 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_A))
% 2.74/2.95           = (k4_xboole_0 @ sk_B @ X0))),
% 2.74/2.95      inference('demod', [status(thm)], ['101', '102'])).
% 2.74/2.95  thf('104', plain,
% 2.74/2.95      (((k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ sk_A))
% 2.74/2.95         = (k4_xboole_0 @ sk_B @ sk_C))),
% 2.74/2.95      inference('sup+', [status(thm)], ['84', '103'])).
% 2.74/2.95  thf('105', plain,
% 2.74/2.95      (![X0 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_A))
% 2.74/2.95           = (k4_xboole_0 @ sk_B @ X0))),
% 2.74/2.95      inference('demod', [status(thm)], ['101', '102'])).
% 2.74/2.95  thf('106', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.74/2.95      inference('sup-', [status(thm)], ['6', '7'])).
% 2.74/2.95  thf('107', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_C))),
% 2.74/2.95      inference('demod', [status(thm)], ['104', '105', '106'])).
% 2.74/2.95  thf('108', plain,
% 2.74/2.95      (![X12 : $i, X13 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 2.74/2.95           = (k2_xboole_0 @ X12 @ X13))),
% 2.74/2.95      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.74/2.95  thf('109', plain,
% 2.74/2.95      (((k2_xboole_0 @ sk_C @ k1_xboole_0) = (k2_xboole_0 @ sk_C @ sk_B))),
% 2.74/2.95      inference('sup+', [status(thm)], ['107', '108'])).
% 2.74/2.95  thf('110', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.74/2.95      inference('cnf', [status(esa)], [t1_boole])).
% 2.74/2.95  thf('111', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.74/2.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.74/2.95  thf('112', plain,
% 2.74/2.95      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 2.74/2.95      inference('demod', [status(thm)], ['0', '1'])).
% 2.74/2.95  thf('113', plain,
% 2.74/2.95      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 2.74/2.95      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.74/2.95  thf('114', plain, ((r1_tarski @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A))),
% 2.74/2.95      inference('sup+', [status(thm)], ['112', '113'])).
% 2.74/2.95  thf('115', plain,
% 2.74/2.95      (![X7 : $i, X9 : $i]:
% 2.74/2.95         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 2.74/2.95      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.74/2.95  thf('116', plain,
% 2.74/2.95      (((k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 2.74/2.95      inference('sup-', [status(thm)], ['114', '115'])).
% 2.74/2.95  thf('117', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 2.74/2.95           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 2.74/2.95      inference('sup+', [status(thm)], ['27', '28'])).
% 2.74/2.95  thf('118', plain,
% 2.74/2.95      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 2.74/2.95         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B)))),
% 2.74/2.95      inference('sup+', [status(thm)], ['116', '117'])).
% 2.74/2.95  thf('119', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.74/2.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.74/2.95  thf('120', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.74/2.95      inference('sup+', [status(thm)], ['23', '24'])).
% 2.74/2.95  thf('121', plain,
% 2.74/2.95      (((sk_A) = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B)))),
% 2.74/2.95      inference('demod', [status(thm)], ['118', '119', '120'])).
% 2.74/2.95  thf('122', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 2.74/2.95      inference('demod', [status(thm)], ['22', '25'])).
% 2.74/2.95  thf('123', plain,
% 2.74/2.95      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.74/2.95           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.74/2.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.74/2.95  thf('124', plain,
% 2.74/2.95      (![X0 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ sk_C @ X0)
% 2.74/2.95           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)))),
% 2.74/2.95      inference('sup+', [status(thm)], ['122', '123'])).
% 2.74/2.95  thf('125', plain,
% 2.74/2.95      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_B))
% 2.74/2.95         = (k4_xboole_0 @ sk_C @ sk_A))),
% 2.74/2.95      inference('sup+', [status(thm)], ['121', '124'])).
% 2.74/2.95  thf('126', plain,
% 2.74/2.95      (![X18 : $i, X19 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.74/2.95           = (k3_xboole_0 @ X18 @ X19))),
% 2.74/2.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.74/2.95  thf('127', plain,
% 2.74/2.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.74/2.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.74/2.95  thf('128', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 2.74/2.95      inference('demod', [status(thm)], ['22', '25'])).
% 2.74/2.95  thf('129', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (sk_C))),
% 2.74/2.95      inference('demod', [status(thm)], ['125', '126', '127', '128'])).
% 2.74/2.95  thf('130', plain,
% 2.74/2.95      (![X20 : $i, X21 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 2.74/2.95           = (X20))),
% 2.74/2.95      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.74/2.95  thf('131', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.74/2.95      inference('sup-', [status(thm)], ['86', '87'])).
% 2.74/2.95  thf('132', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 2.74/2.95      inference('sup+', [status(thm)], ['130', '131'])).
% 2.74/2.95  thf('133', plain,
% 2.74/2.95      (![X12 : $i, X13 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 2.74/2.95           = (k2_xboole_0 @ X12 @ X13))),
% 2.74/2.95      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.74/2.95  thf('134', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 2.74/2.95           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.74/2.95      inference('sup+', [status(thm)], ['132', '133'])).
% 2.74/2.95  thf('135', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.74/2.95      inference('cnf', [status(esa)], [t1_boole])).
% 2.74/2.95  thf('136', plain,
% 2.74/2.95      (![X0 : $i, X1 : $i]:
% 2.74/2.95         ((X1) = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.74/2.95      inference('demod', [status(thm)], ['134', '135'])).
% 2.74/2.95  thf('137', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 2.74/2.95      inference('sup+', [status(thm)], ['129', '136'])).
% 2.74/2.95  thf('138', plain, (((sk_C) = (sk_B))),
% 2.74/2.95      inference('demod', [status(thm)], ['109', '110', '111', '137'])).
% 2.74/2.95  thf('139', plain, (((sk_C) != (sk_B))),
% 2.74/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.95  thf('140', plain, ($false),
% 2.74/2.95      inference('simplify_reflect-', [status(thm)], ['138', '139'])).
% 2.74/2.95  
% 2.74/2.95  % SZS output end Refutation
% 2.74/2.95  
% 2.74/2.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
