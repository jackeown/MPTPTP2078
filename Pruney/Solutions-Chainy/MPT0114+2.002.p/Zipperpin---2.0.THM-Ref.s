%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uCPm0hZqOy

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:42 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  165 (1160 expanded)
%              Number of leaves         :   27 ( 387 expanded)
%              Depth                    :   22
%              Number of atoms          : 1340 (8839 expanded)
%              Number of equality atoms :  106 ( 865 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t107_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
      <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t107_xboole_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_xboole_0 @ X31 @ X32 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X31 @ X32 ) @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('3',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_xboole_0 @ X31 @ X32 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X31 @ X32 ) @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('11',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X29 @ X30 ) @ X30 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','9','18'])).

thf('20',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['20'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
        = ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('40',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('68',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('70',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','71'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ X33 @ X34 )
      = ( k5_xboole_0 @ X33 @ ( k4_xboole_0 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
        = sk_A )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','76'])).

thf('78',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = sk_A )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['19','77'])).

thf('79',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','71'])).

thf('81',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['79','83'])).

thf('85',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['78','84'])).

thf('86',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('89',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['20'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('92',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ~ ( r1_xboole_0 @ X27 @ X28 )
      | ( r1_xboole_0 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_A @ X0 )
        | ~ ( r1_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,(
    ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['87','96','97'])).

thf('99',plain,(
    ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','9','18'])).

thf('101',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['101'])).

thf('103',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('104',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) )
        = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','68','69'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ X0 )
        = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['101'])).

thf('112',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['87','96','97','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['110','112'])).

thf('114',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['100','113'])).

thf('115',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('116',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X29 @ X30 ) @ X30 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('117',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['20'])).

thf('120',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ~ ( r1_xboole_0 @ X27 @ X28 )
      | ( r1_xboole_0 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('121',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_A @ X0 )
        | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
        = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('126',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
        = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('128',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
        = sk_A )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = sk_A )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['115','128'])).

thf('130',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['20'])).

thf('131',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['87','96','97','130'])).

thf('132',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference(simpl_trail,[status(thm)],['129','131'])).

thf('133',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['114','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['79','83'])).

thf('135',plain,(
    r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    $false ),
    inference(demod,[status(thm)],['99','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uCPm0hZqOy
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:43:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.30/1.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.30/1.50  % Solved by: fo/fo7.sh
% 1.30/1.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.30/1.50  % done 2888 iterations in 1.033s
% 1.30/1.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.30/1.50  % SZS output start Refutation
% 1.30/1.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.30/1.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.30/1.50  thf(sk_A_type, type, sk_A: $i).
% 1.30/1.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.30/1.50  thf(sk_C_type, type, sk_C: $i).
% 1.30/1.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.30/1.50  thf(sk_B_type, type, sk_B: $i).
% 1.30/1.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.30/1.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.30/1.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.30/1.50  thf(t107_xboole_1, conjecture,
% 1.30/1.50    (![A:$i,B:$i,C:$i]:
% 1.30/1.50     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.30/1.50       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 1.30/1.50         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 1.30/1.50  thf(zf_stmt_0, negated_conjecture,
% 1.30/1.50    (~( ![A:$i,B:$i,C:$i]:
% 1.30/1.50        ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.30/1.50          ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 1.30/1.50            ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 1.30/1.50    inference('cnf.neg', [status(esa)], [t107_xboole_1])).
% 1.30/1.50  thf('0', plain,
% 1.30/1.50      ((~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 1.30/1.50        | ~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 1.30/1.50        | ~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.50  thf('1', plain,
% 1.30/1.50      ((~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 1.30/1.50         <= (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('split', [status(esa)], ['0'])).
% 1.30/1.50  thf(t94_xboole_1, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( k2_xboole_0 @ A @ B ) =
% 1.30/1.50       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.30/1.50  thf('2', plain,
% 1.30/1.50      (![X31 : $i, X32 : $i]:
% 1.30/1.50         ((k2_xboole_0 @ X31 @ X32)
% 1.30/1.50           = (k5_xboole_0 @ (k5_xboole_0 @ X31 @ X32) @ 
% 1.30/1.50              (k3_xboole_0 @ X31 @ X32)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.30/1.50  thf('3', plain,
% 1.30/1.50      (![X31 : $i, X32 : $i]:
% 1.30/1.50         ((k2_xboole_0 @ X31 @ X32)
% 1.30/1.50           = (k5_xboole_0 @ (k5_xboole_0 @ X31 @ X32) @ 
% 1.30/1.50              (k3_xboole_0 @ X31 @ X32)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.30/1.50  thf('4', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.30/1.50           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.30/1.50              (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 1.30/1.50      inference('sup+', [status(thm)], ['2', '3'])).
% 1.30/1.50  thf(l97_xboole_1, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 1.30/1.50  thf('5', plain,
% 1.30/1.50      (![X14 : $i, X15 : $i]:
% 1.30/1.50         (r1_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k5_xboole_0 @ X14 @ X15))),
% 1.30/1.50      inference('cnf', [status(esa)], [l97_xboole_1])).
% 1.30/1.50  thf(d7_xboole_0, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.30/1.50       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.30/1.50  thf('6', plain,
% 1.30/1.50      (![X6 : $i, X7 : $i]:
% 1.30/1.50         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 1.30/1.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.30/1.50  thf('7', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.30/1.50           = (k1_xboole_0))),
% 1.30/1.50      inference('sup-', [status(thm)], ['5', '6'])).
% 1.30/1.50  thf(commutativity_k3_xboole_0, axiom,
% 1.30/1.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.30/1.50  thf('8', plain,
% 1.30/1.50      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.30/1.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.30/1.50  thf('9', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.30/1.50           = (k1_xboole_0))),
% 1.30/1.50      inference('demod', [status(thm)], ['7', '8'])).
% 1.30/1.50  thf(t3_boole, axiom,
% 1.30/1.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.30/1.50  thf('10', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.30/1.50      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.50  thf(t79_xboole_1, axiom,
% 1.30/1.50    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.30/1.50  thf('11', plain,
% 1.30/1.50      (![X29 : $i, X30 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X29 @ X30) @ X30)),
% 1.30/1.50      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.30/1.50  thf('12', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.30/1.50      inference('sup+', [status(thm)], ['10', '11'])).
% 1.30/1.50  thf('13', plain,
% 1.30/1.50      (![X6 : $i, X7 : $i]:
% 1.30/1.50         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 1.30/1.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.30/1.50  thf('14', plain,
% 1.30/1.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.30/1.50      inference('sup-', [status(thm)], ['12', '13'])).
% 1.30/1.50  thf(t100_xboole_1, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.30/1.50  thf('15', plain,
% 1.30/1.50      (![X16 : $i, X17 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ X16 @ X17)
% 1.30/1.50           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.30/1.50  thf('16', plain,
% 1.30/1.50      (![X0 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.30/1.50      inference('sup+', [status(thm)], ['14', '15'])).
% 1.30/1.50  thf('17', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.30/1.50      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.50  thf('18', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.30/1.50      inference('sup+', [status(thm)], ['16', '17'])).
% 1.30/1.50  thf('19', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.30/1.50           = (k2_xboole_0 @ X1 @ X0))),
% 1.30/1.50      inference('demod', [status(thm)], ['4', '9', '18'])).
% 1.30/1.50  thf('20', plain,
% 1.30/1.50      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 1.30/1.50        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.50  thf('21', plain,
% 1.30/1.50      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('split', [status(esa)], ['20'])).
% 1.30/1.50  thf(l32_xboole_1, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.30/1.50  thf('22', plain,
% 1.30/1.50      (![X11 : $i, X13 : $i]:
% 1.30/1.50         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 1.30/1.50          | ~ (r1_tarski @ X11 @ X13))),
% 1.30/1.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.30/1.50  thf('23', plain,
% 1.30/1.50      ((((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('sup-', [status(thm)], ['21', '22'])).
% 1.30/1.50  thf(t48_xboole_1, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.30/1.50  thf('24', plain,
% 1.30/1.50      (![X24 : $i, X25 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.30/1.50           = (k3_xboole_0 @ X24 @ X25))),
% 1.30/1.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.50  thf('25', plain,
% 1.30/1.50      ((((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 1.30/1.50          = (k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('sup+', [status(thm)], ['23', '24'])).
% 1.30/1.50  thf('26', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.30/1.50      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.50  thf('27', plain,
% 1.30/1.50      ((((sk_A) = (k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('demod', [status(thm)], ['25', '26'])).
% 1.30/1.50  thf(t23_xboole_1, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i]:
% 1.30/1.50     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.30/1.50       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.30/1.50  thf('28', plain,
% 1.30/1.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.30/1.50         ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 1.30/1.50           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 1.30/1.50              (k3_xboole_0 @ X18 @ X20)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.30/1.50  thf('29', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          ((k3_xboole_0 @ sk_A @ 
% 1.30/1.50            (k2_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_C) @ X0))
% 1.30/1.50            = (k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ X0))))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('sup+', [status(thm)], ['27', '28'])).
% 1.30/1.50  thf(t47_xboole_1, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.30/1.50  thf('30', plain,
% 1.30/1.50      (![X22 : $i, X23 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 1.30/1.50           = (k4_xboole_0 @ X22 @ X23))),
% 1.30/1.50      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.30/1.50  thf('31', plain,
% 1.30/1.50      (![X24 : $i, X25 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.30/1.50           = (k3_xboole_0 @ X24 @ X25))),
% 1.30/1.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.50  thf('32', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.30/1.50           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.30/1.50      inference('sup+', [status(thm)], ['30', '31'])).
% 1.30/1.50  thf('33', plain,
% 1.30/1.50      (![X24 : $i, X25 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.30/1.50           = (k3_xboole_0 @ X24 @ X25))),
% 1.30/1.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.50  thf('34', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k3_xboole_0 @ X1 @ X0)
% 1.30/1.50           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.30/1.50      inference('demod', [status(thm)], ['32', '33'])).
% 1.30/1.50  thf('35', plain,
% 1.30/1.50      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.30/1.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.30/1.50  thf('36', plain,
% 1.30/1.50      (![X16 : $i, X17 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ X16 @ X17)
% 1.30/1.50           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.30/1.50  thf('37', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ X0 @ X1)
% 1.30/1.50           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.30/1.50      inference('sup+', [status(thm)], ['35', '36'])).
% 1.30/1.50  thf('38', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 1.30/1.50           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.30/1.50      inference('sup+', [status(thm)], ['34', '37'])).
% 1.30/1.50  thf('39', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.30/1.50      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.50  thf('40', plain,
% 1.30/1.50      (![X24 : $i, X25 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.30/1.50           = (k3_xboole_0 @ X24 @ X25))),
% 1.30/1.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.50  thf('41', plain,
% 1.30/1.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.30/1.50      inference('sup+', [status(thm)], ['39', '40'])).
% 1.30/1.50  thf('42', plain,
% 1.30/1.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.30/1.50      inference('sup-', [status(thm)], ['12', '13'])).
% 1.30/1.50  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.30/1.50      inference('demod', [status(thm)], ['41', '42'])).
% 1.30/1.50  thf(d6_xboole_0, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( k5_xboole_0 @ A @ B ) =
% 1.30/1.50       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.30/1.50  thf('44', plain,
% 1.30/1.50      (![X4 : $i, X5 : $i]:
% 1.30/1.50         ((k5_xboole_0 @ X4 @ X5)
% 1.30/1.50           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 1.30/1.50      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.30/1.50  thf('45', plain,
% 1.30/1.50      (![X0 : $i]:
% 1.30/1.50         ((k5_xboole_0 @ X0 @ X0)
% 1.30/1.50           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.30/1.50      inference('sup+', [status(thm)], ['43', '44'])).
% 1.30/1.50  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.30/1.50      inference('demod', [status(thm)], ['41', '42'])).
% 1.30/1.50  thf('47', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.30/1.50      inference('sup+', [status(thm)], ['10', '11'])).
% 1.30/1.50  thf(symmetry_r1_xboole_0, axiom,
% 1.30/1.50    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.30/1.50  thf('48', plain,
% 1.30/1.50      (![X9 : $i, X10 : $i]:
% 1.30/1.50         ((r1_xboole_0 @ X9 @ X10) | ~ (r1_xboole_0 @ X10 @ X9))),
% 1.30/1.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.30/1.50  thf('49', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.30/1.50      inference('sup-', [status(thm)], ['47', '48'])).
% 1.30/1.50  thf('50', plain,
% 1.30/1.50      (![X6 : $i, X7 : $i]:
% 1.30/1.50         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 1.30/1.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.30/1.50  thf('51', plain,
% 1.30/1.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.30/1.50      inference('sup-', [status(thm)], ['49', '50'])).
% 1.30/1.50  thf('52', plain,
% 1.30/1.50      (![X22 : $i, X23 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 1.30/1.50           = (k4_xboole_0 @ X22 @ X23))),
% 1.30/1.50      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.30/1.50  thf('53', plain,
% 1.30/1.50      (![X0 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 1.30/1.50           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.30/1.50      inference('sup+', [status(thm)], ['51', '52'])).
% 1.30/1.50  thf('54', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.30/1.50      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.50  thf('55', plain,
% 1.30/1.50      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.30/1.50      inference('demod', [status(thm)], ['53', '54'])).
% 1.30/1.50  thf('56', plain,
% 1.30/1.50      (![X4 : $i, X5 : $i]:
% 1.30/1.50         ((k5_xboole_0 @ X4 @ X5)
% 1.30/1.50           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 1.30/1.50      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.30/1.50  thf('57', plain,
% 1.30/1.50      (![X0 : $i]:
% 1.30/1.50         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.30/1.50           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.30/1.50      inference('sup+', [status(thm)], ['55', '56'])).
% 1.30/1.50  thf('58', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.30/1.50      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.50  thf('59', plain,
% 1.30/1.50      (![X4 : $i, X5 : $i]:
% 1.30/1.50         ((k5_xboole_0 @ X4 @ X5)
% 1.30/1.50           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 1.30/1.50      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.30/1.50  thf('60', plain,
% 1.30/1.50      (![X0 : $i]:
% 1.30/1.50         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.30/1.50           = (k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ X0))),
% 1.30/1.50      inference('sup+', [status(thm)], ['58', '59'])).
% 1.30/1.50  thf(commutativity_k2_xboole_0, axiom,
% 1.30/1.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.30/1.50  thf('61', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.30/1.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.30/1.50  thf('62', plain,
% 1.30/1.50      (![X0 : $i]:
% 1.30/1.50         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.30/1.50           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.30/1.50      inference('demod', [status(thm)], ['60', '61'])).
% 1.30/1.50  thf('63', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.30/1.50      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.50  thf('64', plain,
% 1.30/1.50      (![X4 : $i, X5 : $i]:
% 1.30/1.50         ((k5_xboole_0 @ X4 @ X5)
% 1.30/1.50           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 1.30/1.50      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.30/1.50  thf('65', plain,
% 1.30/1.50      (![X0 : $i]:
% 1.30/1.50         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 1.30/1.50           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.30/1.50      inference('sup+', [status(thm)], ['63', '64'])).
% 1.30/1.50  thf('66', plain,
% 1.30/1.50      (![X0 : $i]:
% 1.30/1.50         ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 1.30/1.50      inference('sup+', [status(thm)], ['62', '65'])).
% 1.30/1.50  thf('67', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.30/1.50      inference('sup+', [status(thm)], ['16', '17'])).
% 1.30/1.50  thf('68', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 1.30/1.50      inference('demod', [status(thm)], ['66', '67'])).
% 1.30/1.50  thf('69', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.30/1.50      inference('cnf', [status(esa)], [t3_boole])).
% 1.30/1.50  thf('70', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.30/1.50      inference('demod', [status(thm)], ['57', '68', '69'])).
% 1.30/1.50  thf('71', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.30/1.50      inference('demod', [status(thm)], ['45', '46', '70'])).
% 1.30/1.50  thf('72', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.30/1.50      inference('demod', [status(thm)], ['38', '71'])).
% 1.30/1.50  thf(t98_xboole_1, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.30/1.50  thf('73', plain,
% 1.30/1.50      (![X33 : $i, X34 : $i]:
% 1.30/1.50         ((k2_xboole_0 @ X33 @ X34)
% 1.30/1.50           = (k5_xboole_0 @ X33 @ (k4_xboole_0 @ X34 @ X33)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.30/1.50  thf('74', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.30/1.50           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.30/1.50      inference('sup+', [status(thm)], ['72', '73'])).
% 1.30/1.50  thf('75', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.30/1.50      inference('sup+', [status(thm)], ['16', '17'])).
% 1.30/1.50  thf('76', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 1.30/1.50      inference('demod', [status(thm)], ['74', '75'])).
% 1.30/1.50  thf('77', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          ((k3_xboole_0 @ sk_A @ 
% 1.30/1.50            (k2_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_C) @ X0)) = (sk_A)))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('demod', [status(thm)], ['29', '76'])).
% 1.30/1.50  thf('78', plain,
% 1.30/1.50      ((((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (sk_A)))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('sup+', [status(thm)], ['19', '77'])).
% 1.30/1.50  thf('79', plain,
% 1.30/1.50      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.30/1.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.30/1.50  thf('80', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.30/1.50      inference('demod', [status(thm)], ['38', '71'])).
% 1.30/1.50  thf('81', plain,
% 1.30/1.50      (![X11 : $i, X12 : $i]:
% 1.30/1.50         ((r1_tarski @ X11 @ X12)
% 1.30/1.50          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 1.30/1.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.30/1.50  thf('82', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         (((k1_xboole_0) != (k1_xboole_0))
% 1.30/1.50          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 1.30/1.50      inference('sup-', [status(thm)], ['80', '81'])).
% 1.30/1.50  thf('83', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.30/1.50      inference('simplify', [status(thm)], ['82'])).
% 1.30/1.50  thf('84', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.30/1.50      inference('sup+', [status(thm)], ['79', '83'])).
% 1.30/1.50  thf('85', plain,
% 1.30/1.50      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('sup+', [status(thm)], ['78', '84'])).
% 1.30/1.50  thf('86', plain,
% 1.30/1.50      ((~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 1.30/1.50         <= (~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('split', [status(esa)], ['0'])).
% 1.30/1.50  thf('87', plain,
% 1.30/1.50      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 1.30/1.50       ~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['85', '86'])).
% 1.30/1.50  thf('88', plain,
% 1.30/1.50      (![X14 : $i, X15 : $i]:
% 1.30/1.50         (r1_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k5_xboole_0 @ X14 @ X15))),
% 1.30/1.50      inference('cnf', [status(esa)], [l97_xboole_1])).
% 1.30/1.50  thf('89', plain,
% 1.30/1.50      (![X9 : $i, X10 : $i]:
% 1.30/1.50         ((r1_xboole_0 @ X9 @ X10) | ~ (r1_xboole_0 @ X10 @ X9))),
% 1.30/1.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.30/1.50  thf('90', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         (r1_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))),
% 1.30/1.50      inference('sup-', [status(thm)], ['88', '89'])).
% 1.30/1.50  thf('91', plain,
% 1.30/1.50      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('split', [status(esa)], ['20'])).
% 1.30/1.50  thf(t63_xboole_1, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i]:
% 1.30/1.50     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.30/1.50       ( r1_xboole_0 @ A @ C ) ))).
% 1.30/1.50  thf('92', plain,
% 1.30/1.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.30/1.50         (~ (r1_tarski @ X26 @ X27)
% 1.30/1.50          | ~ (r1_xboole_0 @ X27 @ X28)
% 1.30/1.50          | (r1_xboole_0 @ X26 @ X28))),
% 1.30/1.50      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.30/1.50  thf('93', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          ((r1_xboole_0 @ sk_A @ X0)
% 1.30/1.50           | ~ (r1_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_C) @ X0)))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('sup-', [status(thm)], ['91', '92'])).
% 1.30/1.50  thf('94', plain,
% 1.30/1.50      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('sup-', [status(thm)], ['90', '93'])).
% 1.30/1.50  thf('95', plain,
% 1.30/1.50      ((~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 1.30/1.50         <= (~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('split', [status(esa)], ['0'])).
% 1.30/1.50  thf('96', plain,
% 1.30/1.50      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))) | 
% 1.30/1.50       ~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['94', '95'])).
% 1.30/1.50  thf('97', plain,
% 1.30/1.50      (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 1.30/1.50       ~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 1.30/1.50       ~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 1.30/1.50      inference('split', [status(esa)], ['0'])).
% 1.30/1.50  thf('98', plain, (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.30/1.50      inference('sat_resolution*', [status(thm)], ['87', '96', '97'])).
% 1.30/1.50  thf('99', plain, (~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))),
% 1.30/1.50      inference('simpl_trail', [status(thm)], ['1', '98'])).
% 1.30/1.50  thf('100', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.30/1.50           = (k2_xboole_0 @ X1 @ X0))),
% 1.30/1.50      inference('demod', [status(thm)], ['4', '9', '18'])).
% 1.30/1.50  thf('101', plain,
% 1.30/1.50      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 1.30/1.50        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.50  thf('102', plain,
% 1.30/1.50      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 1.30/1.50         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('split', [status(esa)], ['101'])).
% 1.30/1.50  thf('103', plain,
% 1.30/1.50      (![X6 : $i, X7 : $i]:
% 1.30/1.50         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 1.30/1.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.30/1.50  thf('104', plain,
% 1.30/1.50      ((((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 1.30/1.50         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('sup-', [status(thm)], ['102', '103'])).
% 1.30/1.50  thf('105', plain,
% 1.30/1.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.30/1.50         ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 1.30/1.50           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 1.30/1.50              (k3_xboole_0 @ X18 @ X20)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.30/1.50  thf('106', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.30/1.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.30/1.50  thf('107', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.50         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 1.30/1.50           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.30/1.50      inference('sup+', [status(thm)], ['105', '106'])).
% 1.30/1.50  thf('108', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          ((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0))
% 1.30/1.50            = (k3_xboole_0 @ sk_A @ 
% 1.30/1.50               (k2_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_C)))))
% 1.30/1.50         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('sup+', [status(thm)], ['104', '107'])).
% 1.30/1.50  thf('109', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.30/1.50      inference('demod', [status(thm)], ['57', '68', '69'])).
% 1.30/1.50  thf('110', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          ((k3_xboole_0 @ sk_A @ X0)
% 1.30/1.50            = (k3_xboole_0 @ sk_A @ 
% 1.30/1.50               (k2_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_C)))))
% 1.30/1.50         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('demod', [status(thm)], ['108', '109'])).
% 1.30/1.50  thf('111', plain,
% 1.30/1.50      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))) | 
% 1.30/1.50       ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.30/1.50      inference('split', [status(esa)], ['101'])).
% 1.30/1.50  thf('112', plain, (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 1.30/1.50      inference('sat_resolution*', [status(thm)], ['87', '96', '97', '111'])).
% 1.30/1.50  thf('113', plain,
% 1.30/1.50      (![X0 : $i]:
% 1.30/1.50         ((k3_xboole_0 @ sk_A @ X0)
% 1.30/1.50           = (k3_xboole_0 @ sk_A @ 
% 1.30/1.50              (k2_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('simpl_trail', [status(thm)], ['110', '112'])).
% 1.30/1.50  thf('114', plain,
% 1.30/1.50      (((k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))
% 1.30/1.50         = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.30/1.50      inference('sup+', [status(thm)], ['100', '113'])).
% 1.30/1.50  thf('115', plain,
% 1.30/1.50      (![X24 : $i, X25 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.30/1.50           = (k3_xboole_0 @ X24 @ X25))),
% 1.30/1.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.30/1.50  thf('116', plain,
% 1.30/1.50      (![X29 : $i, X30 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X29 @ X30) @ X30)),
% 1.30/1.50      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.30/1.50  thf('117', plain,
% 1.30/1.50      (![X9 : $i, X10 : $i]:
% 1.30/1.50         ((r1_xboole_0 @ X9 @ X10) | ~ (r1_xboole_0 @ X10 @ X9))),
% 1.30/1.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.30/1.50  thf('118', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.30/1.50      inference('sup-', [status(thm)], ['116', '117'])).
% 1.30/1.50  thf('119', plain,
% 1.30/1.50      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('split', [status(esa)], ['20'])).
% 1.30/1.50  thf('120', plain,
% 1.30/1.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.30/1.50         (~ (r1_tarski @ X26 @ X27)
% 1.30/1.50          | ~ (r1_xboole_0 @ X27 @ X28)
% 1.30/1.50          | (r1_xboole_0 @ X26 @ X28))),
% 1.30/1.50      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.30/1.50  thf('121', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          ((r1_xboole_0 @ sk_A @ X0)
% 1.30/1.50           | ~ (r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ X0)))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('sup-', [status(thm)], ['119', '120'])).
% 1.30/1.50  thf('122', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          (r1_xboole_0 @ sk_A @ 
% 1.30/1.50           (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('sup-', [status(thm)], ['118', '121'])).
% 1.30/1.50  thf('123', plain,
% 1.30/1.50      (![X6 : $i, X7 : $i]:
% 1.30/1.50         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 1.30/1.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.30/1.50  thf('124', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          ((k3_xboole_0 @ sk_A @ 
% 1.30/1.50            (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))) = (k1_xboole_0)))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('sup-', [status(thm)], ['122', '123'])).
% 1.30/1.50  thf('125', plain,
% 1.30/1.50      (![X16 : $i, X17 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ X16 @ X17)
% 1.30/1.50           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.30/1.50  thf('126', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          ((k4_xboole_0 @ sk_A @ 
% 1.30/1.50            (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C)))
% 1.30/1.50            = (k5_xboole_0 @ sk_A @ k1_xboole_0)))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('sup+', [status(thm)], ['124', '125'])).
% 1.30/1.50  thf('127', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.30/1.50      inference('sup+', [status(thm)], ['16', '17'])).
% 1.30/1.50  thf('128', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          ((k4_xboole_0 @ sk_A @ 
% 1.30/1.50            (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))) = (sk_A)))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('demod', [status(thm)], ['126', '127'])).
% 1.30/1.50  thf('129', plain,
% 1.30/1.50      ((((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (sk_A)))
% 1.30/1.50         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.30/1.50      inference('sup+', [status(thm)], ['115', '128'])).
% 1.30/1.50  thf('130', plain,
% 1.30/1.50      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 1.30/1.50       ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.30/1.50      inference('split', [status(esa)], ['20'])).
% 1.30/1.50  thf('131', plain, (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.30/1.50      inference('sat_resolution*', [status(thm)], ['87', '96', '97', '130'])).
% 1.30/1.50  thf('132', plain,
% 1.30/1.50      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 1.30/1.50      inference('simpl_trail', [status(thm)], ['129', '131'])).
% 1.30/1.50  thf('133', plain,
% 1.30/1.50      (((k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 1.30/1.50      inference('demod', [status(thm)], ['114', '132'])).
% 1.30/1.50  thf('134', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.30/1.50      inference('sup+', [status(thm)], ['79', '83'])).
% 1.30/1.50  thf('135', plain, ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))),
% 1.30/1.50      inference('sup+', [status(thm)], ['133', '134'])).
% 1.30/1.50  thf('136', plain, ($false), inference('demod', [status(thm)], ['99', '135'])).
% 1.30/1.50  
% 1.30/1.50  % SZS output end Refutation
% 1.30/1.50  
% 1.34/1.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
