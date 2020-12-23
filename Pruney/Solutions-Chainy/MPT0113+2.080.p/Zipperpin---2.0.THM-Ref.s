%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nd8d9m3gmh

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:39 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 719 expanded)
%              Number of leaves         :   22 ( 241 expanded)
%              Depth                    :   23
%              Number of atoms          :  755 (5842 expanded)
%              Number of equality atoms :   66 ( 615 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','11'])).

thf('13',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('25',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['13','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','34'])).

thf('36',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('40',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('45',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('47',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('52',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('56',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('58',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X3 @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('63',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ X2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('70',plain,(
    ! [X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('73',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('77',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('84',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['50','84'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('86',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('87',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['35','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nd8d9m3gmh
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:26:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.84  % Solved by: fo/fo7.sh
% 0.59/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.84  % done 848 iterations in 0.382s
% 0.59/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.84  % SZS output start Refutation
% 0.59/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.84  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.84  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.84  thf(t106_xboole_1, conjecture,
% 0.59/0.84    (![A:$i,B:$i,C:$i]:
% 0.59/0.84     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.59/0.84       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.59/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.84    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.84        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.59/0.84          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.59/0.84    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.59/0.84  thf('0', plain,
% 0.59/0.84      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('1', plain,
% 0.59/0.84      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.59/0.84      inference('split', [status(esa)], ['0'])).
% 0.59/0.84  thf(t46_xboole_1, axiom,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.59/0.84  thf('2', plain,
% 0.59/0.84      (![X16 : $i, X17 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (k1_xboole_0))),
% 0.59/0.84      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.59/0.84  thf(t52_xboole_1, axiom,
% 0.59/0.84    (![A:$i,B:$i,C:$i]:
% 0.59/0.84     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.59/0.84       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.59/0.84  thf('3', plain,
% 0.59/0.84      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.59/0.84           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 0.59/0.84              (k3_xboole_0 @ X21 @ X23)))),
% 0.59/0.84      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.59/0.84  thf('4', plain,
% 0.59/0.84      (![X16 : $i, X17 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (k1_xboole_0))),
% 0.59/0.84      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.59/0.84  thf(l32_xboole_1, axiom,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.84  thf('5', plain,
% 0.59/0.84      (![X3 : $i, X4 : $i]:
% 0.59/0.84         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.59/0.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.84  thf('6', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i]:
% 0.59/0.84         (((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.84          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.84  thf('7', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.84      inference('simplify', [status(thm)], ['6'])).
% 0.59/0.84  thf('8', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf(t1_xboole_1, axiom,
% 0.59/0.84    (![A:$i,B:$i,C:$i]:
% 0.59/0.84     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.59/0.84       ( r1_tarski @ A @ C ) ))).
% 0.59/0.84  thf('9', plain,
% 0.59/0.84      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.59/0.84         (~ (r1_tarski @ X11 @ X12)
% 0.59/0.84          | ~ (r1_tarski @ X12 @ X13)
% 0.59/0.84          | (r1_tarski @ X11 @ X13))),
% 0.59/0.84      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.59/0.84  thf('10', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         ((r1_tarski @ sk_A @ X0)
% 0.59/0.84          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.84  thf('11', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['7', '10'])).
% 0.59/0.84  thf('12', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ X0)))),
% 0.59/0.84      inference('sup+', [status(thm)], ['3', '11'])).
% 0.59/0.84  thf('13', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.59/0.84      inference('sup+', [status(thm)], ['2', '12'])).
% 0.59/0.84  thf('14', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.84      inference('simplify', [status(thm)], ['6'])).
% 0.59/0.84  thf(t28_xboole_1, axiom,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.84  thf('15', plain,
% 0.59/0.84      (![X14 : $i, X15 : $i]:
% 0.59/0.84         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.59/0.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.84  thf('16', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i]:
% 0.59/0.84         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.59/0.84      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.84  thf(t16_xboole_1, axiom,
% 0.59/0.84    (![A:$i,B:$i,C:$i]:
% 0.59/0.84     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.84       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.59/0.84  thf('17', plain,
% 0.59/0.84      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.59/0.84         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 0.59/0.84           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.59/0.84      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.59/0.84  thf(t100_xboole_1, axiom,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.84  thf('18', plain,
% 0.59/0.84      (![X6 : $i, X7 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X6 @ X7)
% 0.59/0.84           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.59/0.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.84  thf('19', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 0.59/0.84           = (k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 0.59/0.84              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.59/0.84      inference('sup+', [status(thm)], ['17', '18'])).
% 0.59/0.84  thf(t49_xboole_1, axiom,
% 0.59/0.84    (![A:$i,B:$i,C:$i]:
% 0.59/0.84     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.59/0.84       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.59/0.84  thf('20', plain,
% 0.59/0.84      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.84         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.59/0.84           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.59/0.84      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.59/0.84  thf('21', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.84         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.84           = (k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 0.59/0.84              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.59/0.84      inference('demod', [status(thm)], ['19', '20'])).
% 0.59/0.84  thf('22', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.84         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))
% 0.59/0.84           = (k5_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X2 @ X0)))),
% 0.59/0.84      inference('sup+', [status(thm)], ['16', '21'])).
% 0.59/0.84  thf('23', plain,
% 0.59/0.84      (![X16 : $i, X17 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (k1_xboole_0))),
% 0.59/0.84      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.59/0.84  thf(t92_xboole_1, axiom,
% 0.59/0.84    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.59/0.84  thf('24', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.59/0.84      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.59/0.84  thf('25', plain,
% 0.59/0.84      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.84      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.59/0.84  thf('26', plain,
% 0.59/0.84      (![X6 : $i, X7 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X6 @ X7)
% 0.59/0.84           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.59/0.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.84  thf('27', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.84      inference('sup+', [status(thm)], ['25', '26'])).
% 0.59/0.84  thf(t5_boole, axiom,
% 0.59/0.84    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.84  thf('28', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 0.59/0.84      inference('cnf', [status(esa)], [t5_boole])).
% 0.59/0.84  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.59/0.84  thf('30', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.59/0.84      inference('demod', [status(thm)], ['13', '29'])).
% 0.59/0.84  thf('31', plain,
% 0.59/0.84      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.59/0.84      inference('split', [status(esa)], ['0'])).
% 0.59/0.84  thf('32', plain, (((r1_tarski @ sk_A @ sk_B))),
% 0.59/0.84      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.84  thf('33', plain,
% 0.59/0.84      (~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_tarski @ sk_A @ sk_B))),
% 0.59/0.84      inference('split', [status(esa)], ['0'])).
% 0.59/0.84  thf('34', plain, (~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.84      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 0.59/0.84  thf('35', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.59/0.84      inference('simpl_trail', [status(thm)], ['1', '34'])).
% 0.59/0.84  thf('36', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('37', plain,
% 0.59/0.84      (![X3 : $i, X5 : $i]:
% 0.59/0.84         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.59/0.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.84  thf('38', plain,
% 0.59/0.84      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['36', '37'])).
% 0.59/0.84  thf('39', plain,
% 0.59/0.84      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['36', '37'])).
% 0.59/0.84  thf('40', plain,
% 0.59/0.84      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.59/0.84           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 0.59/0.84              (k3_xboole_0 @ X21 @ X23)))),
% 0.59/0.84      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.59/0.84  thf('41', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.84      inference('simplify', [status(thm)], ['6'])).
% 0.59/0.84  thf('42', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.84         (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ 
% 0.59/0.84          (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.59/0.84      inference('sup+', [status(thm)], ['40', '41'])).
% 0.59/0.84  thf('43', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.59/0.84      inference('sup+', [status(thm)], ['39', '42'])).
% 0.59/0.84  thf('44', plain,
% 0.59/0.84      (![X14 : $i, X15 : $i]:
% 0.59/0.84         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.59/0.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.84  thf('45', plain,
% 0.59/0.84      (((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.59/0.84         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.59/0.84      inference('sup-', [status(thm)], ['43', '44'])).
% 0.59/0.84  thf('46', plain,
% 0.59/0.84      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.84      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.59/0.84  thf('47', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.59/0.84      inference('demod', [status(thm)], ['45', '46'])).
% 0.59/0.84  thf('48', plain,
% 0.59/0.84      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.59/0.84           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 0.59/0.84              (k3_xboole_0 @ X21 @ X23)))),
% 0.59/0.84      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.59/0.84  thf('49', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.59/0.84           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.59/0.84      inference('sup+', [status(thm)], ['47', '48'])).
% 0.59/0.84  thf('50', plain,
% 0.59/0.84      (((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C))
% 0.59/0.84         = (k1_xboole_0))),
% 0.59/0.84      inference('demod', [status(thm)], ['38', '49'])).
% 0.59/0.84  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.59/0.84  thf('52', plain,
% 0.59/0.84      (![X3 : $i, X4 : $i]:
% 0.59/0.84         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.59/0.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.84  thf('53', plain,
% 0.59/0.84      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_tarski @ X0 @ k1_xboole_0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['51', '52'])).
% 0.59/0.84  thf('54', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.59/0.84      inference('simplify', [status(thm)], ['53'])).
% 0.59/0.84  thf('55', plain,
% 0.59/0.84      (![X16 : $i, X17 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (k1_xboole_0))),
% 0.59/0.84      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.59/0.84  thf('56', plain,
% 0.59/0.84      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.59/0.84           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 0.59/0.84              (k3_xboole_0 @ X21 @ X23)))),
% 0.59/0.84      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.59/0.84  thf('57', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.84      inference('simplify', [status(thm)], ['6'])).
% 0.59/0.84  thf('58', plain,
% 0.59/0.84      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.59/0.84         (~ (r1_tarski @ X11 @ X12)
% 0.59/0.84          | ~ (r1_tarski @ X12 @ X13)
% 0.59/0.84          | (r1_tarski @ X11 @ X13))),
% 0.59/0.84      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.59/0.84  thf('59', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.84         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.59/0.84      inference('sup-', [status(thm)], ['57', '58'])).
% 0.59/0.84  thf('60', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.84         (~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X3)
% 0.59/0.84          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X3))),
% 0.59/0.84      inference('sup-', [status(thm)], ['56', '59'])).
% 0.59/0.84  thf('61', plain,
% 0.59/0.84      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.59/0.84         (~ (r1_tarski @ (k4_xboole_0 @ X3 @ k1_xboole_0) @ X0)
% 0.59/0.84          | (r1_tarski @ (k4_xboole_0 @ X3 @ X2) @ X0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['55', '60'])).
% 0.59/0.84  thf('62', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.59/0.84  thf('63', plain,
% 0.59/0.84      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.59/0.84         (~ (r1_tarski @ X3 @ X0) | (r1_tarski @ (k4_xboole_0 @ X3 @ X2) @ X0))),
% 0.59/0.84      inference('demod', [status(thm)], ['61', '62'])).
% 0.59/0.84  thf('64', plain,
% 0.59/0.84      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.59/0.84      inference('sup-', [status(thm)], ['54', '63'])).
% 0.59/0.84  thf('65', plain,
% 0.59/0.84      (![X3 : $i, X5 : $i]:
% 0.59/0.84         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.59/0.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.84  thf('66', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.59/0.84           = (k1_xboole_0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['64', '65'])).
% 0.59/0.84  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.59/0.84  thf('68', plain,
% 0.59/0.84      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.84      inference('demod', [status(thm)], ['66', '67'])).
% 0.59/0.84  thf('69', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.84         (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ 
% 0.59/0.84          (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.59/0.84      inference('sup+', [status(thm)], ['40', '41'])).
% 0.59/0.84  thf('70', plain,
% 0.59/0.84      (![X1 : $i]:
% 0.59/0.84         (r1_tarski @ (k4_xboole_0 @ X1 @ k1_xboole_0) @ 
% 0.59/0.84          (k4_xboole_0 @ X1 @ k1_xboole_0))),
% 0.59/0.84      inference('sup+', [status(thm)], ['68', '69'])).
% 0.59/0.84  thf('71', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.59/0.84  thf('72', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.59/0.84  thf('73', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.59/0.84      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.59/0.84  thf('74', plain,
% 0.59/0.84      (![X3 : $i, X5 : $i]:
% 0.59/0.84         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.59/0.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.84  thf('75', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['73', '74'])).
% 0.59/0.84  thf('76', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.59/0.84      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.59/0.84  thf('77', plain,
% 0.59/0.84      (![X14 : $i, X15 : $i]:
% 0.59/0.84         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.59/0.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.84  thf('78', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['76', '77'])).
% 0.59/0.84  thf('79', plain,
% 0.59/0.84      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.59/0.84           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 0.59/0.84              (k3_xboole_0 @ X21 @ X23)))),
% 0.59/0.84      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.59/0.84  thf('80', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.84           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.59/0.84      inference('sup+', [status(thm)], ['78', '79'])).
% 0.59/0.84  thf('81', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.59/0.84           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0))),
% 0.59/0.84      inference('sup+', [status(thm)], ['75', '80'])).
% 0.59/0.84  thf('82', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.59/0.84  thf('83', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['73', '74'])).
% 0.59/0.84  thf('84', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.59/0.84      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.59/0.84  thf('85', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.59/0.84      inference('demod', [status(thm)], ['50', '84'])).
% 0.59/0.84  thf(d7_xboole_0, axiom,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.59/0.84       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.84  thf('86', plain,
% 0.59/0.84      (![X0 : $i, X2 : $i]:
% 0.59/0.84         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.59/0.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.59/0.84  thf('87', plain,
% 0.59/0.84      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.84      inference('sup-', [status(thm)], ['85', '86'])).
% 0.59/0.84  thf('88', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.59/0.84      inference('simplify', [status(thm)], ['87'])).
% 0.59/0.84  thf('89', plain, ($false), inference('demod', [status(thm)], ['35', '88'])).
% 0.59/0.84  
% 0.59/0.84  % SZS output end Refutation
% 0.59/0.84  
% 0.70/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
