%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kvZfy9AGNF

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:39 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 181 expanded)
%              Number of leaves         :   22 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  609 (1314 expanded)
%              Number of equality atoms :   63 ( 115 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('18',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','22'])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['14','15'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X20 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('37',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['31','41'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['24','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('45',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('62',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['43','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['23','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kvZfy9AGNF
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.67/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.85  % Solved by: fo/fo7.sh
% 0.67/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.85  % done 893 iterations in 0.396s
% 0.67/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.85  % SZS output start Refutation
% 0.67/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.85  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.67/0.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.85  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.67/0.85  thf(t106_xboole_1, conjecture,
% 0.67/0.85    (![A:$i,B:$i,C:$i]:
% 0.67/0.85     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.67/0.85       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.67/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.85    (~( ![A:$i,B:$i,C:$i]:
% 0.67/0.85        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.67/0.85          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.67/0.85    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.67/0.85  thf('0', plain,
% 0.67/0.85      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('1', plain,
% 0.67/0.85      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.67/0.85      inference('split', [status(esa)], ['0'])).
% 0.67/0.85  thf(t79_xboole_1, axiom,
% 0.67/0.85    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.67/0.85  thf('2', plain,
% 0.67/0.85      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 0.67/0.85      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.67/0.85  thf(d7_xboole_0, axiom,
% 0.67/0.85    (![A:$i,B:$i]:
% 0.67/0.85     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.67/0.85       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.67/0.85  thf('3', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.67/0.85      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.67/0.85  thf('4', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.67/0.85      inference('sup-', [status(thm)], ['2', '3'])).
% 0.67/0.85  thf(t100_xboole_1, axiom,
% 0.67/0.85    (![A:$i,B:$i]:
% 0.67/0.85     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.67/0.85  thf('5', plain,
% 0.67/0.85      (![X6 : $i, X7 : $i]:
% 0.67/0.85         ((k4_xboole_0 @ X6 @ X7)
% 0.67/0.85           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.67/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.67/0.85  thf('6', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.67/0.85           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.67/0.85      inference('sup+', [status(thm)], ['4', '5'])).
% 0.67/0.85  thf(t5_boole, axiom,
% 0.67/0.85    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.67/0.85  thf('7', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 0.67/0.85      inference('cnf', [status(esa)], [t5_boole])).
% 0.67/0.85  thf('8', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.67/0.85           = (k4_xboole_0 @ X1 @ X0))),
% 0.67/0.85      inference('demod', [status(thm)], ['6', '7'])).
% 0.67/0.85  thf('9', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf(t28_xboole_1, axiom,
% 0.67/0.85    (![A:$i,B:$i]:
% 0.67/0.85     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.67/0.85  thf('10', plain,
% 0.67/0.85      (![X13 : $i, X14 : $i]:
% 0.67/0.85         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.67/0.85      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.67/0.85  thf('11', plain,
% 0.67/0.85      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.67/0.85      inference('sup-', [status(thm)], ['9', '10'])).
% 0.67/0.85  thf(t49_xboole_1, axiom,
% 0.67/0.85    (![A:$i,B:$i,C:$i]:
% 0.67/0.85     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.67/0.85       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.67/0.85  thf('12', plain,
% 0.67/0.85      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.67/0.85           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.67/0.85      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.67/0.85  thf('13', plain,
% 0.67/0.85      (![X0 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ sk_A @ 
% 0.67/0.85           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.67/0.85           = (k4_xboole_0 @ sk_A @ X0))),
% 0.67/0.85      inference('sup+', [status(thm)], ['11', '12'])).
% 0.67/0.85  thf('14', plain,
% 0.67/0.85      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.67/0.85         = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.67/0.85      inference('sup+', [status(thm)], ['8', '13'])).
% 0.67/0.85  thf('15', plain,
% 0.67/0.85      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.67/0.85      inference('sup-', [status(thm)], ['9', '10'])).
% 0.67/0.85  thf('16', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.67/0.85      inference('sup+', [status(thm)], ['14', '15'])).
% 0.67/0.85  thf('17', plain,
% 0.67/0.85      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 0.67/0.85      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.67/0.85  thf('18', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.67/0.85      inference('sup+', [status(thm)], ['16', '17'])).
% 0.67/0.85  thf('19', plain,
% 0.67/0.85      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.67/0.85      inference('split', [status(esa)], ['0'])).
% 0.67/0.85  thf('20', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.67/0.85      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.85  thf('21', plain,
% 0.67/0.85      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.67/0.85      inference('split', [status(esa)], ['0'])).
% 0.67/0.85  thf('22', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.67/0.85      inference('sat_resolution*', [status(thm)], ['20', '21'])).
% 0.67/0.85  thf('23', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.67/0.85      inference('simpl_trail', [status(thm)], ['1', '22'])).
% 0.67/0.85  thf('24', plain,
% 0.67/0.85      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.67/0.85      inference('sup-', [status(thm)], ['9', '10'])).
% 0.67/0.85  thf('25', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.67/0.85      inference('sup+', [status(thm)], ['14', '15'])).
% 0.67/0.85  thf('26', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.67/0.85      inference('sup-', [status(thm)], ['2', '3'])).
% 0.67/0.85  thf('27', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.67/0.85      inference('sup+', [status(thm)], ['25', '26'])).
% 0.67/0.85  thf(t50_xboole_1, axiom,
% 0.67/0.85    (![A:$i,B:$i,C:$i]:
% 0.67/0.85     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.67/0.85       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.67/0.85  thf('28', plain,
% 0.67/0.85      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.67/0.85           = (k4_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ 
% 0.67/0.85              (k3_xboole_0 @ X20 @ X22)))),
% 0.67/0.85      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.67/0.85  thf('29', plain,
% 0.67/0.85      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.67/0.85           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.67/0.85      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.67/0.85  thf('30', plain,
% 0.67/0.85      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.67/0.85           = (k3_xboole_0 @ X20 @ 
% 0.67/0.85              (k4_xboole_0 @ X21 @ (k3_xboole_0 @ X20 @ X22))))),
% 0.67/0.85      inference('demod', [status(thm)], ['28', '29'])).
% 0.67/0.85  thf('31', plain,
% 0.67/0.85      (![X0 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 0.67/0.85           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.67/0.85      inference('sup+', [status(thm)], ['27', '30'])).
% 0.67/0.85  thf('32', plain,
% 0.67/0.85      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.67/0.85           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.67/0.85      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.67/0.85  thf('33', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.67/0.85      inference('sup-', [status(thm)], ['2', '3'])).
% 0.67/0.85  thf('34', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)
% 0.67/0.85           = (k1_xboole_0))),
% 0.67/0.85      inference('sup+', [status(thm)], ['32', '33'])).
% 0.67/0.85  thf(t16_xboole_1, axiom,
% 0.67/0.85    (![A:$i,B:$i,C:$i]:
% 0.67/0.85     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.67/0.85       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.67/0.85  thf('35', plain,
% 0.67/0.85      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 0.67/0.85           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.67/0.85      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.67/0.85  thf('36', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.67/0.85      inference('sup-', [status(thm)], ['2', '3'])).
% 0.67/0.85  thf('37', plain,
% 0.67/0.85      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.85      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.67/0.85  thf('38', plain,
% 0.67/0.85      (![X6 : $i, X7 : $i]:
% 0.67/0.85         ((k4_xboole_0 @ X6 @ X7)
% 0.67/0.85           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.67/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.67/0.85  thf('39', plain,
% 0.67/0.85      (![X0 : $i]:
% 0.67/0.85         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.67/0.85      inference('sup+', [status(thm)], ['37', '38'])).
% 0.67/0.85  thf('40', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 0.67/0.85      inference('cnf', [status(esa)], [t5_boole])).
% 0.67/0.85  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.67/0.85      inference('demod', [status(thm)], ['39', '40'])).
% 0.67/0.85  thf('42', plain,
% 0.67/0.85      (![X0 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 0.67/0.85           = (k3_xboole_0 @ sk_A @ X0))),
% 0.67/0.85      inference('demod', [status(thm)], ['31', '41'])).
% 0.67/0.85  thf('43', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.67/0.85      inference('demod', [status(thm)], ['24', '42'])).
% 0.67/0.85  thf('44', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.67/0.85      inference('sup-', [status(thm)], ['2', '3'])).
% 0.67/0.85  thf('45', plain,
% 0.67/0.85      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.67/0.85           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.67/0.85      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.67/0.85  thf('46', plain,
% 0.67/0.85      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 0.67/0.85      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.67/0.85  thf('47', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.85         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 0.67/0.85      inference('sup+', [status(thm)], ['45', '46'])).
% 0.67/0.85  thf('48', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.67/0.85      inference('sup+', [status(thm)], ['44', '47'])).
% 0.67/0.85  thf('49', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.67/0.85      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.67/0.85  thf('50', plain,
% 0.67/0.85      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.67/0.85      inference('sup-', [status(thm)], ['48', '49'])).
% 0.67/0.85  thf('51', plain,
% 0.67/0.85      (![X6 : $i, X7 : $i]:
% 0.67/0.85         ((k4_xboole_0 @ X6 @ X7)
% 0.67/0.85           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.67/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.67/0.85  thf('52', plain,
% 0.67/0.85      (![X0 : $i]:
% 0.67/0.85         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.67/0.85           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.67/0.85      inference('sup+', [status(thm)], ['50', '51'])).
% 0.67/0.85  thf('53', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 0.67/0.85      inference('cnf', [status(esa)], [t5_boole])).
% 0.67/0.85  thf('54', plain,
% 0.67/0.85      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.67/0.85      inference('demod', [status(thm)], ['52', '53'])).
% 0.67/0.85  thf(t98_xboole_1, axiom,
% 0.67/0.85    (![A:$i,B:$i]:
% 0.67/0.85     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.67/0.85  thf('55', plain,
% 0.67/0.85      (![X26 : $i, X27 : $i]:
% 0.67/0.85         ((k2_xboole_0 @ X26 @ X27)
% 0.67/0.85           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.67/0.85      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.67/0.85  thf('56', plain,
% 0.67/0.85      (![X0 : $i]:
% 0.67/0.85         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.67/0.85      inference('sup+', [status(thm)], ['54', '55'])).
% 0.67/0.85  thf('57', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 0.67/0.85      inference('cnf', [status(esa)], [t5_boole])).
% 0.67/0.85  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.67/0.85      inference('demod', [status(thm)], ['56', '57'])).
% 0.67/0.85  thf(t46_xboole_1, axiom,
% 0.67/0.85    (![A:$i,B:$i]:
% 0.67/0.85     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.67/0.85  thf('59', plain,
% 0.67/0.85      (![X15 : $i, X16 : $i]:
% 0.67/0.85         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (k1_xboole_0))),
% 0.67/0.85      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.67/0.85  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.67/0.85      inference('sup+', [status(thm)], ['58', '59'])).
% 0.67/0.85  thf('61', plain,
% 0.67/0.85      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.67/0.85         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.67/0.85           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.67/0.85      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.67/0.85  thf(l32_xboole_1, axiom,
% 0.67/0.85    (![A:$i,B:$i]:
% 0.67/0.85     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.85  thf('62', plain,
% 0.67/0.85      (![X3 : $i, X4 : $i]:
% 0.67/0.85         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.67/0.85      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.67/0.85  thf('63', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.85         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.67/0.85          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.67/0.85      inference('sup-', [status(thm)], ['61', '62'])).
% 0.67/0.85  thf('64', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         (((k3_xboole_0 @ X1 @ k1_xboole_0) != (k1_xboole_0))
% 0.67/0.85          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.67/0.85      inference('sup-', [status(thm)], ['60', '63'])).
% 0.67/0.85  thf('65', plain,
% 0.67/0.85      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.85      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.67/0.85  thf('66', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         (((k1_xboole_0) != (k1_xboole_0))
% 0.67/0.85          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.67/0.85      inference('demod', [status(thm)], ['64', '65'])).
% 0.67/0.85  thf('67', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.67/0.85      inference('simplify', [status(thm)], ['66'])).
% 0.67/0.85  thf('68', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.67/0.85      inference('sup+', [status(thm)], ['43', '67'])).
% 0.67/0.85  thf('69', plain, ($false), inference('demod', [status(thm)], ['23', '68'])).
% 0.67/0.85  
% 0.67/0.85  % SZS output end Refutation
% 0.67/0.85  
% 0.67/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
