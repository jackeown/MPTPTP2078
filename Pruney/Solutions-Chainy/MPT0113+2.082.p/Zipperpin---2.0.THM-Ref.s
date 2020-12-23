%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kScsPhctXG

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:39 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 187 expanded)
%              Number of leaves         :   23 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  644 (1358 expanded)
%              Number of equality atoms :   68 ( 121 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X22: $i,X23: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X23 ) ),
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
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X23 ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
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
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('46',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X23 ) ),
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
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('62',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['43','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['23','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kScsPhctXG
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 10:57:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.18/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.57  % Solved by: fo/fo7.sh
% 0.18/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.57  % done 266 iterations in 0.129s
% 0.18/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.57  % SZS output start Refutation
% 0.18/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.18/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.18/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.18/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.18/0.57  thf(t106_xboole_1, conjecture,
% 0.18/0.57    (![A:$i,B:$i,C:$i]:
% 0.18/0.57     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.18/0.57       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.18/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.18/0.57        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.18/0.57          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.18/0.57    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.18/0.57  thf('0', plain,
% 0.18/0.57      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('1', plain,
% 0.18/0.57      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.18/0.57      inference('split', [status(esa)], ['0'])).
% 0.18/0.57  thf(t79_xboole_1, axiom,
% 0.18/0.57    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.18/0.57  thf('2', plain,
% 0.18/0.57      (![X22 : $i, X23 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X23)),
% 0.18/0.57      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.18/0.57  thf(d7_xboole_0, axiom,
% 0.18/0.57    (![A:$i,B:$i]:
% 0.18/0.57     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.18/0.57       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.18/0.57  thf('3', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.18/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.18/0.57  thf('4', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.18/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.57  thf(t100_xboole_1, axiom,
% 0.18/0.57    (![A:$i,B:$i]:
% 0.18/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.18/0.57  thf('5', plain,
% 0.18/0.57      (![X6 : $i, X7 : $i]:
% 0.18/0.57         ((k4_xboole_0 @ X6 @ X7)
% 0.18/0.57           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.18/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.18/0.57  thf('6', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.18/0.57           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.18/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.18/0.57  thf(t5_boole, axiom,
% 0.18/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.18/0.57  thf('7', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.18/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.18/0.57  thf('8', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.18/0.57           = (k4_xboole_0 @ X1 @ X0))),
% 0.18/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.18/0.57  thf('9', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf(t28_xboole_1, axiom,
% 0.18/0.57    (![A:$i,B:$i]:
% 0.18/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.18/0.57  thf('10', plain,
% 0.18/0.57      (![X13 : $i, X14 : $i]:
% 0.18/0.57         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.18/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.18/0.57  thf('11', plain,
% 0.18/0.57      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.18/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.57  thf(t49_xboole_1, axiom,
% 0.18/0.57    (![A:$i,B:$i,C:$i]:
% 0.18/0.57     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.18/0.57       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.18/0.57  thf('12', plain,
% 0.18/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 0.18/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 0.18/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.18/0.57  thf('13', plain,
% 0.18/0.57      (![X0 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ sk_A @ 
% 0.18/0.57           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.18/0.57           = (k4_xboole_0 @ sk_A @ X0))),
% 0.18/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.18/0.57  thf('14', plain,
% 0.18/0.57      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.18/0.57         = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.18/0.57      inference('sup+', [status(thm)], ['8', '13'])).
% 0.18/0.57  thf('15', plain,
% 0.18/0.57      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.18/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.57  thf('16', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.18/0.57      inference('sup+', [status(thm)], ['14', '15'])).
% 0.18/0.57  thf('17', plain,
% 0.18/0.57      (![X22 : $i, X23 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X23)),
% 0.18/0.57      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.18/0.57  thf('18', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.18/0.57      inference('sup+', [status(thm)], ['16', '17'])).
% 0.18/0.57  thf('19', plain,
% 0.18/0.57      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.18/0.57      inference('split', [status(esa)], ['0'])).
% 0.18/0.57  thf('20', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.18/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.18/0.57  thf('21', plain,
% 0.18/0.57      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.18/0.57      inference('split', [status(esa)], ['0'])).
% 0.18/0.57  thf('22', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.18/0.57      inference('sat_resolution*', [status(thm)], ['20', '21'])).
% 0.18/0.57  thf('23', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.18/0.57      inference('simpl_trail', [status(thm)], ['1', '22'])).
% 0.18/0.57  thf('24', plain,
% 0.18/0.57      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.18/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.57  thf('25', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.18/0.57      inference('sup+', [status(thm)], ['14', '15'])).
% 0.18/0.57  thf('26', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.18/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.57  thf('27', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.18/0.57      inference('sup+', [status(thm)], ['25', '26'])).
% 0.18/0.57  thf(t50_xboole_1, axiom,
% 0.18/0.57    (![A:$i,B:$i,C:$i]:
% 0.18/0.57     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.18/0.57       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.18/0.57  thf('28', plain,
% 0.18/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.18/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 0.18/0.57              (k3_xboole_0 @ X18 @ X20)))),
% 0.18/0.57      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.18/0.57  thf('29', plain,
% 0.18/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 0.18/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 0.18/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.18/0.57  thf('30', plain,
% 0.18/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.18/0.57           = (k3_xboole_0 @ X18 @ 
% 0.18/0.57              (k4_xboole_0 @ X19 @ (k3_xboole_0 @ X18 @ X20))))),
% 0.18/0.57      inference('demod', [status(thm)], ['28', '29'])).
% 0.18/0.57  thf('31', plain,
% 0.18/0.57      (![X0 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 0.18/0.57           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.18/0.57      inference('sup+', [status(thm)], ['27', '30'])).
% 0.18/0.57  thf('32', plain,
% 0.18/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 0.18/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 0.18/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.18/0.57  thf('33', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.18/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.57  thf('34', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)
% 0.18/0.57           = (k1_xboole_0))),
% 0.18/0.57      inference('sup+', [status(thm)], ['32', '33'])).
% 0.18/0.57  thf(t16_xboole_1, axiom,
% 0.18/0.57    (![A:$i,B:$i,C:$i]:
% 0.18/0.57     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.18/0.57       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.18/0.57  thf('35', plain,
% 0.18/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 0.18/0.57           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.18/0.57      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.18/0.57  thf('36', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.18/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.57  thf('37', plain,
% 0.18/0.57      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.18/0.57      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.18/0.57  thf('38', plain,
% 0.18/0.57      (![X6 : $i, X7 : $i]:
% 0.18/0.57         ((k4_xboole_0 @ X6 @ X7)
% 0.18/0.57           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.18/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.18/0.57  thf('39', plain,
% 0.18/0.57      (![X0 : $i]:
% 0.18/0.57         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.18/0.57      inference('sup+', [status(thm)], ['37', '38'])).
% 0.18/0.57  thf('40', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.18/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.18/0.57  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.18/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.18/0.57  thf('42', plain,
% 0.18/0.57      (![X0 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 0.18/0.57           = (k3_xboole_0 @ sk_A @ X0))),
% 0.18/0.57      inference('demod', [status(thm)], ['31', '41'])).
% 0.18/0.57  thf('43', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.18/0.57      inference('demod', [status(thm)], ['24', '42'])).
% 0.18/0.57  thf('44', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.18/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.57  thf('45', plain,
% 0.18/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 0.18/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 0.18/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.18/0.57  thf('46', plain,
% 0.18/0.57      (![X22 : $i, X23 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X23)),
% 0.18/0.57      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.18/0.57  thf('47', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.57         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 0.18/0.57      inference('sup+', [status(thm)], ['45', '46'])).
% 0.18/0.57  thf('48', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.18/0.57      inference('sup+', [status(thm)], ['44', '47'])).
% 0.18/0.57  thf('49', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.18/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.18/0.57  thf('50', plain,
% 0.18/0.57      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.18/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.18/0.57  thf('51', plain,
% 0.18/0.57      (![X6 : $i, X7 : $i]:
% 0.18/0.57         ((k4_xboole_0 @ X6 @ X7)
% 0.18/0.57           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.18/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.18/0.57  thf('52', plain,
% 0.18/0.57      (![X0 : $i]:
% 0.18/0.57         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.18/0.57           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.18/0.57      inference('sup+', [status(thm)], ['50', '51'])).
% 0.18/0.57  thf('53', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.18/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.18/0.57  thf('54', plain,
% 0.18/0.57      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.18/0.57      inference('demod', [status(thm)], ['52', '53'])).
% 0.18/0.57  thf(t98_xboole_1, axiom,
% 0.18/0.57    (![A:$i,B:$i]:
% 0.18/0.57     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.18/0.57  thf('55', plain,
% 0.18/0.57      (![X25 : $i, X26 : $i]:
% 0.18/0.57         ((k2_xboole_0 @ X25 @ X26)
% 0.18/0.57           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.18/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.18/0.57  thf('56', plain,
% 0.18/0.57      (![X0 : $i]:
% 0.18/0.57         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.18/0.57      inference('sup+', [status(thm)], ['54', '55'])).
% 0.18/0.57  thf('57', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.18/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.18/0.57  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.18/0.57      inference('sup+', [status(thm)], ['56', '57'])).
% 0.18/0.57  thf(t21_xboole_1, axiom,
% 0.18/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.18/0.57  thf('59', plain,
% 0.18/0.57      (![X11 : $i, X12 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (X11))),
% 0.18/0.57      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.18/0.57  thf('60', plain,
% 0.18/0.57      (![X6 : $i, X7 : $i]:
% 0.18/0.57         ((k4_xboole_0 @ X6 @ X7)
% 0.18/0.57           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.18/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.18/0.57  thf('61', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.18/0.57           = (k5_xboole_0 @ X0 @ X0))),
% 0.18/0.57      inference('sup+', [status(thm)], ['59', '60'])).
% 0.18/0.57  thf(t92_xboole_1, axiom,
% 0.18/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.18/0.57  thf('62', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 0.18/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.18/0.57  thf('63', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.18/0.57      inference('demod', [status(thm)], ['61', '62'])).
% 0.18/0.57  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.18/0.57      inference('sup+', [status(thm)], ['58', '63'])).
% 0.18/0.57  thf('65', plain,
% 0.18/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.18/0.57         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 0.18/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 0.18/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.18/0.57  thf(l32_xboole_1, axiom,
% 0.18/0.57    (![A:$i,B:$i]:
% 0.18/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.18/0.57  thf('66', plain,
% 0.18/0.57      (![X3 : $i, X4 : $i]:
% 0.18/0.57         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.18/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.18/0.57  thf('67', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.57         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.18/0.57          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.18/0.57      inference('sup-', [status(thm)], ['65', '66'])).
% 0.18/0.57  thf('68', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         (((k3_xboole_0 @ X1 @ k1_xboole_0) != (k1_xboole_0))
% 0.18/0.57          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.18/0.57      inference('sup-', [status(thm)], ['64', '67'])).
% 0.18/0.57  thf('69', plain,
% 0.18/0.57      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.18/0.57      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.18/0.57  thf('70', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.18/0.57          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.18/0.57      inference('demod', [status(thm)], ['68', '69'])).
% 0.18/0.57  thf('71', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.18/0.57      inference('simplify', [status(thm)], ['70'])).
% 0.18/0.57  thf('72', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.18/0.57      inference('sup+', [status(thm)], ['43', '71'])).
% 0.18/0.57  thf('73', plain, ($false), inference('demod', [status(thm)], ['23', '72'])).
% 0.18/0.57  
% 0.18/0.57  % SZS output end Refutation
% 0.18/0.57  
% 0.18/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
