%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h98hjYRJDC

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:31 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 222 expanded)
%              Number of leaves         :   27 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  688 (1565 expanded)
%              Number of equality atoms :   60 ( 126 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('19',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34','43'])).

thf('45',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference('sup+',[status(thm)],['20','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('47',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('54',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('63',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('66',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('69',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['63','78'])).

thf('80',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['52','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h98hjYRJDC
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:46:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.50/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.71  % Solved by: fo/fo7.sh
% 0.50/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.71  % done 801 iterations in 0.281s
% 0.50/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.71  % SZS output start Refutation
% 0.50/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.50/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.50/0.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.50/0.71  thf(sk_B_type, type, sk_B: $i > $i).
% 0.50/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.50/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.50/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.50/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.71  thf(t106_xboole_1, conjecture,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.50/0.71       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.50/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.50/0.71        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.50/0.71          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.50/0.71    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.50/0.71  thf('0', plain,
% 0.50/0.71      ((~ (r1_tarski @ sk_A @ sk_B_1) | ~ (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('1', plain,
% 0.50/0.71      ((~ (r1_tarski @ sk_A @ sk_B_1)) <= (~ ((r1_tarski @ sk_A @ sk_B_1)))),
% 0.50/0.71      inference('split', [status(esa)], ['0'])).
% 0.50/0.71  thf(t17_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.50/0.71  thf('2', plain,
% 0.50/0.71      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 0.50/0.71      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.50/0.71  thf(l32_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.50/0.71  thf('3', plain,
% 0.50/0.71      (![X9 : $i, X11 : $i]:
% 0.50/0.71         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.50/0.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.50/0.71  thf('4', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.71  thf(t49_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.50/0.71       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.50/0.71  thf('5', plain,
% 0.50/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.71         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 0.50/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 0.50/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.50/0.71  thf('6', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.50/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.50/0.71  thf(t100_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.50/0.71  thf('7', plain,
% 0.50/0.71      (![X14 : $i, X15 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X14 @ X15)
% 0.50/0.71           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.71  thf('8', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.50/0.71           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['6', '7'])).
% 0.50/0.71  thf(t5_boole, axiom,
% 0.50/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.50/0.71  thf('9', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 0.50/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.50/0.71  thf('10', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['8', '9'])).
% 0.50/0.71  thf('11', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['8', '9'])).
% 0.50/0.71  thf('12', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(t28_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.50/0.71  thf('13', plain,
% 0.50/0.71      (![X20 : $i, X21 : $i]:
% 0.50/0.71         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.50/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.71  thf('14', plain,
% 0.50/0.71      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['12', '13'])).
% 0.50/0.71  thf('15', plain,
% 0.50/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.71         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 0.50/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 0.50/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.50/0.71  thf('16', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((k3_xboole_0 @ sk_A @ 
% 0.50/0.71           (k4_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ X0))
% 0.50/0.71           = (k4_xboole_0 @ sk_A @ X0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['14', '15'])).
% 0.50/0.71  thf('17', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.50/0.71           = (k4_xboole_0 @ sk_A @ 
% 0.50/0.71              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['11', '16'])).
% 0.50/0.71  thf('18', plain,
% 0.50/0.71      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['12', '13'])).
% 0.50/0.71  thf('19', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((sk_A)
% 0.50/0.71           = (k4_xboole_0 @ sk_A @ 
% 0.50/0.71              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 0.50/0.71      inference('demod', [status(thm)], ['17', '18'])).
% 0.50/0.71  thf('20', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.50/0.71      inference('sup+', [status(thm)], ['10', '19'])).
% 0.50/0.71  thf('21', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.50/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.50/0.71  thf(t4_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.50/0.71            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.50/0.71       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.50/0.71            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.50/0.71  thf('22', plain,
% 0.50/0.71      (![X4 : $i, X5 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X4 @ X5)
% 0.50/0.71          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.50/0.71  thf(t21_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.50/0.71  thf('23', plain,
% 0.50/0.71      (![X18 : $i, X19 : $i]:
% 0.50/0.71         ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (X18))),
% 0.50/0.71      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.50/0.71  thf('24', plain,
% 0.50/0.71      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 0.50/0.71      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.50/0.71  thf('25', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.50/0.71      inference('sup+', [status(thm)], ['23', '24'])).
% 0.50/0.71  thf('26', plain,
% 0.50/0.71      (![X20 : $i, X21 : $i]:
% 0.50/0.71         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.50/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.71  thf('27', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.50/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.50/0.71  thf('28', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.71  thf('29', plain,
% 0.50/0.71      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.50/0.71          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.50/0.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.50/0.71  thf('30', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.50/0.71          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.71  thf('31', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['27', '30'])).
% 0.50/0.71  thf('32', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X1 @ X0)
% 0.50/0.71          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['22', '31'])).
% 0.50/0.71  thf('33', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (~ (r1_xboole_0 @ k1_xboole_0 @ 
% 0.50/0.71             (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.50/0.71          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['21', '32'])).
% 0.50/0.71  thf('34', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.50/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.50/0.71  thf('35', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.50/0.71  thf(l97_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.50/0.71  thf('36', plain,
% 0.50/0.71      (![X12 : $i, X13 : $i]:
% 0.50/0.71         (r1_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k5_xboole_0 @ X12 @ X13))),
% 0.50/0.71      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.50/0.71  thf('37', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['35', '36'])).
% 0.50/0.71  thf(t92_xboole_1, axiom,
% 0.50/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.50/0.71  thf('38', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ X29) = (k1_xboole_0))),
% 0.50/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.50/0.71  thf('39', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.50/0.71      inference('demod', [status(thm)], ['37', '38'])).
% 0.50/0.71  thf('40', plain,
% 0.50/0.71      (![X4 : $i, X5 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X4 @ X5)
% 0.50/0.71          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.50/0.71  thf('41', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.50/0.71          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.71  thf('42', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('sup-', [status(thm)], ['40', '41'])).
% 0.50/0.71  thf('43', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.50/0.71      inference('sup-', [status(thm)], ['39', '42'])).
% 0.50/0.71  thf('44', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['33', '34', '43'])).
% 0.50/0.71  thf('45', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.50/0.71      inference('sup+', [status(thm)], ['20', '44'])).
% 0.50/0.71  thf('46', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('sup-', [status(thm)], ['40', '41'])).
% 0.50/0.71  thf('47', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.50/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.71  thf('48', plain,
% 0.50/0.71      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.50/0.71      inference('split', [status(esa)], ['0'])).
% 0.50/0.71  thf('49', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.50/0.71      inference('sup-', [status(thm)], ['47', '48'])).
% 0.50/0.71  thf('50', plain,
% 0.50/0.71      (~ ((r1_tarski @ sk_A @ sk_B_1)) | ~ ((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.50/0.71      inference('split', [status(esa)], ['0'])).
% 0.50/0.71  thf('51', plain, (~ ((r1_tarski @ sk_A @ sk_B_1))),
% 0.50/0.71      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.50/0.71  thf('52', plain, (~ (r1_tarski @ sk_A @ sk_B_1)),
% 0.50/0.71      inference('simpl_trail', [status(thm)], ['1', '51'])).
% 0.50/0.71  thf('53', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.50/0.71  thf('54', plain,
% 0.50/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.71         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 0.50/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 0.50/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.50/0.71  thf('55', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.50/0.71           = (k4_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('sup+', [status(thm)], ['53', '54'])).
% 0.50/0.71  thf('56', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.71  thf('57', plain,
% 0.50/0.71      (![X14 : $i, X15 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X14 @ X15)
% 0.50/0.71           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.71  thf('58', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X0 @ X1)
% 0.50/0.71           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['56', '57'])).
% 0.50/0.71  thf('59', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.50/0.71           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['55', '58'])).
% 0.50/0.71  thf('60', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ X29) = (k1_xboole_0))),
% 0.50/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.50/0.71  thf('61', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.50/0.71      inference('demod', [status(thm)], ['59', '60'])).
% 0.50/0.71  thf('62', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((k3_xboole_0 @ sk_A @ 
% 0.50/0.71           (k4_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ X0))
% 0.50/0.71           = (k4_xboole_0 @ sk_A @ X0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['14', '15'])).
% 0.50/0.71  thf('63', plain,
% 0.50/0.71      (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.50/0.71      inference('sup+', [status(thm)], ['61', '62'])).
% 0.50/0.71  thf('64', plain,
% 0.50/0.71      (![X14 : $i, X15 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X14 @ X15)
% 0.50/0.71           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.71  thf(commutativity_k5_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.50/0.71  thf('65', plain,
% 0.50/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.50/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.50/0.71  thf('66', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 0.50/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.50/0.71  thf('67', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['65', '66'])).
% 0.50/0.71  thf('68', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['64', '67'])).
% 0.50/0.71  thf(t7_xboole_0, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.50/0.71          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.50/0.71  thf('69', plain,
% 0.50/0.71      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.50/0.71      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.50/0.71  thf('70', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['64', '67'])).
% 0.50/0.71  thf('71', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.50/0.71          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.71  thf('72', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.50/0.71          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['70', '71'])).
% 0.50/0.71  thf('73', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.50/0.71      inference('demod', [status(thm)], ['37', '38'])).
% 0.50/0.71  thf('74', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['72', '73'])).
% 0.50/0.71  thf('75', plain,
% 0.50/0.71      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['69', '74'])).
% 0.50/0.71  thf('76', plain,
% 0.50/0.71      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['68', '75'])).
% 0.50/0.71  thf('77', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.71  thf('78', plain,
% 0.50/0.71      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['76', '77'])).
% 0.50/0.71  thf('79', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.50/0.71      inference('demod', [status(thm)], ['63', '78'])).
% 0.50/0.71  thf('80', plain,
% 0.50/0.71      (![X9 : $i, X10 : $i]:
% 0.50/0.71         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 0.50/0.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.50/0.71  thf('81', plain,
% 0.50/0.71      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B_1))),
% 0.50/0.71      inference('sup-', [status(thm)], ['79', '80'])).
% 0.50/0.71  thf('82', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.50/0.71      inference('simplify', [status(thm)], ['81'])).
% 0.50/0.71  thf('83', plain, ($false), inference('demod', [status(thm)], ['52', '82'])).
% 0.50/0.71  
% 0.50/0.71  % SZS output end Refutation
% 0.50/0.71  
% 0.50/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
