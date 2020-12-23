%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pG82wEbwgt

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:31 EST 2020

% Result     : Theorem 4.76s
% Output     : Refutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 168 expanded)
%              Number of leaves         :   25 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  701 (1251 expanded)
%              Number of equality atoms :   64 ( 101 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('2',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('15',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('16',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k3_xboole_0 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('32',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k3_xboole_0 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('44',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','40','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','45'])).

thf('47',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k3_xboole_0 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C_1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
      = ( k3_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','57','58','59'])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['14','60'])).

thf('62',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('63',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('68',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('72',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference('sup+',[status(thm)],['61','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['13','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pG82wEbwgt
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:52:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 4.76/4.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.76/4.93  % Solved by: fo/fo7.sh
% 4.76/4.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.76/4.93  % done 3280 iterations in 4.481s
% 4.76/4.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.76/4.93  % SZS output start Refutation
% 4.76/4.93  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.76/4.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.76/4.93  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.76/4.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.76/4.93  thf(sk_B_type, type, sk_B: $i > $i).
% 4.76/4.93  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.76/4.93  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.76/4.93  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.76/4.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.76/4.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.76/4.93  thf(sk_A_type, type, sk_A: $i).
% 4.76/4.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.76/4.93  thf(t106_xboole_1, conjecture,
% 4.76/4.93    (![A:$i,B:$i,C:$i]:
% 4.76/4.93     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 4.76/4.93       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 4.76/4.93  thf(zf_stmt_0, negated_conjecture,
% 4.76/4.93    (~( ![A:$i,B:$i,C:$i]:
% 4.76/4.93        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 4.76/4.93          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 4.76/4.93    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 4.76/4.93  thf('0', plain,
% 4.76/4.93      ((~ (r1_tarski @ sk_A @ sk_B_1) | ~ (r1_xboole_0 @ sk_A @ sk_C_1))),
% 4.76/4.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.93  thf('1', plain,
% 4.76/4.93      ((~ (r1_tarski @ sk_A @ sk_B_1)) <= (~ ((r1_tarski @ sk_A @ sk_B_1)))),
% 4.76/4.93      inference('split', [status(esa)], ['0'])).
% 4.76/4.93  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 4.76/4.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.93  thf(t28_xboole_1, axiom,
% 4.76/4.93    (![A:$i,B:$i]:
% 4.76/4.93     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.76/4.93  thf('3', plain,
% 4.76/4.93      (![X17 : $i, X18 : $i]:
% 4.76/4.93         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 4.76/4.93      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.76/4.93  thf('4', plain,
% 4.76/4.93      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (sk_A))),
% 4.76/4.93      inference('sup-', [status(thm)], ['2', '3'])).
% 4.76/4.93  thf(t49_xboole_1, axiom,
% 4.76/4.93    (![A:$i,B:$i,C:$i]:
% 4.76/4.93     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 4.76/4.93       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 4.76/4.93  thf('5', plain,
% 4.76/4.93      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 4.76/4.93           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 4.76/4.93      inference('cnf', [status(esa)], [t49_xboole_1])).
% 4.76/4.93  thf(t79_xboole_1, axiom,
% 4.76/4.93    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 4.76/4.93  thf('6', plain,
% 4.76/4.93      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 4.76/4.93      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.76/4.93  thf('7', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.76/4.93         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 4.76/4.93      inference('sup+', [status(thm)], ['5', '6'])).
% 4.76/4.93  thf('8', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 4.76/4.93      inference('sup+', [status(thm)], ['4', '7'])).
% 4.76/4.93  thf('9', plain,
% 4.76/4.93      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 4.76/4.93      inference('split', [status(esa)], ['0'])).
% 4.76/4.93  thf('10', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 4.76/4.93      inference('sup-', [status(thm)], ['8', '9'])).
% 4.76/4.93  thf('11', plain,
% 4.76/4.93      (~ ((r1_tarski @ sk_A @ sk_B_1)) | ~ ((r1_xboole_0 @ sk_A @ sk_C_1))),
% 4.76/4.93      inference('split', [status(esa)], ['0'])).
% 4.76/4.93  thf('12', plain, (~ ((r1_tarski @ sk_A @ sk_B_1))),
% 4.76/4.93      inference('sat_resolution*', [status(thm)], ['10', '11'])).
% 4.76/4.93  thf('13', plain, (~ (r1_tarski @ sk_A @ sk_B_1)),
% 4.76/4.93      inference('simpl_trail', [status(thm)], ['1', '12'])).
% 4.76/4.93  thf('14', plain,
% 4.76/4.93      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (sk_A))),
% 4.76/4.93      inference('sup-', [status(thm)], ['2', '3'])).
% 4.76/4.93  thf('15', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 4.76/4.93      inference('sup+', [status(thm)], ['4', '7'])).
% 4.76/4.93  thf(t7_xboole_0, axiom,
% 4.76/4.93    (![A:$i]:
% 4.76/4.93     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.76/4.93          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 4.76/4.93  thf('16', plain,
% 4.76/4.93      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 4.76/4.93      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.76/4.93  thf(commutativity_k3_xboole_0, axiom,
% 4.76/4.93    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.76/4.93  thf('17', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.76/4.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.76/4.93  thf(t4_xboole_0, axiom,
% 4.76/4.93    (![A:$i,B:$i]:
% 4.76/4.93     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 4.76/4.93            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.76/4.93       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.76/4.93            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 4.76/4.93  thf('18', plain,
% 4.76/4.93      (![X4 : $i, X6 : $i, X7 : $i]:
% 4.76/4.93         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 4.76/4.93          | ~ (r1_xboole_0 @ X4 @ X7))),
% 4.76/4.93      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.76/4.93  thf('19', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.76/4.93         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 4.76/4.93          | ~ (r1_xboole_0 @ X0 @ X1))),
% 4.76/4.93      inference('sup-', [status(thm)], ['17', '18'])).
% 4.76/4.93  thf('20', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i]:
% 4.76/4.93         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 4.76/4.93      inference('sup-', [status(thm)], ['16', '19'])).
% 4.76/4.93  thf('21', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 4.76/4.93      inference('sup-', [status(thm)], ['15', '20'])).
% 4.76/4.93  thf('22', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.76/4.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.76/4.93  thf(t16_xboole_1, axiom,
% 4.76/4.93    (![A:$i,B:$i,C:$i]:
% 4.76/4.93     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 4.76/4.93       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 4.76/4.93  thf('23', plain,
% 4.76/4.93      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16)
% 4.76/4.93           = (k3_xboole_0 @ X14 @ (k3_xboole_0 @ X15 @ X16)))),
% 4.76/4.93      inference('cnf', [status(esa)], [t16_xboole_1])).
% 4.76/4.93  thf('24', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 4.76/4.93           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 4.76/4.93      inference('sup+', [status(thm)], ['22', '23'])).
% 4.76/4.93  thf('25', plain,
% 4.76/4.93      (![X0 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 4.76/4.93           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 4.76/4.93      inference('sup+', [status(thm)], ['21', '24'])).
% 4.76/4.93  thf(t100_xboole_1, axiom,
% 4.76/4.93    (![A:$i,B:$i]:
% 4.76/4.93     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.76/4.93  thf('26', plain,
% 4.76/4.93      (![X12 : $i, X13 : $i]:
% 4.76/4.93         ((k4_xboole_0 @ X12 @ X13)
% 4.76/4.93           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 4.76/4.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.76/4.93  thf(commutativity_k5_xboole_0, axiom,
% 4.76/4.93    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 4.76/4.93  thf('27', plain,
% 4.76/4.93      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 4.76/4.93      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 4.76/4.93  thf(t5_boole, axiom,
% 4.76/4.93    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.76/4.93  thf('28', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 4.76/4.93      inference('cnf', [status(esa)], [t5_boole])).
% 4.76/4.93  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.76/4.93      inference('sup+', [status(thm)], ['27', '28'])).
% 4.76/4.93  thf('30', plain,
% 4.76/4.93      (![X0 : $i]:
% 4.76/4.93         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 4.76/4.93      inference('sup+', [status(thm)], ['26', '29'])).
% 4.76/4.93  thf('31', plain,
% 4.76/4.93      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (sk_A))),
% 4.76/4.93      inference('sup-', [status(thm)], ['2', '3'])).
% 4.76/4.93  thf('32', plain,
% 4.76/4.93      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16)
% 4.76/4.93           = (k3_xboole_0 @ X14 @ (k3_xboole_0 @ X15 @ X16)))),
% 4.76/4.93      inference('cnf', [status(esa)], [t16_xboole_1])).
% 4.76/4.93  thf('33', plain,
% 4.76/4.93      (![X12 : $i, X13 : $i]:
% 4.76/4.93         ((k4_xboole_0 @ X12 @ X13)
% 4.76/4.93           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 4.76/4.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.76/4.93  thf('34', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.76/4.93         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 4.76/4.93           = (k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 4.76/4.93              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 4.76/4.93      inference('sup+', [status(thm)], ['32', '33'])).
% 4.76/4.93  thf('35', plain,
% 4.76/4.93      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 4.76/4.93           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 4.76/4.93      inference('cnf', [status(esa)], [t49_xboole_1])).
% 4.76/4.93  thf('36', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 4.76/4.93           = (k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 4.76/4.93              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 4.76/4.93      inference('demod', [status(thm)], ['34', '35'])).
% 4.76/4.93  thf('37', plain,
% 4.76/4.93      (![X0 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ X0 @ 
% 4.76/4.93           (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)))
% 4.76/4.93           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ 
% 4.76/4.93              (k3_xboole_0 @ X0 @ sk_A)))),
% 4.76/4.93      inference('sup+', [status(thm)], ['31', '36'])).
% 4.76/4.93  thf('38', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 4.76/4.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.93  thf(l32_xboole_1, axiom,
% 4.76/4.93    (![A:$i,B:$i]:
% 4.76/4.93     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.76/4.93  thf('39', plain,
% 4.76/4.93      (![X9 : $i, X11 : $i]:
% 4.76/4.93         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 4.76/4.93      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.76/4.93  thf('40', plain,
% 4.76/4.93      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (k1_xboole_0))),
% 4.76/4.93      inference('sup-', [status(thm)], ['38', '39'])).
% 4.76/4.93  thf('41', plain,
% 4.76/4.93      (![X0 : $i]:
% 4.76/4.93         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 4.76/4.93      inference('sup+', [status(thm)], ['26', '29'])).
% 4.76/4.93  thf('42', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.76/4.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.76/4.93  thf('43', plain,
% 4.76/4.93      (![X0 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 4.76/4.93      inference('sup+', [status(thm)], ['41', '42'])).
% 4.76/4.93  thf(t92_xboole_1, axiom,
% 4.76/4.93    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 4.76/4.93  thf('44', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ X28) = (k1_xboole_0))),
% 4.76/4.93      inference('cnf', [status(esa)], [t92_xboole_1])).
% 4.76/4.93  thf('45', plain,
% 4.76/4.93      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.76/4.93      inference('demod', [status(thm)], ['37', '40', '43', '44'])).
% 4.76/4.93  thf('46', plain,
% 4.76/4.93      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 4.76/4.93      inference('demod', [status(thm)], ['30', '45'])).
% 4.76/4.93  thf('47', plain,
% 4.76/4.93      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16)
% 4.76/4.93           = (k3_xboole_0 @ X14 @ (k3_xboole_0 @ X15 @ X16)))),
% 4.76/4.93      inference('cnf', [status(esa)], [t16_xboole_1])).
% 4.76/4.93  thf('48', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.76/4.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.76/4.93  thf('49', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 4.76/4.93           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.76/4.93      inference('sup+', [status(thm)], ['47', '48'])).
% 4.76/4.93  thf('50', plain,
% 4.76/4.93      (![X0 : $i]:
% 4.76/4.93         ((k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_A)))),
% 4.76/4.93      inference('demod', [status(thm)], ['25', '46', '49'])).
% 4.76/4.93  thf('51', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.76/4.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.76/4.93  thf('52', plain,
% 4.76/4.93      (![X12 : $i, X13 : $i]:
% 4.76/4.93         ((k4_xboole_0 @ X12 @ X13)
% 4.76/4.93           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 4.76/4.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.76/4.93  thf('53', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i]:
% 4.76/4.93         ((k4_xboole_0 @ X0 @ X1)
% 4.76/4.93           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.76/4.93      inference('sup+', [status(thm)], ['51', '52'])).
% 4.76/4.93  thf('54', plain,
% 4.76/4.93      (![X0 : $i]:
% 4.76/4.93         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C_1)
% 4.76/4.93           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ k1_xboole_0))),
% 4.76/4.93      inference('sup+', [status(thm)], ['50', '53'])).
% 4.76/4.93  thf('55', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.76/4.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.76/4.93  thf('56', plain,
% 4.76/4.93      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 4.76/4.93           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 4.76/4.93      inference('cnf', [status(esa)], [t49_xboole_1])).
% 4.76/4.93  thf('57', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 4.76/4.93           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 4.76/4.93      inference('sup+', [status(thm)], ['55', '56'])).
% 4.76/4.93  thf('58', plain,
% 4.76/4.93      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 4.76/4.93      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 4.76/4.93  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.76/4.93      inference('sup+', [status(thm)], ['27', '28'])).
% 4.76/4.93  thf('60', plain,
% 4.76/4.93      (![X0 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1))
% 4.76/4.93           = (k3_xboole_0 @ X0 @ sk_A))),
% 4.76/4.93      inference('demod', [status(thm)], ['54', '57', '58', '59'])).
% 4.76/4.93  thf('61', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_A))),
% 4.76/4.93      inference('demod', [status(thm)], ['14', '60'])).
% 4.76/4.93  thf('62', plain,
% 4.76/4.93      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 4.76/4.93      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.76/4.93  thf('63', plain,
% 4.76/4.93      (![X4 : $i, X5 : $i]:
% 4.76/4.93         ((r1_xboole_0 @ X4 @ X5)
% 4.76/4.93          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 4.76/4.93      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.76/4.93  thf('64', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.76/4.93         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 4.76/4.93          | ~ (r1_xboole_0 @ X0 @ X1))),
% 4.76/4.93      inference('sup-', [status(thm)], ['17', '18'])).
% 4.76/4.93  thf('65', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i]:
% 4.76/4.93         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 4.76/4.93      inference('sup-', [status(thm)], ['63', '64'])).
% 4.76/4.93  thf('66', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.76/4.93      inference('sup-', [status(thm)], ['62', '65'])).
% 4.76/4.93  thf('67', plain,
% 4.76/4.93      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 4.76/4.93      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.76/4.93  thf('68', plain,
% 4.76/4.93      (![X4 : $i, X6 : $i, X7 : $i]:
% 4.76/4.93         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 4.76/4.93          | ~ (r1_xboole_0 @ X4 @ X7))),
% 4.76/4.93      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.76/4.93  thf('69', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i]:
% 4.76/4.93         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 4.76/4.93      inference('sup-', [status(thm)], ['67', '68'])).
% 4.76/4.93  thf('70', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 4.76/4.93      inference('sup-', [status(thm)], ['66', '69'])).
% 4.76/4.93  thf('71', plain,
% 4.76/4.93      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.76/4.93         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 4.76/4.93           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 4.76/4.93      inference('cnf', [status(esa)], [t49_xboole_1])).
% 4.76/4.93  thf('72', plain,
% 4.76/4.93      (![X9 : $i, X10 : $i]:
% 4.76/4.93         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 4.76/4.93      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.76/4.93  thf('73', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.76/4.93         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 4.76/4.93          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 4.76/4.93      inference('sup-', [status(thm)], ['71', '72'])).
% 4.76/4.93  thf('74', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i]:
% 4.76/4.93         (((k1_xboole_0) != (k1_xboole_0))
% 4.76/4.93          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 4.76/4.93      inference('sup-', [status(thm)], ['70', '73'])).
% 4.76/4.93  thf('75', plain,
% 4.76/4.93      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 4.76/4.93      inference('simplify', [status(thm)], ['74'])).
% 4.76/4.93  thf('76', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 4.76/4.93      inference('sup+', [status(thm)], ['61', '75'])).
% 4.76/4.93  thf('77', plain, ($false), inference('demod', [status(thm)], ['13', '76'])).
% 4.76/4.93  
% 4.76/4.93  % SZS output end Refutation
% 4.76/4.93  
% 4.76/4.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
