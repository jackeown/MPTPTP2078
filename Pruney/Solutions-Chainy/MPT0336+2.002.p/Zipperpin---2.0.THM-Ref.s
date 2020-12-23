%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uWGFxsYdLV

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:20 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 179 expanded)
%              Number of leaves         :   27 (  67 expanded)
%              Depth                    :   18
%              Number of atoms          :  697 (1216 expanded)
%              Number of equality atoms :   64 (  98 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
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

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('11',plain,(
    ! [X25: $i] :
      ( r1_xboole_0 @ X25 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X28 @ X29 )
        = X28 )
      | ~ ( r1_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X25: $i] :
      ( r1_xboole_0 @ X25 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X28 @ X29 )
        = X28 )
      | ~ ( r1_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','24'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','29'])).

thf('31',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup+',[status(thm)],['9','30'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('32',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k4_xboole_0 @ X40 @ ( k1_tarski @ X41 ) )
        = X40 )
      | ( r2_hidden @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('33',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('39',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X28 @ X29 )
        = X28 )
      | ~ ( r1_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('42',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('48',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['33','50'])).

thf('52',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_xboole_0 @ X31 @ X32 )
      = ( k5_xboole_0 @ X31 @ ( k4_xboole_0 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('56',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55','60'])).

thf('62',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('64',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_xboole_0 @ X31 @ X32 )
      = ( k5_xboole_0 @ X31 @ ( k4_xboole_0 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('67',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','71'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf('74',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_xboole_0 @ X28 @ X30 )
      | ( ( k4_xboole_0 @ X28 @ X30 )
       != X28 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
       != sk_B )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_B != sk_B )
    | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('81',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['2','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uWGFxsYdLV
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.85/1.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.85/1.07  % Solved by: fo/fo7.sh
% 0.85/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.07  % done 2189 iterations in 0.622s
% 0.85/1.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.85/1.07  % SZS output start Refutation
% 0.85/1.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.85/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.85/1.07  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.85/1.07  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.85/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.07  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.85/1.07  thf(sk_D_type, type, sk_D: $i).
% 0.85/1.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.85/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.85/1.07  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.85/1.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.85/1.07  thf(sk_B_type, type, sk_B: $i).
% 0.85/1.07  thf(t149_zfmisc_1, conjecture,
% 0.85/1.07    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.07     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.85/1.07         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.85/1.07       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.85/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.07    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.07        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.85/1.07            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.85/1.07          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.85/1.07    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.85/1.07  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.07  thf(commutativity_k2_xboole_0, axiom,
% 0.85/1.07    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.85/1.07  thf('1', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.85/1.07      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.85/1.07  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 0.85/1.07      inference('demod', [status(thm)], ['0', '1'])).
% 0.85/1.07  thf('3', plain,
% 0.85/1.07      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.07  thf(commutativity_k3_xboole_0, axiom,
% 0.85/1.07    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.85/1.07  thf('4', plain,
% 0.85/1.07      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.85/1.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.85/1.07  thf('5', plain,
% 0.85/1.07      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.85/1.07      inference('demod', [status(thm)], ['3', '4'])).
% 0.85/1.07  thf(t12_xboole_1, axiom,
% 0.85/1.07    (![A:$i,B:$i]:
% 0.85/1.07     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.85/1.07  thf('6', plain,
% 0.85/1.07      (![X16 : $i, X17 : $i]:
% 0.85/1.07         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 0.85/1.07      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.85/1.07  thf('7', plain,
% 0.85/1.07      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 0.85/1.07         = (k1_tarski @ sk_D))),
% 0.85/1.07      inference('sup-', [status(thm)], ['5', '6'])).
% 0.85/1.07  thf('8', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.85/1.07      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.85/1.07  thf('9', plain,
% 0.85/1.07      (((k2_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.85/1.07         = (k1_tarski @ sk_D))),
% 0.85/1.07      inference('demod', [status(thm)], ['7', '8'])).
% 0.85/1.07  thf('10', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.85/1.07      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.85/1.07  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.85/1.07  thf('11', plain, (![X25 : $i]: (r1_xboole_0 @ X25 @ k1_xboole_0)),
% 0.85/1.07      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.85/1.07  thf(t83_xboole_1, axiom,
% 0.85/1.07    (![A:$i,B:$i]:
% 0.85/1.07     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.85/1.07  thf('12', plain,
% 0.85/1.07      (![X28 : $i, X29 : $i]:
% 0.85/1.07         (((k4_xboole_0 @ X28 @ X29) = (X28)) | ~ (r1_xboole_0 @ X28 @ X29))),
% 0.85/1.07      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.85/1.07  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.85/1.07      inference('sup-', [status(thm)], ['11', '12'])).
% 0.85/1.07  thf(t48_xboole_1, axiom,
% 0.85/1.07    (![A:$i,B:$i]:
% 0.85/1.07     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.85/1.07  thf('14', plain,
% 0.85/1.07      (![X23 : $i, X24 : $i]:
% 0.85/1.07         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.85/1.07           = (k3_xboole_0 @ X23 @ X24))),
% 0.85/1.07      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.85/1.07  thf('15', plain,
% 0.85/1.07      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.85/1.07      inference('sup+', [status(thm)], ['13', '14'])).
% 0.85/1.07  thf('16', plain, (![X25 : $i]: (r1_xboole_0 @ X25 @ k1_xboole_0)),
% 0.85/1.07      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.85/1.07  thf(symmetry_r1_xboole_0, axiom,
% 0.85/1.07    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.85/1.07  thf('17', plain,
% 0.85/1.07      (![X4 : $i, X5 : $i]:
% 0.85/1.07         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.85/1.07      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.85/1.07  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.85/1.07      inference('sup-', [status(thm)], ['16', '17'])).
% 0.85/1.07  thf('19', plain,
% 0.85/1.07      (![X28 : $i, X29 : $i]:
% 0.85/1.07         (((k4_xboole_0 @ X28 @ X29) = (X28)) | ~ (r1_xboole_0 @ X28 @ X29))),
% 0.85/1.07      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.85/1.07  thf('20', plain,
% 0.85/1.07      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.85/1.07      inference('sup-', [status(thm)], ['18', '19'])).
% 0.85/1.07  thf('21', plain,
% 0.85/1.07      (![X23 : $i, X24 : $i]:
% 0.85/1.07         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.85/1.07           = (k3_xboole_0 @ X23 @ X24))),
% 0.85/1.07      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.85/1.07  thf('22', plain,
% 0.85/1.07      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.85/1.07      inference('sup+', [status(thm)], ['20', '21'])).
% 0.85/1.07  thf('23', plain,
% 0.85/1.07      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.85/1.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.85/1.07  thf('24', plain,
% 0.85/1.07      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.85/1.07      inference('sup+', [status(thm)], ['22', '23'])).
% 0.85/1.07  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.85/1.07      inference('demod', [status(thm)], ['15', '24'])).
% 0.85/1.07  thf(t41_xboole_1, axiom,
% 0.85/1.07    (![A:$i,B:$i,C:$i]:
% 0.85/1.07     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.85/1.07       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.85/1.07  thf('26', plain,
% 0.85/1.07      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.85/1.07         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 0.85/1.07           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 0.85/1.07      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.85/1.07  thf('27', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i]:
% 0.85/1.07         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.85/1.07           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.85/1.07      inference('sup+', [status(thm)], ['25', '26'])).
% 0.85/1.07  thf('28', plain,
% 0.85/1.07      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.85/1.07      inference('sup-', [status(thm)], ['18', '19'])).
% 0.85/1.07  thf('29', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i]:
% 0.85/1.07         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.85/1.07      inference('demod', [status(thm)], ['27', '28'])).
% 0.85/1.07  thf('30', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i]:
% 0.85/1.07         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.85/1.07      inference('sup+', [status(thm)], ['10', '29'])).
% 0.85/1.07  thf('31', plain,
% 0.85/1.07      (((k1_xboole_0)
% 0.85/1.07         = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D)))),
% 0.85/1.07      inference('sup+', [status(thm)], ['9', '30'])).
% 0.85/1.07  thf(t65_zfmisc_1, axiom,
% 0.85/1.07    (![A:$i,B:$i]:
% 0.85/1.07     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.85/1.07       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.85/1.07  thf('32', plain,
% 0.85/1.07      (![X40 : $i, X41 : $i]:
% 0.85/1.07         (((k4_xboole_0 @ X40 @ (k1_tarski @ X41)) = (X40))
% 0.85/1.07          | (r2_hidden @ X41 @ X40))),
% 0.85/1.07      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.85/1.07  thf('33', plain,
% 0.85/1.07      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.85/1.07        | (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.85/1.07      inference('sup+', [status(thm)], ['31', '32'])).
% 0.85/1.07  thf('34', plain,
% 0.85/1.07      (![X23 : $i, X24 : $i]:
% 0.85/1.07         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.85/1.07           = (k3_xboole_0 @ X23 @ X24))),
% 0.85/1.07      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.85/1.07  thf(t36_xboole_1, axiom,
% 0.85/1.07    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.85/1.07  thf('35', plain,
% 0.85/1.07      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.85/1.07      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.85/1.07  thf('36', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.85/1.07      inference('sup+', [status(thm)], ['34', '35'])).
% 0.85/1.07  thf('37', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.07  thf('38', plain,
% 0.85/1.07      (![X4 : $i, X5 : $i]:
% 0.85/1.07         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.85/1.07      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.85/1.07  thf('39', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.85/1.07      inference('sup-', [status(thm)], ['37', '38'])).
% 0.85/1.07  thf('40', plain,
% 0.85/1.07      (![X28 : $i, X29 : $i]:
% 0.85/1.07         (((k4_xboole_0 @ X28 @ X29) = (X28)) | ~ (r1_xboole_0 @ X28 @ X29))),
% 0.85/1.07      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.85/1.07  thf('41', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 0.85/1.07      inference('sup-', [status(thm)], ['39', '40'])).
% 0.85/1.07  thf(t106_xboole_1, axiom,
% 0.85/1.07    (![A:$i,B:$i,C:$i]:
% 0.85/1.07     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.85/1.08       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.85/1.08  thf('42', plain,
% 0.85/1.08      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.85/1.08         ((r1_xboole_0 @ X13 @ X15)
% 0.85/1.08          | ~ (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X15)))),
% 0.85/1.08      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.85/1.08  thf('43', plain,
% 0.85/1.08      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ sk_C_1))),
% 0.85/1.08      inference('sup-', [status(thm)], ['41', '42'])).
% 0.85/1.08  thf('44', plain,
% 0.85/1.08      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C_1)),
% 0.85/1.08      inference('sup-', [status(thm)], ['36', '43'])).
% 0.85/1.08  thf('45', plain,
% 0.85/1.08      (![X4 : $i, X5 : $i]:
% 0.85/1.08         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.85/1.08      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.85/1.08  thf('46', plain,
% 0.85/1.08      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0))),
% 0.85/1.08      inference('sup-', [status(thm)], ['44', '45'])).
% 0.85/1.08  thf('47', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 0.85/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.08  thf(t3_xboole_0, axiom,
% 0.85/1.08    (![A:$i,B:$i]:
% 0.85/1.08     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.85/1.08            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.85/1.08       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.85/1.08            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.85/1.08  thf('48', plain,
% 0.85/1.08      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.85/1.08         (~ (r2_hidden @ X8 @ X6)
% 0.85/1.08          | ~ (r2_hidden @ X8 @ X9)
% 0.85/1.08          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.85/1.08      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.85/1.08  thf('49', plain,
% 0.85/1.08      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 0.85/1.08      inference('sup-', [status(thm)], ['47', '48'])).
% 0.85/1.08  thf('50', plain,
% 0.85/1.08      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 0.85/1.08      inference('sup-', [status(thm)], ['46', '49'])).
% 0.85/1.08  thf('51', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.85/1.08      inference('clc', [status(thm)], ['33', '50'])).
% 0.85/1.08  thf('52', plain,
% 0.85/1.08      (![X23 : $i, X24 : $i]:
% 0.85/1.08         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.85/1.08           = (k3_xboole_0 @ X23 @ X24))),
% 0.85/1.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.85/1.08  thf(t98_xboole_1, axiom,
% 0.85/1.08    (![A:$i,B:$i]:
% 0.85/1.08     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.85/1.08  thf('53', plain,
% 0.85/1.08      (![X31 : $i, X32 : $i]:
% 0.85/1.08         ((k2_xboole_0 @ X31 @ X32)
% 0.85/1.08           = (k5_xboole_0 @ X31 @ (k4_xboole_0 @ X32 @ X31)))),
% 0.85/1.08      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.85/1.08  thf('54', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.85/1.08           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.85/1.08      inference('sup+', [status(thm)], ['52', '53'])).
% 0.85/1.08  thf('55', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.85/1.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.85/1.08  thf('56', plain,
% 0.85/1.08      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.85/1.08      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.85/1.08  thf('57', plain,
% 0.85/1.08      (![X16 : $i, X17 : $i]:
% 0.85/1.08         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 0.85/1.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.85/1.08  thf('58', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.85/1.08      inference('sup-', [status(thm)], ['56', '57'])).
% 0.85/1.08  thf('59', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.85/1.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.85/1.08  thf('60', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.85/1.08      inference('demod', [status(thm)], ['58', '59'])).
% 0.85/1.08  thf('61', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         ((X1)
% 0.85/1.08           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.85/1.08      inference('demod', [status(thm)], ['54', '55', '60'])).
% 0.85/1.08  thf('62', plain,
% 0.85/1.08      (((sk_B) = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ k1_xboole_0))),
% 0.85/1.08      inference('sup+', [status(thm)], ['51', '61'])).
% 0.85/1.08  thf('63', plain,
% 0.85/1.08      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.85/1.08      inference('sup-', [status(thm)], ['18', '19'])).
% 0.85/1.08  thf('64', plain,
% 0.85/1.08      (![X31 : $i, X32 : $i]:
% 0.85/1.08         ((k2_xboole_0 @ X31 @ X32)
% 0.85/1.08           = (k5_xboole_0 @ X31 @ (k4_xboole_0 @ X32 @ X31)))),
% 0.85/1.08      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.85/1.08  thf('65', plain,
% 0.85/1.08      (![X0 : $i]:
% 0.85/1.08         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.85/1.08      inference('sup+', [status(thm)], ['63', '64'])).
% 0.85/1.08  thf('66', plain,
% 0.85/1.08      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.85/1.08      inference('sup+', [status(thm)], ['22', '23'])).
% 0.85/1.08  thf('67', plain,
% 0.85/1.08      (![X23 : $i, X24 : $i]:
% 0.85/1.08         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.85/1.08           = (k3_xboole_0 @ X23 @ X24))),
% 0.85/1.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.85/1.08  thf('68', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.85/1.08      inference('demod', [status(thm)], ['58', '59'])).
% 0.85/1.08  thf('69', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.85/1.08      inference('sup+', [status(thm)], ['67', '68'])).
% 0.85/1.08  thf('70', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.85/1.08      inference('sup+', [status(thm)], ['66', '69'])).
% 0.85/1.08  thf('71', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.85/1.08      inference('sup+', [status(thm)], ['65', '70'])).
% 0.85/1.08  thf('72', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.85/1.08      inference('demod', [status(thm)], ['62', '71'])).
% 0.85/1.08  thf('73', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 0.85/1.08      inference('sup-', [status(thm)], ['39', '40'])).
% 0.85/1.08  thf('74', plain,
% 0.85/1.08      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.85/1.08         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 0.85/1.08           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 0.85/1.08      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.85/1.08  thf('75', plain,
% 0.85/1.08      (![X0 : $i]:
% 0.85/1.08         ((k4_xboole_0 @ sk_B @ X0)
% 0.85/1.08           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 0.85/1.08      inference('sup+', [status(thm)], ['73', '74'])).
% 0.85/1.08  thf('76', plain,
% 0.85/1.08      (![X28 : $i, X30 : $i]:
% 0.85/1.08         ((r1_xboole_0 @ X28 @ X30) | ((k4_xboole_0 @ X28 @ X30) != (X28)))),
% 0.85/1.08      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.85/1.08  thf('77', plain,
% 0.85/1.08      (![X0 : $i]:
% 0.85/1.08         (((k4_xboole_0 @ sk_B @ X0) != (sk_B))
% 0.85/1.08          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 0.85/1.08      inference('sup-', [status(thm)], ['75', '76'])).
% 0.85/1.08  thf('78', plain,
% 0.85/1.08      ((((sk_B) != (sk_B))
% 0.85/1.08        | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.85/1.08      inference('sup-', [status(thm)], ['72', '77'])).
% 0.85/1.08  thf('79', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 0.85/1.08      inference('simplify', [status(thm)], ['78'])).
% 0.85/1.08  thf('80', plain,
% 0.85/1.08      (![X4 : $i, X5 : $i]:
% 0.85/1.08         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.85/1.08      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.85/1.08  thf('81', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 0.85/1.08      inference('sup-', [status(thm)], ['79', '80'])).
% 0.85/1.08  thf('82', plain, ($false), inference('demod', [status(thm)], ['2', '81'])).
% 0.85/1.08  
% 0.85/1.08  % SZS output end Refutation
% 0.85/1.08  
% 0.92/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
