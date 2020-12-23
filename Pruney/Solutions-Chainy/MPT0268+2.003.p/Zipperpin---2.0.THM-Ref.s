%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MkFRX7Tnwl

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:52 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 247 expanded)
%              Number of leaves         :   26 (  79 expanded)
%              Depth                    :   15
%              Number of atoms          :  763 (2029 expanded)
%              Number of equality atoms :   91 ( 237 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('10',plain,(
    ! [X57: $i,X59: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X57 ) @ X59 )
      | ~ ( r2_hidden @ X57 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('11',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('14',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('16',plain,(
    ! [X65: $i,X66: $i] :
      ( ( X66 != X65 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X66 ) @ ( k1_tarski @ X65 ) )
       != ( k1_tarski @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('17',plain,(
    ! [X65: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X65 ) @ ( k1_tarski @ X65 ) )
     != ( k1_tarski @ X65 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('20',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','21'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('28',plain,(
    ! [X60: $i,X62: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X60 ) @ X62 )
        = ( k1_tarski @ X60 ) )
      | ( r2_hidden @ X60 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('51',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ k1_xboole_0 )
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','62'])).

thf('64',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('67',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('68',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','25','67'])).

thf('69',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['66','68'])).

thf('70',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['27','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MkFRX7Tnwl
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.83/1.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.02  % Solved by: fo/fo7.sh
% 0.83/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.02  % done 1178 iterations in 0.571s
% 0.83/1.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.02  % SZS output start Refutation
% 0.83/1.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.83/1.02  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.83/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.83/1.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.83/1.02  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.83/1.02  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.83/1.02  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.83/1.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.02  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.83/1.02  thf(t65_zfmisc_1, conjecture,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.83/1.02       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.83/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.02    (~( ![A:$i,B:$i]:
% 0.83/1.02        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.83/1.02          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.83/1.02    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.83/1.02  thf('0', plain,
% 0.83/1.02      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.83/1.02        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.83/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.02  thf('1', plain,
% 0.83/1.02      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.83/1.02      inference('split', [status(esa)], ['0'])).
% 0.83/1.02  thf('2', plain,
% 0.83/1.02      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.83/1.02       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.83/1.02      inference('split', [status(esa)], ['0'])).
% 0.83/1.02  thf(t100_xboole_1, axiom,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.83/1.02  thf('3', plain,
% 0.83/1.02      (![X4 : $i, X5 : $i]:
% 0.83/1.02         ((k4_xboole_0 @ X4 @ X5)
% 0.83/1.02           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.83/1.02  thf(commutativity_k5_xboole_0, axiom,
% 0.83/1.02    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.83/1.02  thf('4', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.83/1.02  thf(t5_boole, axiom,
% 0.83/1.02    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.83/1.02  thf('5', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.83/1.02      inference('cnf', [status(esa)], [t5_boole])).
% 0.83/1.02  thf('6', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.83/1.02      inference('sup+', [status(thm)], ['4', '5'])).
% 0.83/1.02  thf('7', plain,
% 0.83/1.02      (![X0 : $i]:
% 0.83/1.02         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.83/1.02      inference('sup+', [status(thm)], ['3', '6'])).
% 0.83/1.02  thf('8', plain,
% 0.83/1.02      (((r2_hidden @ sk_B @ sk_A)
% 0.83/1.02        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.83/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.02  thf('9', plain,
% 0.83/1.02      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.83/1.02      inference('split', [status(esa)], ['8'])).
% 0.83/1.02  thf(l1_zfmisc_1, axiom,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.83/1.02  thf('10', plain,
% 0.83/1.02      (![X57 : $i, X59 : $i]:
% 0.83/1.02         ((r1_tarski @ (k1_tarski @ X57) @ X59) | ~ (r2_hidden @ X57 @ X59))),
% 0.83/1.02      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.83/1.02  thf('11', plain,
% 0.83/1.02      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_A))
% 0.83/1.02         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.83/1.02      inference('sup-', [status(thm)], ['9', '10'])).
% 0.83/1.02  thf('12', plain,
% 0.83/1.02      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.83/1.02         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.83/1.02      inference('split', [status(esa)], ['0'])).
% 0.83/1.02  thf(t38_xboole_1, axiom,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.83/1.02       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.83/1.02  thf('13', plain,
% 0.83/1.02      (![X8 : $i, X9 : $i]:
% 0.83/1.02         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.83/1.02  thf('14', plain,
% 0.83/1.02      (((~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.83/1.02         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.83/1.02         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.83/1.02      inference('sup-', [status(thm)], ['12', '13'])).
% 0.83/1.02  thf('15', plain,
% 0.83/1.02      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.83/1.02         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.83/1.02             ((r2_hidden @ sk_B @ sk_A)))),
% 0.83/1.02      inference('sup-', [status(thm)], ['11', '14'])).
% 0.83/1.02  thf(t20_zfmisc_1, axiom,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.83/1.02         ( k1_tarski @ A ) ) <=>
% 0.83/1.02       ( ( A ) != ( B ) ) ))).
% 0.83/1.02  thf('16', plain,
% 0.83/1.02      (![X65 : $i, X66 : $i]:
% 0.83/1.02         (((X66) != (X65))
% 0.83/1.02          | ((k4_xboole_0 @ (k1_tarski @ X66) @ (k1_tarski @ X65))
% 0.83/1.02              != (k1_tarski @ X66)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.83/1.02  thf('17', plain,
% 0.83/1.02      (![X65 : $i]:
% 0.83/1.02         ((k4_xboole_0 @ (k1_tarski @ X65) @ (k1_tarski @ X65))
% 0.83/1.02           != (k1_tarski @ X65))),
% 0.83/1.02      inference('simplify', [status(thm)], ['16'])).
% 0.83/1.02  thf('18', plain,
% 0.83/1.02      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B)))
% 0.83/1.02         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.83/1.02             ((r2_hidden @ sk_B @ sk_A)))),
% 0.83/1.02      inference('sup-', [status(thm)], ['15', '17'])).
% 0.83/1.02  thf('19', plain,
% 0.83/1.02      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.83/1.02         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.83/1.02             ((r2_hidden @ sk_B @ sk_A)))),
% 0.83/1.02      inference('sup-', [status(thm)], ['11', '14'])).
% 0.83/1.02  thf('20', plain,
% 0.83/1.02      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.83/1.02         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.83/1.02             ((r2_hidden @ sk_B @ sk_A)))),
% 0.83/1.02      inference('sup-', [status(thm)], ['11', '14'])).
% 0.83/1.02  thf('21', plain,
% 0.83/1.02      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.83/1.02         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.83/1.02             ((r2_hidden @ sk_B @ sk_A)))),
% 0.83/1.02      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.83/1.02  thf('22', plain,
% 0.83/1.02      ((((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.83/1.02         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.83/1.02             ((r2_hidden @ sk_B @ sk_A)))),
% 0.83/1.02      inference('sup-', [status(thm)], ['7', '21'])).
% 0.83/1.02  thf(idempotence_k3_xboole_0, axiom,
% 0.83/1.02    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.83/1.02  thf('23', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.83/1.02      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.83/1.02  thf('24', plain,
% 0.83/1.02      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.83/1.02         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.83/1.02             ((r2_hidden @ sk_B @ sk_A)))),
% 0.83/1.02      inference('demod', [status(thm)], ['22', '23'])).
% 0.83/1.02  thf('25', plain,
% 0.83/1.02      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.83/1.02       ~ ((r2_hidden @ sk_B @ sk_A))),
% 0.83/1.02      inference('simplify', [status(thm)], ['24'])).
% 0.83/1.02  thf('26', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 0.83/1.02      inference('sat_resolution*', [status(thm)], ['2', '25'])).
% 0.83/1.02  thf('27', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.83/1.02      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.83/1.02  thf(l33_zfmisc_1, axiom,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.83/1.02       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.83/1.02  thf('28', plain,
% 0.83/1.02      (![X60 : $i, X62 : $i]:
% 0.83/1.02         (((k4_xboole_0 @ (k1_tarski @ X60) @ X62) = (k1_tarski @ X60))
% 0.83/1.02          | (r2_hidden @ X60 @ X62))),
% 0.83/1.02      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.83/1.02  thf('29', plain,
% 0.83/1.02      (![X4 : $i, X5 : $i]:
% 0.83/1.02         ((k4_xboole_0 @ X4 @ X5)
% 0.83/1.02           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.83/1.02  thf(t92_xboole_1, axiom,
% 0.83/1.02    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.83/1.02  thf('30', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.83/1.02      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.83/1.02  thf(t91_xboole_1, axiom,
% 0.83/1.02    (![A:$i,B:$i,C:$i]:
% 0.83/1.02     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.83/1.02       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.83/1.02  thf('31', plain,
% 0.83/1.02      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.83/1.02         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.83/1.02           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.83/1.02  thf('32', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.83/1.02           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.02      inference('sup+', [status(thm)], ['30', '31'])).
% 0.83/1.02  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.83/1.02      inference('sup+', [status(thm)], ['4', '5'])).
% 0.83/1.02  thf('34', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.02      inference('demod', [status(thm)], ['32', '33'])).
% 0.83/1.02  thf('35', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k3_xboole_0 @ X1 @ X0)
% 0.83/1.02           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.83/1.02      inference('sup+', [status(thm)], ['29', '34'])).
% 0.83/1.02  thf('36', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.83/1.02            = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 0.83/1.02          | (r2_hidden @ X0 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['28', '35'])).
% 0.83/1.02  thf('37', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.83/1.02      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.83/1.02  thf('38', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.83/1.02          | (r2_hidden @ X0 @ X1))),
% 0.83/1.02      inference('demod', [status(thm)], ['36', '37'])).
% 0.83/1.02  thf('39', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.83/1.02  thf('40', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.02      inference('demod', [status(thm)], ['32', '33'])).
% 0.83/1.02  thf('41', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.02      inference('sup+', [status(thm)], ['39', '40'])).
% 0.83/1.02  thf(t95_xboole_1, axiom,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( k3_xboole_0 @ A @ B ) =
% 0.83/1.02       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.83/1.02  thf('42', plain,
% 0.83/1.02      (![X17 : $i, X18 : $i]:
% 0.83/1.02         ((k3_xboole_0 @ X17 @ X18)
% 0.83/1.02           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.83/1.02              (k2_xboole_0 @ X17 @ X18)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.83/1.02  thf('43', plain,
% 0.83/1.02      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.83/1.02         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.83/1.02           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.83/1.02  thf('44', plain,
% 0.83/1.02      (![X17 : $i, X18 : $i]:
% 0.83/1.02         ((k3_xboole_0 @ X17 @ X18)
% 0.83/1.02           = (k5_xboole_0 @ X17 @ 
% 0.83/1.02              (k5_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X18))))),
% 0.83/1.02      inference('demod', [status(thm)], ['42', '43'])).
% 0.83/1.02  thf('45', plain,
% 0.83/1.02      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.83/1.02         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.83/1.02           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.83/1.02  thf('46', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.02         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.83/1.02           = (k5_xboole_0 @ X1 @ 
% 0.83/1.02              (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ X2)))),
% 0.83/1.02      inference('sup+', [status(thm)], ['44', '45'])).
% 0.83/1.02  thf('47', plain,
% 0.83/1.02      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.83/1.02         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.83/1.02           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.83/1.02  thf('48', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.02         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.83/1.02           = (k5_xboole_0 @ X1 @ 
% 0.83/1.02              (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))))),
% 0.83/1.02      inference('demod', [status(thm)], ['46', '47'])).
% 0.83/1.02  thf('49', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.83/1.02           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.83/1.02      inference('sup+', [status(thm)], ['41', '48'])).
% 0.83/1.02  thf('50', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.83/1.02  thf(commutativity_k2_tarski, axiom,
% 0.83/1.02    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.83/1.02  thf('51', plain,
% 0.83/1.02      (![X19 : $i, X20 : $i]:
% 0.83/1.02         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 0.83/1.02      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.83/1.02  thf(l51_zfmisc_1, axiom,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.83/1.02  thf('52', plain,
% 0.83/1.02      (![X63 : $i, X64 : $i]:
% 0.83/1.02         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 0.83/1.02      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.83/1.02  thf('53', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['51', '52'])).
% 0.83/1.02  thf('54', plain,
% 0.83/1.02      (![X63 : $i, X64 : $i]:
% 0.83/1.02         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 0.83/1.02      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.83/1.02  thf('55', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['53', '54'])).
% 0.83/1.02  thf('56', plain,
% 0.83/1.02      (![X17 : $i, X18 : $i]:
% 0.83/1.02         ((k3_xboole_0 @ X17 @ X18)
% 0.83/1.02           = (k5_xboole_0 @ X17 @ 
% 0.83/1.02              (k5_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X18))))),
% 0.83/1.02      inference('demod', [status(thm)], ['42', '43'])).
% 0.83/1.02  thf('57', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.02      inference('demod', [status(thm)], ['32', '33'])).
% 0.83/1.02  thf('58', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.83/1.02           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.83/1.02      inference('sup+', [status(thm)], ['56', '57'])).
% 0.83/1.02  thf('59', plain,
% 0.83/1.02      (![X4 : $i, X5 : $i]:
% 0.83/1.02         ((k4_xboole_0 @ X4 @ X5)
% 0.83/1.02           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.83/1.02  thf('60', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.83/1.02           = (k4_xboole_0 @ X1 @ X0))),
% 0.83/1.02      inference('demod', [status(thm)], ['58', '59'])).
% 0.83/1.02  thf('61', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.83/1.02           = (k4_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['55', '60'])).
% 0.83/1.02  thf('62', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.83/1.02           = (k4_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('demod', [status(thm)], ['49', '50', '61'])).
% 0.83/1.02  thf('63', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         (((k5_xboole_0 @ X1 @ k1_xboole_0)
% 0.83/1.02            = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.83/1.02          | (r2_hidden @ X0 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['38', '62'])).
% 0.83/1.02  thf('64', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.83/1.02      inference('cnf', [status(esa)], [t5_boole])).
% 0.83/1.02  thf('65', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.83/1.02          | (r2_hidden @ X0 @ X1))),
% 0.83/1.02      inference('demod', [status(thm)], ['63', '64'])).
% 0.83/1.02  thf('66', plain,
% 0.83/1.02      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.83/1.02         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.83/1.02      inference('split', [status(esa)], ['8'])).
% 0.83/1.02  thf('67', plain,
% 0.83/1.02      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.83/1.02       ((r2_hidden @ sk_B @ sk_A))),
% 0.83/1.02      inference('split', [status(esa)], ['8'])).
% 0.83/1.02  thf('68', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.83/1.02      inference('sat_resolution*', [status(thm)], ['2', '25', '67'])).
% 0.83/1.02  thf('69', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 0.83/1.02      inference('simpl_trail', [status(thm)], ['66', '68'])).
% 0.83/1.02  thf('70', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.83/1.02      inference('sup-', [status(thm)], ['65', '69'])).
% 0.83/1.02  thf('71', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.83/1.02      inference('simplify', [status(thm)], ['70'])).
% 0.83/1.02  thf('72', plain, ($false), inference('demod', [status(thm)], ['27', '71'])).
% 0.83/1.02  
% 0.83/1.02  % SZS output end Refutation
% 0.83/1.02  
% 0.83/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
