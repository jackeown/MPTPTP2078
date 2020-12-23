%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Rmli07Wcjt

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:42 EST 2020

% Result     : Theorem 33.94s
% Output     : Refutation 33.94s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 428 expanded)
%              Number of leaves         :   24 ( 135 expanded)
%              Depth                    :   25
%              Number of atoms          : 1295 (3766 expanded)
%              Number of equality atoms :   98 ( 259 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ ( k3_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('3',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('10',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','23'])).

thf('25',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['2','24'])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('27',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k3_xboole_0 @ X6 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('40',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 )
      | ( r1_xboole_0 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_A @ X0 )
        | ~ ( r1_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,(
    ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['30','44','45'])).

thf('47',plain,(
    ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('48',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ ( k3_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('49',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('50',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('58',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('64',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('66',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('71',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
      = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('75',plain,
    ( ( r1_xboole_0 @ ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('78',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('79',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','86'])).

thf('88',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('89',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['76','92'])).

thf('94',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 )
      | ( r1_xboole_0 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) @ X0 ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['68'])).

thf('100',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['30','44','45','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['98','100'])).

thf('102',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('105',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k3_xboole_0 @ X6 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','108'])).

thf('110',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['62','111'])).

thf('113',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('114',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('115',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('117',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('119',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('121',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['30','44','45','120'])).

thf('122',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['119','121'])).

thf('123',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['112','122'])).

thf('124',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('125',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    $false ),
    inference(demod,[status(thm)],['47','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Rmli07Wcjt
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 33.94/34.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 33.94/34.13  % Solved by: fo/fo7.sh
% 33.94/34.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 33.94/34.13  % done 16504 iterations in 33.667s
% 33.94/34.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 33.94/34.13  % SZS output start Refutation
% 33.94/34.13  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 33.94/34.13  thf(sk_B_type, type, sk_B: $i).
% 33.94/34.13  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 33.94/34.13  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 33.94/34.13  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 33.94/34.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 33.94/34.13  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 33.94/34.13  thf(sk_A_type, type, sk_A: $i).
% 33.94/34.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 33.94/34.13  thf(sk_C_type, type, sk_C: $i).
% 33.94/34.13  thf(t107_xboole_1, conjecture,
% 33.94/34.13    (![A:$i,B:$i,C:$i]:
% 33.94/34.13     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 33.94/34.13       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 33.94/34.13         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 33.94/34.13  thf(zf_stmt_0, negated_conjecture,
% 33.94/34.13    (~( ![A:$i,B:$i,C:$i]:
% 33.94/34.13        ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 33.94/34.13          ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 33.94/34.13            ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 33.94/34.13    inference('cnf.neg', [status(esa)], [t107_xboole_1])).
% 33.94/34.13  thf('0', plain,
% 33.94/34.13      ((~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 33.94/34.13        | ~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 33.94/34.13        | ~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 33.94/34.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.94/34.13  thf('1', plain,
% 33.94/34.13      ((~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 33.94/34.13         <= (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('split', [status(esa)], ['0'])).
% 33.94/34.13  thf(t93_xboole_1, axiom,
% 33.94/34.13    (![A:$i,B:$i]:
% 33.94/34.13     ( ( k2_xboole_0 @ A @ B ) =
% 33.94/34.13       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 33.94/34.13  thf('2', plain,
% 33.94/34.13      (![X29 : $i, X30 : $i]:
% 33.94/34.13         ((k2_xboole_0 @ X29 @ X30)
% 33.94/34.13           = (k2_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ 
% 33.94/34.13              (k3_xboole_0 @ X29 @ X30)))),
% 33.94/34.13      inference('cnf', [status(esa)], [t93_xboole_1])).
% 33.94/34.13  thf('3', plain,
% 33.94/34.13      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 33.94/34.13        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 33.94/34.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.94/34.13  thf('4', plain,
% 33.94/34.13      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 33.94/34.13         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('split', [status(esa)], ['3'])).
% 33.94/34.13  thf(l32_xboole_1, axiom,
% 33.94/34.13    (![A:$i,B:$i]:
% 33.94/34.13     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 33.94/34.13  thf('5', plain,
% 33.94/34.13      (![X9 : $i, X11 : $i]:
% 33.94/34.13         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 33.94/34.13      inference('cnf', [status(esa)], [l32_xboole_1])).
% 33.94/34.13  thf('6', plain,
% 33.94/34.13      ((((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 33.94/34.13         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('sup-', [status(thm)], ['4', '5'])).
% 33.94/34.13  thf(t41_xboole_1, axiom,
% 33.94/34.13    (![A:$i,B:$i,C:$i]:
% 33.94/34.13     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 33.94/34.13       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 33.94/34.13  thf('7', plain,
% 33.94/34.13      (![X17 : $i, X18 : $i, X19 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 33.94/34.13           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 33.94/34.13      inference('cnf', [status(esa)], [t41_xboole_1])).
% 33.94/34.13  thf('8', plain,
% 33.94/34.13      ((![X0 : $i]:
% 33.94/34.13          ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 33.94/34.13            = (k4_xboole_0 @ sk_A @ 
% 33.94/34.13               (k2_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_C) @ X0))))
% 33.94/34.13         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('sup+', [status(thm)], ['6', '7'])).
% 33.94/34.13  thf(t3_boole, axiom,
% 33.94/34.13    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 33.94/34.13  thf('9', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 33.94/34.13      inference('cnf', [status(esa)], [t3_boole])).
% 33.94/34.13  thf(t79_xboole_1, axiom,
% 33.94/34.13    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 33.94/34.13  thf('10', plain,
% 33.94/34.13      (![X27 : $i, X28 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ X28)),
% 33.94/34.13      inference('cnf', [status(esa)], [t79_xboole_1])).
% 33.94/34.13  thf('11', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 33.94/34.13      inference('sup+', [status(thm)], ['9', '10'])).
% 33.94/34.13  thf(d7_xboole_0, axiom,
% 33.94/34.13    (![A:$i,B:$i]:
% 33.94/34.13     ( ( r1_xboole_0 @ A @ B ) <=>
% 33.94/34.13       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 33.94/34.13  thf('12', plain,
% 33.94/34.13      (![X6 : $i, X7 : $i]:
% 33.94/34.13         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 33.94/34.13      inference('cnf', [status(esa)], [d7_xboole_0])).
% 33.94/34.13  thf('13', plain,
% 33.94/34.13      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 33.94/34.13      inference('sup-', [status(thm)], ['11', '12'])).
% 33.94/34.13  thf(commutativity_k3_xboole_0, axiom,
% 33.94/34.13    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 33.94/34.13  thf('14', plain,
% 33.94/34.13      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 33.94/34.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 33.94/34.13  thf('15', plain,
% 33.94/34.13      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 33.94/34.13      inference('sup+', [status(thm)], ['13', '14'])).
% 33.94/34.13  thf(t100_xboole_1, axiom,
% 33.94/34.13    (![A:$i,B:$i]:
% 33.94/34.13     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 33.94/34.13  thf('16', plain,
% 33.94/34.13      (![X14 : $i, X15 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X14 @ X15)
% 33.94/34.13           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 33.94/34.13      inference('cnf', [status(esa)], [t100_xboole_1])).
% 33.94/34.13  thf('17', plain,
% 33.94/34.13      (![X0 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 33.94/34.13           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 33.94/34.13      inference('sup+', [status(thm)], ['15', '16'])).
% 33.94/34.13  thf('18', plain,
% 33.94/34.13      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 33.94/34.13      inference('sup-', [status(thm)], ['11', '12'])).
% 33.94/34.13  thf('19', plain,
% 33.94/34.13      (![X14 : $i, X15 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X14 @ X15)
% 33.94/34.13           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 33.94/34.13      inference('cnf', [status(esa)], [t100_xboole_1])).
% 33.94/34.13  thf('20', plain,
% 33.94/34.13      (![X0 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 33.94/34.13      inference('sup+', [status(thm)], ['18', '19'])).
% 33.94/34.13  thf('21', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 33.94/34.13      inference('cnf', [status(esa)], [t3_boole])).
% 33.94/34.13  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 33.94/34.13      inference('sup+', [status(thm)], ['20', '21'])).
% 33.94/34.13  thf('23', plain,
% 33.94/34.13      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 33.94/34.13      inference('demod', [status(thm)], ['17', '22'])).
% 33.94/34.13  thf('24', plain,
% 33.94/34.13      ((![X0 : $i]:
% 33.94/34.13          ((k1_xboole_0)
% 33.94/34.13            = (k4_xboole_0 @ sk_A @ 
% 33.94/34.13               (k2_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_C) @ X0))))
% 33.94/34.13         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('demod', [status(thm)], ['8', '23'])).
% 33.94/34.13  thf('25', plain,
% 33.94/34.13      ((((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 33.94/34.13         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('sup+', [status(thm)], ['2', '24'])).
% 33.94/34.13  thf('26', plain,
% 33.94/34.13      (![X9 : $i, X10 : $i]:
% 33.94/34.13         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 33.94/34.13      inference('cnf', [status(esa)], [l32_xboole_1])).
% 33.94/34.13  thf('27', plain,
% 33.94/34.13      (((((k1_xboole_0) != (k1_xboole_0))
% 33.94/34.13         | (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 33.94/34.13         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('sup-', [status(thm)], ['25', '26'])).
% 33.94/34.13  thf('28', plain,
% 33.94/34.13      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 33.94/34.13         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('simplify', [status(thm)], ['27'])).
% 33.94/34.13  thf('29', plain,
% 33.94/34.13      ((~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 33.94/34.13         <= (~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('split', [status(esa)], ['0'])).
% 33.94/34.13  thf('30', plain,
% 33.94/34.13      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 33.94/34.13       ~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 33.94/34.13      inference('sup-', [status(thm)], ['28', '29'])).
% 33.94/34.13  thf(l97_xboole_1, axiom,
% 33.94/34.13    (![A:$i,B:$i]:
% 33.94/34.13     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 33.94/34.13  thf('31', plain,
% 33.94/34.13      (![X12 : $i, X13 : $i]:
% 33.94/34.13         (r1_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k5_xboole_0 @ X12 @ X13))),
% 33.94/34.13      inference('cnf', [status(esa)], [l97_xboole_1])).
% 33.94/34.13  thf('32', plain,
% 33.94/34.13      (![X6 : $i, X7 : $i]:
% 33.94/34.13         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 33.94/34.13      inference('cnf', [status(esa)], [d7_xboole_0])).
% 33.94/34.13  thf('33', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i]:
% 33.94/34.13         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 33.94/34.13           = (k1_xboole_0))),
% 33.94/34.13      inference('sup-', [status(thm)], ['31', '32'])).
% 33.94/34.13  thf('34', plain,
% 33.94/34.13      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 33.94/34.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 33.94/34.13  thf('35', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i]:
% 33.94/34.13         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 33.94/34.13           = (k1_xboole_0))),
% 33.94/34.13      inference('demod', [status(thm)], ['33', '34'])).
% 33.94/34.13  thf('36', plain,
% 33.94/34.13      (![X6 : $i, X8 : $i]:
% 33.94/34.13         ((r1_xboole_0 @ X6 @ X8) | ((k3_xboole_0 @ X6 @ X8) != (k1_xboole_0)))),
% 33.94/34.13      inference('cnf', [status(esa)], [d7_xboole_0])).
% 33.94/34.13  thf('37', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i]:
% 33.94/34.13         (((k1_xboole_0) != (k1_xboole_0))
% 33.94/34.13          | (r1_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 33.94/34.13      inference('sup-', [status(thm)], ['35', '36'])).
% 33.94/34.13  thf('38', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i]:
% 33.94/34.13         (r1_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))),
% 33.94/34.13      inference('simplify', [status(thm)], ['37'])).
% 33.94/34.13  thf('39', plain,
% 33.94/34.13      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 33.94/34.13         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('split', [status(esa)], ['3'])).
% 33.94/34.13  thf(t63_xboole_1, axiom,
% 33.94/34.13    (![A:$i,B:$i,C:$i]:
% 33.94/34.13     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 33.94/34.13       ( r1_xboole_0 @ A @ C ) ))).
% 33.94/34.13  thf('40', plain,
% 33.94/34.13      (![X24 : $i, X25 : $i, X26 : $i]:
% 33.94/34.13         (~ (r1_tarski @ X24 @ X25)
% 33.94/34.13          | ~ (r1_xboole_0 @ X25 @ X26)
% 33.94/34.13          | (r1_xboole_0 @ X24 @ X26))),
% 33.94/34.13      inference('cnf', [status(esa)], [t63_xboole_1])).
% 33.94/34.13  thf('41', plain,
% 33.94/34.13      ((![X0 : $i]:
% 33.94/34.13          ((r1_xboole_0 @ sk_A @ X0)
% 33.94/34.13           | ~ (r1_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_C) @ X0)))
% 33.94/34.13         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('sup-', [status(thm)], ['39', '40'])).
% 33.94/34.13  thf('42', plain,
% 33.94/34.13      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 33.94/34.13         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('sup-', [status(thm)], ['38', '41'])).
% 33.94/34.13  thf('43', plain,
% 33.94/34.13      ((~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 33.94/34.13         <= (~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('split', [status(esa)], ['0'])).
% 33.94/34.13  thf('44', plain,
% 33.94/34.13      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))) | 
% 33.94/34.13       ~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 33.94/34.13      inference('sup-', [status(thm)], ['42', '43'])).
% 33.94/34.13  thf('45', plain,
% 33.94/34.13      (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 33.94/34.13       ~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 33.94/34.13       ~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 33.94/34.13      inference('split', [status(esa)], ['0'])).
% 33.94/34.13  thf('46', plain, (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 33.94/34.13      inference('sat_resolution*', [status(thm)], ['30', '44', '45'])).
% 33.94/34.13  thf('47', plain, (~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))),
% 33.94/34.13      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 33.94/34.13  thf('48', plain,
% 33.94/34.13      (![X29 : $i, X30 : $i]:
% 33.94/34.13         ((k2_xboole_0 @ X29 @ X30)
% 33.94/34.13           = (k2_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ 
% 33.94/34.13              (k3_xboole_0 @ X29 @ X30)))),
% 33.94/34.13      inference('cnf', [status(esa)], [t93_xboole_1])).
% 33.94/34.13  thf('49', plain,
% 33.94/34.13      (![X17 : $i, X18 : $i, X19 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 33.94/34.13           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 33.94/34.13      inference('cnf', [status(esa)], [t41_xboole_1])).
% 33.94/34.13  thf(t48_xboole_1, axiom,
% 33.94/34.13    (![A:$i,B:$i]:
% 33.94/34.13     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 33.94/34.13  thf('50', plain,
% 33.94/34.13      (![X22 : $i, X23 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 33.94/34.13           = (k3_xboole_0 @ X22 @ X23))),
% 33.94/34.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 33.94/34.13  thf('51', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X2 @ 
% 33.94/34.13           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 33.94/34.13           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 33.94/34.13      inference('sup+', [status(thm)], ['49', '50'])).
% 33.94/34.13  thf('52', plain,
% 33.94/34.13      (![X17 : $i, X18 : $i, X19 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 33.94/34.13           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 33.94/34.13      inference('cnf', [status(esa)], [t41_xboole_1])).
% 33.94/34.13  thf('53', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X2 @ 
% 33.94/34.13           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 33.94/34.13           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 33.94/34.13      inference('demod', [status(thm)], ['51', '52'])).
% 33.94/34.13  thf('54', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X2 @ 
% 33.94/34.13           (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 33.94/34.13            (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 33.94/34.13           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 33.94/34.13              (k3_xboole_0 @ X1 @ X0)))),
% 33.94/34.13      inference('sup+', [status(thm)], ['48', '53'])).
% 33.94/34.13  thf('55', plain,
% 33.94/34.13      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 33.94/34.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 33.94/34.13  thf('56', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X2 @ 
% 33.94/34.13           (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 33.94/34.13            (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 33.94/34.13           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 33.94/34.13              (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0))))),
% 33.94/34.13      inference('demod', [status(thm)], ['54', '55'])).
% 33.94/34.13  thf(commutativity_k2_xboole_0, axiom,
% 33.94/34.13    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 33.94/34.13  thf('57', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 33.94/34.13      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 33.94/34.13  thf('58', plain,
% 33.94/34.13      (![X22 : $i, X23 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 33.94/34.13           = (k3_xboole_0 @ X22 @ X23))),
% 33.94/34.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 33.94/34.13  thf('59', plain,
% 33.94/34.13      (![X17 : $i, X18 : $i, X19 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 33.94/34.13           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 33.94/34.13      inference('cnf', [status(esa)], [t41_xboole_1])).
% 33.94/34.13  thf('60', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 33.94/34.13           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 33.94/34.13      inference('sup+', [status(thm)], ['58', '59'])).
% 33.94/34.13  thf('61', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 33.94/34.13           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 33.94/34.13      inference('sup+', [status(thm)], ['57', '60'])).
% 33.94/34.13  thf('62', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 33.94/34.13           (k5_xboole_0 @ X1 @ X0))
% 33.94/34.13           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 33.94/34.13              (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0))))),
% 33.94/34.13      inference('demod', [status(thm)], ['56', '61'])).
% 33.94/34.13  thf('63', plain,
% 33.94/34.13      (![X22 : $i, X23 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 33.94/34.13           = (k3_xboole_0 @ X22 @ X23))),
% 33.94/34.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 33.94/34.13  thf('64', plain,
% 33.94/34.13      (![X22 : $i, X23 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 33.94/34.13           = (k3_xboole_0 @ X22 @ X23))),
% 33.94/34.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 33.94/34.13  thf('65', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 33.94/34.13           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 33.94/34.13      inference('sup+', [status(thm)], ['63', '64'])).
% 33.94/34.13  thf(t47_xboole_1, axiom,
% 33.94/34.13    (![A:$i,B:$i]:
% 33.94/34.13     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 33.94/34.13  thf('66', plain,
% 33.94/34.13      (![X20 : $i, X21 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 33.94/34.13           = (k4_xboole_0 @ X20 @ X21))),
% 33.94/34.13      inference('cnf', [status(esa)], [t47_xboole_1])).
% 33.94/34.13  thf('67', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i]:
% 33.94/34.13         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 33.94/34.13           = (k4_xboole_0 @ X1 @ X0))),
% 33.94/34.13      inference('sup+', [status(thm)], ['65', '66'])).
% 33.94/34.13  thf('68', plain,
% 33.94/34.13      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 33.94/34.13        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 33.94/34.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.94/34.13  thf('69', plain,
% 33.94/34.13      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 33.94/34.13         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('split', [status(esa)], ['68'])).
% 33.94/34.13  thf('70', plain,
% 33.94/34.13      (![X6 : $i, X7 : $i]:
% 33.94/34.13         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 33.94/34.13      inference('cnf', [status(esa)], [d7_xboole_0])).
% 33.94/34.13  thf('71', plain,
% 33.94/34.13      ((((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 33.94/34.13         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('sup-', [status(thm)], ['69', '70'])).
% 33.94/34.13  thf('72', plain,
% 33.94/34.13      (![X14 : $i, X15 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X14 @ X15)
% 33.94/34.13           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 33.94/34.13      inference('cnf', [status(esa)], [t100_xboole_1])).
% 33.94/34.13  thf('73', plain,
% 33.94/34.13      ((((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 33.94/34.13          = (k5_xboole_0 @ sk_A @ k1_xboole_0)))
% 33.94/34.13         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('sup+', [status(thm)], ['71', '72'])).
% 33.94/34.13  thf('74', plain,
% 33.94/34.13      (![X27 : $i, X28 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ X28)),
% 33.94/34.13      inference('cnf', [status(esa)], [t79_xboole_1])).
% 33.94/34.13  thf('75', plain,
% 33.94/34.13      (((r1_xboole_0 @ (k5_xboole_0 @ sk_A @ k1_xboole_0) @ 
% 33.94/34.13         (k3_xboole_0 @ sk_B @ sk_C)))
% 33.94/34.13         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('sup+', [status(thm)], ['73', '74'])).
% 33.94/34.13  thf('76', plain,
% 33.94/34.13      (![X22 : $i, X23 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 33.94/34.13           = (k3_xboole_0 @ X22 @ X23))),
% 33.94/34.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 33.94/34.13  thf('77', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 33.94/34.13      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 33.94/34.13  thf('78', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 33.94/34.13      inference('cnf', [status(esa)], [t3_boole])).
% 33.94/34.13  thf('79', plain,
% 33.94/34.13      (![X22 : $i, X23 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 33.94/34.13           = (k3_xboole_0 @ X22 @ X23))),
% 33.94/34.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 33.94/34.13  thf('80', plain,
% 33.94/34.13      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 33.94/34.13      inference('sup+', [status(thm)], ['78', '79'])).
% 33.94/34.13  thf('81', plain,
% 33.94/34.13      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 33.94/34.13      inference('sup-', [status(thm)], ['11', '12'])).
% 33.94/34.13  thf('82', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 33.94/34.13      inference('demod', [status(thm)], ['80', '81'])).
% 33.94/34.13  thf('83', plain,
% 33.94/34.13      (![X17 : $i, X18 : $i, X19 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 33.94/34.13           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 33.94/34.13      inference('cnf', [status(esa)], [t41_xboole_1])).
% 33.94/34.13  thf('84', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 33.94/34.13           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 33.94/34.13      inference('sup+', [status(thm)], ['82', '83'])).
% 33.94/34.13  thf('85', plain,
% 33.94/34.13      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 33.94/34.13      inference('demod', [status(thm)], ['17', '22'])).
% 33.94/34.13  thf('86', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i]:
% 33.94/34.13         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 33.94/34.13      inference('demod', [status(thm)], ['84', '85'])).
% 33.94/34.13  thf('87', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i]:
% 33.94/34.13         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 33.94/34.13      inference('sup+', [status(thm)], ['77', '86'])).
% 33.94/34.13  thf('88', plain,
% 33.94/34.13      (![X17 : $i, X18 : $i, X19 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 33.94/34.13           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 33.94/34.13      inference('cnf', [status(esa)], [t41_xboole_1])).
% 33.94/34.13  thf('89', plain,
% 33.94/34.13      (![X9 : $i, X10 : $i]:
% 33.94/34.13         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 33.94/34.13      inference('cnf', [status(esa)], [l32_xboole_1])).
% 33.94/34.13  thf('90', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.94/34.13         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 33.94/34.13          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 33.94/34.13      inference('sup-', [status(thm)], ['88', '89'])).
% 33.94/34.13  thf('91', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i]:
% 33.94/34.13         (((k1_xboole_0) != (k1_xboole_0))
% 33.94/34.13          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 33.94/34.13      inference('sup-', [status(thm)], ['87', '90'])).
% 33.94/34.13  thf('92', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 33.94/34.13      inference('simplify', [status(thm)], ['91'])).
% 33.94/34.13  thf('93', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 33.94/34.13      inference('sup+', [status(thm)], ['76', '92'])).
% 33.94/34.13  thf('94', plain,
% 33.94/34.13      (![X24 : $i, X25 : $i, X26 : $i]:
% 33.94/34.13         (~ (r1_tarski @ X24 @ X25)
% 33.94/34.13          | ~ (r1_xboole_0 @ X25 @ X26)
% 33.94/34.13          | (r1_xboole_0 @ X24 @ X26))),
% 33.94/34.13      inference('cnf', [status(esa)], [t63_xboole_1])).
% 33.94/34.13  thf('95', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.94/34.13         ((r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 33.94/34.13          | ~ (r1_xboole_0 @ X0 @ X2))),
% 33.94/34.13      inference('sup-', [status(thm)], ['93', '94'])).
% 33.94/34.13  thf('96', plain,
% 33.94/34.13      ((![X0 : $i]:
% 33.94/34.13          (r1_xboole_0 @ 
% 33.94/34.13           (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ k1_xboole_0) @ X0) @ 
% 33.94/34.13           (k3_xboole_0 @ sk_B @ sk_C)))
% 33.94/34.13         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('sup-', [status(thm)], ['75', '95'])).
% 33.94/34.13  thf('97', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 33.94/34.13      inference('sup+', [status(thm)], ['20', '21'])).
% 33.94/34.13  thf('98', plain,
% 33.94/34.13      ((![X0 : $i]:
% 33.94/34.13          (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 33.94/34.13           (k3_xboole_0 @ sk_B @ sk_C)))
% 33.94/34.13         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('demod', [status(thm)], ['96', '97'])).
% 33.94/34.13  thf('99', plain,
% 33.94/34.13      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))) | 
% 33.94/34.13       ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 33.94/34.13      inference('split', [status(esa)], ['68'])).
% 33.94/34.13  thf('100', plain, (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 33.94/34.13      inference('sat_resolution*', [status(thm)], ['30', '44', '45', '99'])).
% 33.94/34.13  thf('101', plain,
% 33.94/34.13      (![X0 : $i]:
% 33.94/34.13         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_B @ sk_C))),
% 33.94/34.13      inference('simpl_trail', [status(thm)], ['98', '100'])).
% 33.94/34.13  thf('102', plain,
% 33.94/34.13      (![X6 : $i, X7 : $i]:
% 33.94/34.13         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 33.94/34.13      inference('cnf', [status(esa)], [d7_xboole_0])).
% 33.94/34.13  thf('103', plain,
% 33.94/34.13      (![X0 : $i]:
% 33.94/34.13         ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 33.94/34.13           (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 33.94/34.13      inference('sup-', [status(thm)], ['101', '102'])).
% 33.94/34.13  thf('104', plain,
% 33.94/34.13      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 33.94/34.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 33.94/34.13  thf('105', plain,
% 33.94/34.13      (![X6 : $i, X8 : $i]:
% 33.94/34.13         ((r1_xboole_0 @ X6 @ X8) | ((k3_xboole_0 @ X6 @ X8) != (k1_xboole_0)))),
% 33.94/34.13      inference('cnf', [status(esa)], [d7_xboole_0])).
% 33.94/34.13  thf('106', plain,
% 33.94/34.13      (![X0 : $i, X1 : $i]:
% 33.94/34.13         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 33.94/34.13      inference('sup-', [status(thm)], ['104', '105'])).
% 33.94/34.13  thf('107', plain,
% 33.94/34.13      (![X0 : $i]:
% 33.94/34.13         (((k1_xboole_0) != (k1_xboole_0))
% 33.94/34.13          | (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 33.94/34.13             (k3_xboole_0 @ sk_A @ X0)))),
% 33.94/34.13      inference('sup-', [status(thm)], ['103', '106'])).
% 33.94/34.13  thf('108', plain,
% 33.94/34.13      (![X0 : $i]:
% 33.94/34.13         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ (k3_xboole_0 @ sk_A @ X0))),
% 33.94/34.13      inference('simplify', [status(thm)], ['107'])).
% 33.94/34.13  thf('109', plain,
% 33.94/34.13      (![X0 : $i]:
% 33.94/34.13         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ (k4_xboole_0 @ sk_A @ X0))),
% 33.94/34.13      inference('sup+', [status(thm)], ['67', '108'])).
% 33.94/34.13  thf('110', plain,
% 33.94/34.13      (![X6 : $i, X7 : $i]:
% 33.94/34.13         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 33.94/34.13      inference('cnf', [status(esa)], [d7_xboole_0])).
% 33.94/34.13  thf('111', plain,
% 33.94/34.13      (![X0 : $i]:
% 33.94/34.13         ((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 33.94/34.13           (k4_xboole_0 @ sk_A @ X0)) = (k1_xboole_0))),
% 33.94/34.13      inference('sup-', [status(thm)], ['109', '110'])).
% 33.94/34.13  thf('112', plain,
% 33.94/34.13      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 33.94/34.13         (k5_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 33.94/34.13      inference('sup+', [status(thm)], ['62', '111'])).
% 33.94/34.13  thf('113', plain,
% 33.94/34.13      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 33.94/34.13         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('split', [status(esa)], ['3'])).
% 33.94/34.13  thf('114', plain,
% 33.94/34.13      (![X9 : $i, X11 : $i]:
% 33.94/34.13         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 33.94/34.13      inference('cnf', [status(esa)], [l32_xboole_1])).
% 33.94/34.13  thf('115', plain,
% 33.94/34.13      ((((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 33.94/34.13         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('sup-', [status(thm)], ['113', '114'])).
% 33.94/34.13  thf('116', plain,
% 33.94/34.13      (![X22 : $i, X23 : $i]:
% 33.94/34.13         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 33.94/34.13           = (k3_xboole_0 @ X22 @ X23))),
% 33.94/34.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 33.94/34.13  thf('117', plain,
% 33.94/34.13      ((((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 33.94/34.13          = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 33.94/34.13         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('sup+', [status(thm)], ['115', '116'])).
% 33.94/34.13  thf('118', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 33.94/34.13      inference('cnf', [status(esa)], [t3_boole])).
% 33.94/34.13  thf('119', plain,
% 33.94/34.13      ((((sk_A) = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 33.94/34.13         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 33.94/34.13      inference('demod', [status(thm)], ['117', '118'])).
% 33.94/34.13  thf('120', plain,
% 33.94/34.13      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 33.94/34.13       ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 33.94/34.13      inference('split', [status(esa)], ['3'])).
% 33.94/34.13  thf('121', plain, (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 33.94/34.13      inference('sat_resolution*', [status(thm)], ['30', '44', '45', '120'])).
% 33.94/34.13  thf('122', plain,
% 33.94/34.13      (((sk_A) = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 33.94/34.13      inference('simpl_trail', [status(thm)], ['119', '121'])).
% 33.94/34.13  thf('123', plain,
% 33.94/34.13      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 33.94/34.13      inference('demod', [status(thm)], ['112', '122'])).
% 33.94/34.13  thf('124', plain,
% 33.94/34.13      (![X9 : $i, X10 : $i]:
% 33.94/34.13         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 33.94/34.13      inference('cnf', [status(esa)], [l32_xboole_1])).
% 33.94/34.13  thf('125', plain,
% 33.94/34.13      ((((k1_xboole_0) != (k1_xboole_0))
% 33.94/34.13        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 33.94/34.13      inference('sup-', [status(thm)], ['123', '124'])).
% 33.94/34.13  thf('126', plain, ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))),
% 33.94/34.13      inference('simplify', [status(thm)], ['125'])).
% 33.94/34.13  thf('127', plain, ($false), inference('demod', [status(thm)], ['47', '126'])).
% 33.94/34.13  
% 33.94/34.13  % SZS output end Refutation
% 33.94/34.13  
% 33.96/34.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
