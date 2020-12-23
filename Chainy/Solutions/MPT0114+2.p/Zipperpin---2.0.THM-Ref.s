%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0114+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PiLfdqDH7b

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:46 EST 2020

% Result     : Theorem 3.53s
% Output     : Refutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 262 expanded)
%              Number of leaves         :   37 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  988 (2468 expanded)
%              Number of equality atoms :   70 (  99 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t107_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k5_xboole_0 @ ( B @ C ) ) ) )
    <=> ( ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
        & ( r1_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( A @ ( k5_xboole_0 @ ( B @ C ) ) ) )
      <=> ( ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
          & ( r1_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t107_xboole_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
   <= ~ ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X369: $i,X370: $i] :
      ( ( k2_xboole_0 @ ( X369 @ X370 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ ( X369 @ X370 ) @ ( k3_xboole_0 @ ( X369 @ X370 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X329: $i,X330: $i] :
      ( r1_tarski @ ( X329 @ ( k2_xboole_0 @ ( X329 @ X330 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,
    ( ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    | ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('6',plain,(
    ! [X127: $i,X128: $i] :
      ( ( ( k2_xboole_0 @ ( X128 @ X127 ) )
        = X127 )
      | ~ ( r1_tarski @ ( X128 @ X127 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( ( k2_xboole_0 @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
      = ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
     => ( r1_tarski @ ( A @ C ) ) ) )).

thf('8',plain,(
    ! [X124: $i,X125: $i,X126: $i] :
      ( ( r1_tarski @ ( X124 @ X125 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( X124 @ X126 ) @ X125 ) ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) @ X0 ) )
        | ( r1_tarski @ ( sk_A_2 @ X0 ) ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) @ X0 ) ) ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,
    ( ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
   <= ~ ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ ( k5_xboole_0 @ ( A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X97: $i,X98: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( X97 @ X98 ) @ ( k5_xboole_0 @ ( X97 @ X98 ) ) ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('15',plain,
    ( ( ( k2_xboole_0 @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
      = ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ ( A @ B ) )
              & ( r1_xboole_0 @ ( A @ C ) ) )
          & ( r1_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
          & ( r1_xboole_0 @ ( A @ B ) )
          & ( r1_xboole_0 @ ( A @ C ) ) ) ) )).

thf('16',plain,(
    ! [X297: $i,X298: $i,X300: $i] :
      ( ( r1_xboole_0 @ ( X297 @ X298 ) )
      | ~ ( r1_xboole_0 @ ( X297 @ ( k2_xboole_0 @ ( X298 @ X300 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( X0 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
        | ( r1_xboole_0 @ ( X0 @ sk_A_2 ) ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_xboole_0 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) @ sk_A_2 ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('19',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('20',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
   <= ~ ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    | ~ ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,(
    ~ ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['13','22','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','24'])).

thf(t61_xboole_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ( r2_xboole_0 @ ( k1_xboole_0 @ A ) ) ) )).

thf('26',plain,(
    ! [X274: $i] :
      ( ( r2_xboole_0 @ ( k1_xboole_0 @ X274 ) )
      | ( X274 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('27',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('28',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('29',plain,(
    ! [X274: $i] :
      ( ( r2_xboole_0 @ ( o_0_0_xboole_0 @ X274 ) )
      | ( X274 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('31',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('33',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
      = o_0_0_xboole_0 )
   <= ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t102_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k5_xboole_0 @ ( B @ C ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) ) ) ) ) )).

thf('35',plain,(
    ! [X108: $i,X109: $i,X110: $i] :
      ( ( k4_xboole_0 @ ( X108 @ ( k5_xboole_0 @ ( X109 @ X110 ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X108 @ ( k2_xboole_0 @ ( X109 @ X110 ) ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( X108 @ X109 ) @ X110 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t102_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X108: $i,X109: $i,X110: $i] :
      ( ( k4_xboole_0 @ ( X108 @ ( k5_xboole_0 @ ( X109 @ X110 ) ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( X108 @ X109 ) @ X110 ) @ ( k4_xboole_0 @ ( X108 @ ( k2_xboole_0 @ ( X109 @ X110 ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) @ o_0_0_xboole_0 ) ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('42',plain,(
    ! [X149: $i] :
      ( ( k2_xboole_0 @ ( X149 @ k1_xboole_0 ) )
      = X149 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('43',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('44',plain,(
    ! [X149: $i] :
      ( ( k2_xboole_0 @ ( X149 @ o_0_0_xboole_0 ) )
      = X149 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
      = ( k3_xboole_0 @ ( sk_C_5 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','45'])).

thf('47',plain,
    ( ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    | ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('48',plain,(
    r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['13','22','23','47'])).

thf('49',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    = ( k3_xboole_0 @ ( sk_C_5 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X104: $i,X105: $i] :
      ( ( k4_xboole_0 @ ( X104 @ X105 ) )
      = ( k5_xboole_0 @ ( X104 @ ( k3_xboole_0 @ ( X104 @ X105 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( X0 @ X1 ) )
      = ( k5_xboole_0 @ ( X0 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ ( A @ A ) )
      = k1_xboole_0 ) )).

thf('53',plain,(
    ! [X368: $i] :
      ( ( k5_xboole_0 @ ( X368 @ X368 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('54',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('55',plain,(
    ! [X368: $i] :
      ( ( k5_xboole_0 @ ( X368 @ X368 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ ( A @ B ) @ C ) )
      = ( k5_xboole_0 @ ( A @ ( k5_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('56',plain,(
    ! [X365: $i,X366: $i,X367: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ ( X365 @ X366 ) @ X367 ) )
      = ( k5_xboole_0 @ ( X365 @ ( k5_xboole_0 @ ( X366 @ X367 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ ( X1 @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( B @ A ) ) ) )).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( X9 @ X8 ) )
      = ( k5_xboole_0 @ ( X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('59',plain,(
    ! [X268: $i] :
      ( ( k5_xboole_0 @ ( X268 @ k1_xboole_0 ) )
      = X268 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('60',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('61',plain,(
    ! [X268: $i] :
      ( ( k5_xboole_0 @ ( X268 @ o_0_0_xboole_0 ) )
      = X268 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( X1 @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['57','62'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X35 @ X36 ) @ ( k4_xboole_0 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('65',plain,(
    ! [X329: $i,X330: $i] :
      ( r1_tarski @ ( X329 @ ( k2_xboole_0 @ ( X329 @ X330 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ ( A @ B ) )
        & ( r2_xboole_0 @ ( B @ A ) ) ) )).

thf('66',plain,(
    ! [X272: $i,X273: $i] :
      ( ~ ( r1_tarski @ ( X272 @ X273 ) )
      | ~ ( r2_xboole_0 @ ( X273 @ X272 ) ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_xboole_0 @ ( k2_xboole_0 @ ( X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_xboole_0 @ ( k5_xboole_0 @ ( X1 @ X0 ) @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_xboole_0 @ ( k3_xboole_0 @ ( X0 @ X1 ) @ ( k4_xboole_0 @ ( X1 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['52','69'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k4_xboole_0 @ ( A @ B ) ) ) )
      = ( k3_xboole_0 @ ( A @ B ) ) ) )).

thf('71',plain,(
    ! [X232: $i,X233: $i] :
      ( ( k4_xboole_0 @ ( X232 @ ( k4_xboole_0 @ ( X232 @ X233 ) ) ) )
      = ( k3_xboole_0 @ ( X232 @ X233 ) ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_xboole_0 @ ( k3_xboole_0 @ ( X0 @ X1 ) @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( r2_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) @ ( k4_xboole_0 @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','72'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) )
      = ( k3_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('74',plain,(
    ! [X138: $i,X139: $i,X140: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( X138 @ X139 ) @ X140 ) )
      = ( k3_xboole_0 @ ( X138 @ ( k3_xboole_0 @ ( X139 @ X140 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('75',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    | ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
   <= ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(split,[status(esa)],['75'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('77',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('78',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('79',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k3_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
      = o_0_0_xboole_0 )
   <= ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    | ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(split,[status(esa)],['75'])).

thf('82',plain,(
    r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['13','22','23','81'])).

thf('83',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    = o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['80','82'])).

thf('84',plain,(
    ~ ( r2_xboole_0 @ ( o_0_0_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['73','74','83'])).

thf('85',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['29','84'])).

thf('86',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k4_xboole_0 @ ( X88 @ X89 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('87',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('88',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k4_xboole_0 @ ( X88 @ X89 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    r1_tarski @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['25','90'])).

%------------------------------------------------------------------------------
