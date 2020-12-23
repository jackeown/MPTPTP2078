%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I5396gTM3a

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:42 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 495 expanded)
%              Number of leaves         :   41 ( 162 expanded)
%              Depth                    :   22
%              Number of atoms          : 1689 (4506 expanded)
%              Number of equality atoms :  136 ( 327 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf('2',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X28: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X28 @ X30 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t102_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t102_xboole_1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X78: $i] :
      ( ( k5_xboole_0 @ X78 @ X78 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X36 @ X37 ) @ X38 )
      = ( k4_xboole_0 @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ k1_xboole_0 ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ( ( k4_xboole_0 @ X28 @ X29 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('19',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t103_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k5_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t103_xboole_1])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t84_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ A @ C )
        & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X72: $i,X73: $i,X74: $i] :
      ( ( r1_xboole_0 @ X72 @ X73 )
      | ~ ( r1_xboole_0 @ X72 @ ( k4_xboole_0 @ X73 @ X74 ) )
      | ~ ( r1_xboole_0 @ X72 @ X74 ) ) ),
    inference(cnf,[status(esa)],[t84_xboole_1])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
        | ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ sk_C ) )
        | ( r1_xboole_0 @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('27',plain,(
    ! [X56: $i] :
      ( r1_xboole_0 @ X56 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ sk_C ) )
        | ( r1_xboole_0 @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X33: $i] :
      ( ( k4_xboole_0 @ X33 @ k1_xboole_0 )
      = X33 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('31',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( r1_xboole_0 @ X64 @ ( k4_xboole_0 @ X65 @ X66 ) )
      | ~ ( r1_xboole_0 @ X65 @ ( k4_xboole_0 @ X64 @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X33: $i] :
      ( ( k4_xboole_0 @ X33 @ k1_xboole_0 )
      = X33 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,(
    ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['22','37','38'])).

thf('40',plain,(
    ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','39'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X34 @ X35 ) @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X83: $i,X84: $i] :
      ( ( k2_xboole_0 @ X83 @ X84 )
      = ( k5_xboole_0 @ X83 @ ( k4_xboole_0 @ X84 @ X83 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X83: $i,X84: $i] :
      ( ( k2_xboole_0 @ X83 @ X84 )
      = ( k5_xboole_0 @ X83 @ ( k4_xboole_0 @ X84 @ X83 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('46',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X78: $i] :
      ( ( k5_xboole_0 @ X78 @ X78 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X36 @ X37 ) @ X38 )
      = ( k4_xboole_0 @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_xboole_0 @ X31 @ ( k4_xboole_0 @ X32 @ X31 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ( ( k4_xboole_0 @ X28 @ X29 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('59',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X21 )
      | ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_A @ X0 )
        | ~ ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('63',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['22','37','38','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(simpl_trail,[status(thm)],['61','63'])).

thf('65',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['45','64'])).

thf('66',plain,(
    ! [X28: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X28 @ X30 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t102_xboole_1])).

thf('69',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_C @ sk_B ) )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('75',plain,
    ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('76',plain,(
    ! [X69: $i,X70: $i] :
      ( ( ( k4_xboole_0 @ X69 @ X70 )
        = X69 )
      | ~ ( r1_xboole_0 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('77',plain,
    ( ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
      = ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('78',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k3_xboole_0 @ X43 @ ( k4_xboole_0 @ X44 @ X45 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X43 @ X44 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('79',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) )
      = ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('81',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ( ( k4_xboole_0 @ X28 @ X29 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('85',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k4_xboole_0 @ X41 @ ( k4_xboole_0 @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('86',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_C @ sk_A ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['79','89'])).

thf('91',plain,(
    ! [X28: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X28 @ X30 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('92',plain,
    ( ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_C @ sk_A ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k3_xboole_0 @ X43 @ ( k4_xboole_0 @ X44 @ X45 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X43 @ X44 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('94',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k4_xboole_0 @ X41 @ ( k4_xboole_0 @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('96',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('97',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('98',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t102_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('101',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('103',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ ( k3_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k3_xboole_0 @ X43 @ ( k4_xboole_0 @ X44 @ X45 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X43 @ X44 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('110',plain,(
    ! [X52: $i] :
      ( ( k5_xboole_0 @ X52 @ k1_xboole_0 )
      = X52 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('113',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ ( k3_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','102','111','114'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('116',plain,(
    ! [X46: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X46 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('117',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('120',plain,(
    ! [X52: $i] :
      ( ( k5_xboole_0 @ X52 @ k1_xboole_0 )
      = X52 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X33: $i] :
      ( ( k4_xboole_0 @ X33 @ k1_xboole_0 )
      = X33 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('123',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','121','122'])).

thf(t72_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf('124',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( X58 = X57 )
      | ~ ( r1_xboole_0 @ X58 @ X59 )
      | ( ( k2_xboole_0 @ X59 @ X57 )
       != ( k2_xboole_0 @ X58 @ X60 ) )
      | ~ ( r1_xboole_0 @ X60 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t72_xboole_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_xboole_0 @ X2 @ X1 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X2 @ k1_xboole_0 )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X56: $i] :
      ( r1_xboole_0 @ X56 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_xboole_0 @ X2 @ X1 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X2 = X0 ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X2
        = ( k2_xboole_0 @ X2 @ X1 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['115','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','102','111','114'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ~ ( r1_xboole_0 @ k1_xboole_0 @ sk_B )
      | ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_C ) )
        = sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['96','131'])).

thf('133',plain,(
    ! [X46: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X46 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('134',plain,(
    ! [X69: $i,X71: $i] :
      ( ( r1_xboole_0 @ X69 @ X71 )
      | ( ( k4_xboole_0 @ X69 @ X71 )
       != X69 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_C ) )
      = sk_B )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['132','136'])).

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('138',plain,(
    ! [X81: $i,X82: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X81 @ X82 ) @ ( k5_xboole_0 @ X81 @ X82 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf('139',plain,
    ( ( r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X28: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X28 @ X30 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('141',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_C ) ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('143',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t102_xboole_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('146',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','121','122'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['141','147'])).

thf('149',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['72'])).

thf('150',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['22','37','38','149'])).

thf('151',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_C ) )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['148','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','121','122'])).

thf('153',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70','71','151','152'])).

thf('154',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ( ( k4_xboole_0 @ X28 @ X29 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('155',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    $false ),
    inference(demod,[status(thm)],['40','156'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I5396gTM3a
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:06:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.68/1.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.68/1.89  % Solved by: fo/fo7.sh
% 1.68/1.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.68/1.89  % done 2394 iterations in 1.434s
% 1.68/1.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.68/1.89  % SZS output start Refutation
% 1.68/1.89  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.68/1.89  thf(sk_A_type, type, sk_A: $i).
% 1.68/1.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.68/1.89  thf(sk_B_type, type, sk_B: $i).
% 1.68/1.89  thf(sk_C_type, type, sk_C: $i).
% 1.68/1.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.68/1.89  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.68/1.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.68/1.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.68/1.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.68/1.89  thf(t107_xboole_1, conjecture,
% 1.68/1.89    (![A:$i,B:$i,C:$i]:
% 1.68/1.89     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.68/1.89       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 1.68/1.89         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 1.68/1.89  thf(zf_stmt_0, negated_conjecture,
% 1.68/1.89    (~( ![A:$i,B:$i,C:$i]:
% 1.68/1.89        ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.68/1.89          ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 1.68/1.89            ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 1.68/1.89    inference('cnf.neg', [status(esa)], [t107_xboole_1])).
% 1.68/1.89  thf('0', plain,
% 1.68/1.89      ((~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 1.68/1.89        | ~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 1.68/1.89        | ~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.68/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.89  thf('1', plain,
% 1.68/1.89      ((~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 1.68/1.89         <= (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('split', [status(esa)], ['0'])).
% 1.68/1.89  thf('2', plain,
% 1.68/1.89      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 1.68/1.89        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.68/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.89  thf('3', plain,
% 1.68/1.89      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 1.68/1.89         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('split', [status(esa)], ['2'])).
% 1.68/1.89  thf(t37_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i]:
% 1.68/1.89     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.68/1.89  thf('4', plain,
% 1.68/1.89      (![X28 : $i, X30 : $i]:
% 1.68/1.89         (((k4_xboole_0 @ X28 @ X30) = (k1_xboole_0))
% 1.68/1.89          | ~ (r1_tarski @ X28 @ X30))),
% 1.68/1.89      inference('cnf', [status(esa)], [t37_xboole_1])).
% 1.68/1.89  thf('5', plain,
% 1.68/1.89      ((((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 1.68/1.89         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup-', [status(thm)], ['3', '4'])).
% 1.68/1.89  thf(t102_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i,C:$i]:
% 1.68/1.89     ( ( k4_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) =
% 1.68/1.89       ( k2_xboole_0 @
% 1.68/1.89         ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ 
% 1.68/1.89         ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ))).
% 1.68/1.89  thf('6', plain,
% 1.68/1.89      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12))
% 1.68/1.89           = (k2_xboole_0 @ (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)) @ 
% 1.68/1.89              (k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t102_xboole_1])).
% 1.68/1.89  thf(t21_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.68/1.89  thf('7', plain,
% 1.68/1.89      (![X22 : $i, X23 : $i]:
% 1.68/1.89         ((k3_xboole_0 @ X22 @ (k2_xboole_0 @ X22 @ X23)) = (X22))),
% 1.68/1.89      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.68/1.89  thf(t100_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i]:
% 1.68/1.89     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.68/1.89  thf('8', plain,
% 1.68/1.89      (![X8 : $i, X9 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X8 @ X9)
% 1.68/1.89           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.68/1.89  thf('9', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 1.68/1.89           = (k5_xboole_0 @ X0 @ X0))),
% 1.68/1.89      inference('sup+', [status(thm)], ['7', '8'])).
% 1.68/1.89  thf(t92_xboole_1, axiom,
% 1.68/1.89    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.68/1.89  thf('10', plain, (![X78 : $i]: ((k5_xboole_0 @ X78 @ X78) = (k1_xboole_0))),
% 1.68/1.89      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.68/1.89  thf('11', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.68/1.89      inference('demod', [status(thm)], ['9', '10'])).
% 1.68/1.89  thf('12', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 1.68/1.89           (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0))) = (k1_xboole_0))),
% 1.68/1.89      inference('sup+', [status(thm)], ['6', '11'])).
% 1.68/1.89  thf(t41_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i,C:$i]:
% 1.68/1.89     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.68/1.89       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.68/1.89  thf('13', plain,
% 1.68/1.89      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ (k4_xboole_0 @ X36 @ X37) @ X38)
% 1.68/1.89           = (k4_xboole_0 @ X36 @ (k2_xboole_0 @ X37 @ X38)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.68/1.89  thf('14', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X2 @ 
% 1.68/1.89           (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.68/1.89            (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0))))
% 1.68/1.89           = (k1_xboole_0))),
% 1.68/1.89      inference('demod', [status(thm)], ['12', '13'])).
% 1.68/1.89  thf('15', plain,
% 1.68/1.89      ((((k4_xboole_0 @ sk_A @ 
% 1.68/1.89          (k2_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ k1_xboole_0))
% 1.68/1.89          = (k1_xboole_0)))
% 1.68/1.89         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup+', [status(thm)], ['5', '14'])).
% 1.68/1.89  thf(t1_boole, axiom,
% 1.68/1.89    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.68/1.89  thf('16', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.68/1.89      inference('cnf', [status(esa)], [t1_boole])).
% 1.68/1.89  thf('17', plain,
% 1.68/1.89      ((((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 1.68/1.89         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('demod', [status(thm)], ['15', '16'])).
% 1.68/1.89  thf('18', plain,
% 1.68/1.89      (![X28 : $i, X29 : $i]:
% 1.68/1.89         ((r1_tarski @ X28 @ X29)
% 1.68/1.89          | ((k4_xboole_0 @ X28 @ X29) != (k1_xboole_0)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t37_xboole_1])).
% 1.68/1.89  thf('19', plain,
% 1.68/1.89      (((((k1_xboole_0) != (k1_xboole_0))
% 1.68/1.89         | (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 1.68/1.89         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup-', [status(thm)], ['17', '18'])).
% 1.68/1.89  thf('20', plain,
% 1.68/1.89      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 1.68/1.89         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('simplify', [status(thm)], ['19'])).
% 1.68/1.89  thf('21', plain,
% 1.68/1.89      ((~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 1.68/1.89         <= (~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('split', [status(esa)], ['0'])).
% 1.68/1.89  thf('22', plain,
% 1.68/1.89      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 1.68/1.89       ~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.68/1.89      inference('sup-', [status(thm)], ['20', '21'])).
% 1.68/1.89  thf(t103_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i]:
% 1.68/1.89     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 1.68/1.89  thf('23', plain,
% 1.68/1.89      (![X13 : $i, X14 : $i]:
% 1.68/1.89         (r1_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k5_xboole_0 @ X13 @ X14))),
% 1.68/1.89      inference('cnf', [status(esa)], [t103_xboole_1])).
% 1.68/1.89  thf('24', plain,
% 1.68/1.89      ((((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 1.68/1.89         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup-', [status(thm)], ['3', '4'])).
% 1.68/1.89  thf(t84_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i,C:$i]:
% 1.68/1.89     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 1.68/1.89          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ))).
% 1.68/1.89  thf('25', plain,
% 1.68/1.89      (![X72 : $i, X73 : $i, X74 : $i]:
% 1.68/1.89         ((r1_xboole_0 @ X72 @ X73)
% 1.68/1.89          | ~ (r1_xboole_0 @ X72 @ (k4_xboole_0 @ X73 @ X74))
% 1.68/1.89          | ~ (r1_xboole_0 @ X72 @ X74))),
% 1.68/1.89      inference('cnf', [status(esa)], [t84_xboole_1])).
% 1.68/1.89  thf('26', plain,
% 1.68/1.89      ((![X0 : $i]:
% 1.68/1.89          (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.68/1.89           | ~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B @ sk_C))
% 1.68/1.89           | (r1_xboole_0 @ X0 @ sk_A)))
% 1.68/1.89         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup-', [status(thm)], ['24', '25'])).
% 1.68/1.89  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.68/1.89  thf('27', plain, (![X56 : $i]: (r1_xboole_0 @ X56 @ k1_xboole_0)),
% 1.68/1.89      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.68/1.89  thf('28', plain,
% 1.68/1.89      ((![X0 : $i]:
% 1.68/1.89          (~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B @ sk_C))
% 1.68/1.89           | (r1_xboole_0 @ X0 @ sk_A)))
% 1.68/1.89         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('demod', [status(thm)], ['26', '27'])).
% 1.68/1.89  thf('29', plain,
% 1.68/1.89      (((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))
% 1.68/1.89         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup-', [status(thm)], ['23', '28'])).
% 1.68/1.89  thf(t3_boole, axiom,
% 1.68/1.89    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.68/1.89  thf('30', plain, (![X33 : $i]: ((k4_xboole_0 @ X33 @ k1_xboole_0) = (X33))),
% 1.68/1.89      inference('cnf', [status(esa)], [t3_boole])).
% 1.68/1.89  thf(t81_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i,C:$i]:
% 1.68/1.89     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.68/1.89       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.68/1.89  thf('31', plain,
% 1.68/1.89      (![X64 : $i, X65 : $i, X66 : $i]:
% 1.68/1.89         ((r1_xboole_0 @ X64 @ (k4_xboole_0 @ X65 @ X66))
% 1.68/1.89          | ~ (r1_xboole_0 @ X65 @ (k4_xboole_0 @ X64 @ X66)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t81_xboole_1])).
% 1.68/1.89  thf('32', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         (~ (r1_xboole_0 @ X1 @ X0)
% 1.68/1.89          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ k1_xboole_0)))),
% 1.68/1.89      inference('sup-', [status(thm)], ['30', '31'])).
% 1.68/1.89  thf('33', plain, (![X33 : $i]: ((k4_xboole_0 @ X33 @ k1_xboole_0) = (X33))),
% 1.68/1.89      inference('cnf', [status(esa)], [t3_boole])).
% 1.68/1.89  thf('34', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.68/1.89      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.89  thf('35', plain,
% 1.68/1.89      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 1.68/1.89         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup-', [status(thm)], ['29', '34'])).
% 1.68/1.89  thf('36', plain,
% 1.68/1.89      ((~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 1.68/1.89         <= (~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('split', [status(esa)], ['0'])).
% 1.68/1.89  thf('37', plain,
% 1.68/1.89      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))) | 
% 1.68/1.89       ~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.68/1.89      inference('sup-', [status(thm)], ['35', '36'])).
% 1.68/1.89  thf('38', plain,
% 1.68/1.89      (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 1.68/1.89       ~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 1.68/1.89       ~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 1.68/1.89      inference('split', [status(esa)], ['0'])).
% 1.68/1.89  thf('39', plain, (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.68/1.89      inference('sat_resolution*', [status(thm)], ['22', '37', '38'])).
% 1.68/1.89  thf('40', plain, (~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))),
% 1.68/1.89      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 1.68/1.89  thf(t40_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i]:
% 1.68/1.89     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.68/1.89  thf('41', plain,
% 1.68/1.89      (![X34 : $i, X35 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ (k2_xboole_0 @ X34 @ X35) @ X35)
% 1.68/1.89           = (k4_xboole_0 @ X34 @ X35))),
% 1.68/1.89      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.68/1.89  thf(t98_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i]:
% 1.68/1.89     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.68/1.89  thf('42', plain,
% 1.68/1.89      (![X83 : $i, X84 : $i]:
% 1.68/1.89         ((k2_xboole_0 @ X83 @ X84)
% 1.68/1.89           = (k5_xboole_0 @ X83 @ (k4_xboole_0 @ X84 @ X83)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.68/1.89  thf('43', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.68/1.89           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.68/1.89      inference('sup+', [status(thm)], ['41', '42'])).
% 1.68/1.89  thf('44', plain,
% 1.68/1.89      (![X83 : $i, X84 : $i]:
% 1.68/1.89         ((k2_xboole_0 @ X83 @ X84)
% 1.68/1.89           = (k5_xboole_0 @ X83 @ (k4_xboole_0 @ X84 @ X83)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.68/1.89  thf('45', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.68/1.89           = (k2_xboole_0 @ X0 @ X1))),
% 1.68/1.89      inference('demod', [status(thm)], ['43', '44'])).
% 1.68/1.89  thf(idempotence_k2_xboole_0, axiom,
% 1.68/1.89    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.68/1.89  thf('46', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 1.68/1.89      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.68/1.89  thf(d6_xboole_0, axiom,
% 1.68/1.89    (![A:$i,B:$i]:
% 1.68/1.89     ( ( k5_xboole_0 @ A @ B ) =
% 1.68/1.89       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.68/1.89  thf('47', plain,
% 1.68/1.89      (![X4 : $i, X5 : $i]:
% 1.68/1.89         ((k5_xboole_0 @ X4 @ X5)
% 1.68/1.89           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 1.68/1.89      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.68/1.89  thf('48', plain,
% 1.68/1.89      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.68/1.89      inference('sup+', [status(thm)], ['46', '47'])).
% 1.68/1.89  thf('49', plain, (![X78 : $i]: ((k5_xboole_0 @ X78 @ X78) = (k1_xboole_0))),
% 1.68/1.89      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.68/1.89  thf('50', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.68/1.89      inference('demod', [status(thm)], ['48', '49'])).
% 1.68/1.89  thf('51', plain,
% 1.68/1.89      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ (k4_xboole_0 @ X36 @ X37) @ X38)
% 1.68/1.89           = (k4_xboole_0 @ X36 @ (k2_xboole_0 @ X37 @ X38)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.68/1.89  thf('52', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k1_xboole_0)
% 1.68/1.89           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.68/1.89      inference('sup+', [status(thm)], ['50', '51'])).
% 1.68/1.89  thf(t39_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i]:
% 1.68/1.89     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.68/1.89  thf('53', plain,
% 1.68/1.89      (![X31 : $i, X32 : $i]:
% 1.68/1.89         ((k2_xboole_0 @ X31 @ (k4_xboole_0 @ X32 @ X31))
% 1.68/1.89           = (k2_xboole_0 @ X31 @ X32))),
% 1.68/1.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.68/1.89  thf('54', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.68/1.89      inference('demod', [status(thm)], ['52', '53'])).
% 1.68/1.89  thf('55', plain,
% 1.68/1.89      (![X28 : $i, X29 : $i]:
% 1.68/1.89         ((r1_tarski @ X28 @ X29)
% 1.68/1.89          | ((k4_xboole_0 @ X28 @ X29) != (k1_xboole_0)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t37_xboole_1])).
% 1.68/1.89  thf('56', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         (((k1_xboole_0) != (k1_xboole_0))
% 1.68/1.89          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.68/1.89      inference('sup-', [status(thm)], ['54', '55'])).
% 1.68/1.89  thf('57', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.68/1.89      inference('simplify', [status(thm)], ['56'])).
% 1.68/1.89  thf('58', plain,
% 1.68/1.89      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 1.68/1.89         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('split', [status(esa)], ['2'])).
% 1.68/1.89  thf(t1_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i,C:$i]:
% 1.68/1.89     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.68/1.89       ( r1_tarski @ A @ C ) ))).
% 1.68/1.89  thf('59', plain,
% 1.68/1.89      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.68/1.89         (~ (r1_tarski @ X19 @ X20)
% 1.68/1.89          | ~ (r1_tarski @ X20 @ X21)
% 1.68/1.89          | (r1_tarski @ X19 @ X21))),
% 1.68/1.89      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.68/1.89  thf('60', plain,
% 1.68/1.89      ((![X0 : $i]:
% 1.68/1.89          ((r1_tarski @ sk_A @ X0)
% 1.68/1.89           | ~ (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ X0)))
% 1.68/1.89         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup-', [status(thm)], ['58', '59'])).
% 1.68/1.89  thf('61', plain,
% 1.68/1.89      ((![X0 : $i]:
% 1.68/1.89          (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))))
% 1.68/1.89         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup-', [status(thm)], ['57', '60'])).
% 1.68/1.89  thf('62', plain,
% 1.68/1.89      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 1.68/1.89       ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.68/1.89      inference('split', [status(esa)], ['2'])).
% 1.68/1.89  thf('63', plain, (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.68/1.89      inference('sat_resolution*', [status(thm)], ['22', '37', '38', '62'])).
% 1.68/1.89  thf('64', plain,
% 1.68/1.89      (![X0 : $i]:
% 1.68/1.89         (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.68/1.89      inference('simpl_trail', [status(thm)], ['61', '63'])).
% 1.68/1.89  thf('65', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))),
% 1.68/1.89      inference('sup+', [status(thm)], ['45', '64'])).
% 1.68/1.89  thf('66', plain,
% 1.68/1.89      (![X28 : $i, X30 : $i]:
% 1.68/1.89         (((k4_xboole_0 @ X28 @ X30) = (k1_xboole_0))
% 1.68/1.89          | ~ (r1_tarski @ X28 @ X30))),
% 1.68/1.89      inference('cnf', [status(esa)], [t37_xboole_1])).
% 1.68/1.89  thf('67', plain,
% 1.68/1.89      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)) = (k1_xboole_0))),
% 1.68/1.89      inference('sup-', [status(thm)], ['65', '66'])).
% 1.68/1.89  thf('68', plain,
% 1.68/1.89      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12))
% 1.68/1.89           = (k2_xboole_0 @ (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)) @ 
% 1.68/1.89              (k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t102_xboole_1])).
% 1.68/1.89  thf('69', plain,
% 1.68/1.89      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_C @ sk_B))
% 1.68/1.89         = (k2_xboole_0 @ k1_xboole_0 @ 
% 1.68/1.89            (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_B)))),
% 1.68/1.89      inference('sup+', [status(thm)], ['67', '68'])).
% 1.68/1.89  thf(commutativity_k5_xboole_0, axiom,
% 1.68/1.89    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.68/1.89  thf('70', plain,
% 1.68/1.89      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.68/1.89      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.68/1.89  thf(commutativity_k3_xboole_0, axiom,
% 1.68/1.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.68/1.89  thf('71', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.68/1.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.68/1.89  thf('72', plain,
% 1.68/1.89      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 1.68/1.89        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.68/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.89  thf('73', plain,
% 1.68/1.89      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 1.68/1.89         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('split', [status(esa)], ['72'])).
% 1.68/1.89  thf('74', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.68/1.89      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.89  thf('75', plain,
% 1.68/1.89      (((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))
% 1.68/1.89         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup-', [status(thm)], ['73', '74'])).
% 1.68/1.89  thf(t83_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i]:
% 1.68/1.89     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.68/1.89  thf('76', plain,
% 1.68/1.89      (![X69 : $i, X70 : $i]:
% 1.68/1.89         (((k4_xboole_0 @ X69 @ X70) = (X69)) | ~ (r1_xboole_0 @ X69 @ X70))),
% 1.68/1.89      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.68/1.89  thf('77', plain,
% 1.68/1.89      ((((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)
% 1.68/1.89          = (k3_xboole_0 @ sk_B @ sk_C)))
% 1.68/1.89         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup-', [status(thm)], ['75', '76'])).
% 1.68/1.89  thf(t49_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i,C:$i]:
% 1.68/1.89     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.68/1.89       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.68/1.89  thf('78', plain,
% 1.68/1.89      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.68/1.89         ((k3_xboole_0 @ X43 @ (k4_xboole_0 @ X44 @ X45))
% 1.68/1.89           = (k4_xboole_0 @ (k3_xboole_0 @ X43 @ X44) @ X45))),
% 1.68/1.89      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.68/1.89  thf('79', plain,
% 1.68/1.89      ((((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A))
% 1.68/1.89          = (k3_xboole_0 @ sk_B @ sk_C)))
% 1.68/1.89         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('demod', [status(thm)], ['77', '78'])).
% 1.68/1.89  thf('80', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.68/1.89      inference('demod', [status(thm)], ['48', '49'])).
% 1.68/1.89  thf('81', plain,
% 1.68/1.89      (![X28 : $i, X29 : $i]:
% 1.68/1.89         ((r1_tarski @ X28 @ X29)
% 1.68/1.89          | ((k4_xboole_0 @ X28 @ X29) != (k1_xboole_0)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t37_xboole_1])).
% 1.68/1.89  thf('82', plain,
% 1.68/1.89      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 1.68/1.89      inference('sup-', [status(thm)], ['80', '81'])).
% 1.68/1.89  thf('83', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.68/1.89      inference('simplify', [status(thm)], ['82'])).
% 1.68/1.89  thf('84', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.68/1.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.68/1.89  thf(t48_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i]:
% 1.68/1.89     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.68/1.89  thf('85', plain,
% 1.68/1.89      (![X41 : $i, X42 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X41 @ (k4_xboole_0 @ X41 @ X42))
% 1.68/1.89           = (k3_xboole_0 @ X41 @ X42))),
% 1.68/1.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.68/1.89  thf(t106_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i,C:$i]:
% 1.68/1.89     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.68/1.89       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.68/1.89  thf('86', plain,
% 1.68/1.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.68/1.89         ((r1_tarski @ X15 @ X16)
% 1.68/1.89          | ~ (r1_tarski @ X15 @ (k4_xboole_0 @ X16 @ X17)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.68/1.89  thf('87', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.89         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 1.68/1.89      inference('sup-', [status(thm)], ['85', '86'])).
% 1.68/1.89  thf('88', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.89         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 1.68/1.89      inference('sup-', [status(thm)], ['84', '87'])).
% 1.68/1.89  thf('89', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.68/1.89      inference('sup-', [status(thm)], ['83', '88'])).
% 1.68/1.89  thf('90', plain,
% 1.68/1.89      (((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_C) @ (k4_xboole_0 @ sk_C @ sk_A)))
% 1.68/1.89         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup+', [status(thm)], ['79', '89'])).
% 1.68/1.89  thf('91', plain,
% 1.68/1.89      (![X28 : $i, X30 : $i]:
% 1.68/1.89         (((k4_xboole_0 @ X28 @ X30) = (k1_xboole_0))
% 1.68/1.89          | ~ (r1_tarski @ X28 @ X30))),
% 1.68/1.89      inference('cnf', [status(esa)], [t37_xboole_1])).
% 1.68/1.89  thf('92', plain,
% 1.68/1.89      ((((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 1.68/1.89          (k4_xboole_0 @ sk_C @ sk_A)) = (k1_xboole_0)))
% 1.68/1.89         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup-', [status(thm)], ['90', '91'])).
% 1.68/1.89  thf('93', plain,
% 1.68/1.89      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.68/1.89         ((k3_xboole_0 @ X43 @ (k4_xboole_0 @ X44 @ X45))
% 1.68/1.89           = (k4_xboole_0 @ (k3_xboole_0 @ X43 @ X44) @ X45))),
% 1.68/1.89      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.68/1.89  thf('94', plain,
% 1.68/1.89      (![X41 : $i, X42 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X41 @ (k4_xboole_0 @ X41 @ X42))
% 1.68/1.89           = (k3_xboole_0 @ X41 @ X42))),
% 1.68/1.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.68/1.89  thf('95', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.68/1.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.68/1.89  thf('96', plain,
% 1.68/1.89      ((((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_C)) = (k1_xboole_0)))
% 1.68/1.89         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 1.68/1.89  thf(idempotence_k3_xboole_0, axiom,
% 1.68/1.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.68/1.89  thf('97', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 1.68/1.89      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.68/1.89  thf('98', plain,
% 1.68/1.89      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12))
% 1.68/1.89           = (k2_xboole_0 @ (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)) @ 
% 1.68/1.89              (k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t102_xboole_1])).
% 1.68/1.89  thf('99', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.68/1.89           = (k2_xboole_0 @ 
% 1.68/1.89              (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 1.68/1.89              (k3_xboole_0 @ X1 @ X0)))),
% 1.68/1.89      inference('sup+', [status(thm)], ['97', '98'])).
% 1.68/1.89  thf('100', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.68/1.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.68/1.89  thf('101', plain,
% 1.68/1.89      (![X8 : $i, X9 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X8 @ X9)
% 1.68/1.89           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.68/1.89  thf('102', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X0 @ X1)
% 1.68/1.89           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.68/1.89      inference('sup+', [status(thm)], ['100', '101'])).
% 1.68/1.89  thf(t22_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.68/1.89  thf('103', plain,
% 1.68/1.89      (![X24 : $i, X25 : $i]:
% 1.68/1.89         ((k2_xboole_0 @ X24 @ (k3_xboole_0 @ X24 @ X25)) = (X24))),
% 1.68/1.89      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.68/1.89  thf('104', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.68/1.89      inference('demod', [status(thm)], ['52', '53'])).
% 1.68/1.89  thf('105', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 1.68/1.89      inference('sup+', [status(thm)], ['103', '104'])).
% 1.68/1.89  thf('106', plain,
% 1.68/1.89      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.68/1.89         ((k3_xboole_0 @ X43 @ (k4_xboole_0 @ X44 @ X45))
% 1.68/1.89           = (k4_xboole_0 @ (k3_xboole_0 @ X43 @ X44) @ X45))),
% 1.68/1.89      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.68/1.89  thf('107', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.68/1.89      inference('demod', [status(thm)], ['105', '106'])).
% 1.68/1.89  thf('108', plain,
% 1.68/1.89      (![X8 : $i, X9 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X8 @ X9)
% 1.68/1.89           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.68/1.89  thf('109', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.68/1.89           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.68/1.89      inference('sup+', [status(thm)], ['107', '108'])).
% 1.68/1.89  thf(t5_boole, axiom,
% 1.68/1.89    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.68/1.89  thf('110', plain, (![X52 : $i]: ((k5_xboole_0 @ X52 @ k1_xboole_0) = (X52))),
% 1.68/1.89      inference('cnf', [status(esa)], [t5_boole])).
% 1.68/1.89  thf('111', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.68/1.89      inference('demod', [status(thm)], ['109', '110'])).
% 1.68/1.89  thf('112', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.68/1.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.68/1.89  thf('113', plain,
% 1.68/1.89      (![X24 : $i, X25 : $i]:
% 1.68/1.89         ((k2_xboole_0 @ X24 @ (k3_xboole_0 @ X24 @ X25)) = (X24))),
% 1.68/1.89      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.68/1.89  thf('114', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 1.68/1.89      inference('sup+', [status(thm)], ['112', '113'])).
% 1.68/1.89  thf('115', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((X1)
% 1.68/1.89           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.68/1.89      inference('demod', [status(thm)], ['99', '102', '111', '114'])).
% 1.68/1.89  thf(t4_boole, axiom,
% 1.68/1.89    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.68/1.89  thf('116', plain,
% 1.68/1.89      (![X46 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X46) = (k1_xboole_0))),
% 1.68/1.89      inference('cnf', [status(esa)], [t4_boole])).
% 1.68/1.89  thf('117', plain,
% 1.68/1.89      (![X4 : $i, X5 : $i]:
% 1.68/1.89         ((k5_xboole_0 @ X4 @ X5)
% 1.68/1.89           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 1.68/1.89      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.68/1.89  thf('118', plain,
% 1.68/1.89      (![X0 : $i]:
% 1.68/1.89         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.68/1.89           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.68/1.89      inference('sup+', [status(thm)], ['116', '117'])).
% 1.68/1.89  thf('119', plain,
% 1.68/1.89      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.68/1.89      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.68/1.89  thf('120', plain, (![X52 : $i]: ((k5_xboole_0 @ X52 @ k1_xboole_0) = (X52))),
% 1.68/1.89      inference('cnf', [status(esa)], [t5_boole])).
% 1.68/1.89  thf('121', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.68/1.89      inference('sup+', [status(thm)], ['119', '120'])).
% 1.68/1.89  thf('122', plain, (![X33 : $i]: ((k4_xboole_0 @ X33 @ k1_xboole_0) = (X33))),
% 1.68/1.89      inference('cnf', [status(esa)], [t3_boole])).
% 1.68/1.89  thf('123', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.68/1.89      inference('demod', [status(thm)], ['118', '121', '122'])).
% 1.68/1.89  thf(t72_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i,C:$i,D:$i]:
% 1.68/1.89     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.68/1.89         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.68/1.89       ( ( C ) = ( B ) ) ))).
% 1.68/1.89  thf('124', plain,
% 1.68/1.89      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 1.68/1.89         (((X58) = (X57))
% 1.68/1.89          | ~ (r1_xboole_0 @ X58 @ X59)
% 1.68/1.89          | ((k2_xboole_0 @ X59 @ X57) != (k2_xboole_0 @ X58 @ X60))
% 1.68/1.89          | ~ (r1_xboole_0 @ X60 @ X57))),
% 1.68/1.89      inference('cnf', [status(esa)], [t72_xboole_1])).
% 1.68/1.89  thf('125', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.89         (((X0) != (k2_xboole_0 @ X2 @ X1))
% 1.68/1.89          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.68/1.89          | ~ (r1_xboole_0 @ X2 @ k1_xboole_0)
% 1.68/1.89          | ((X2) = (X0)))),
% 1.68/1.89      inference('sup-', [status(thm)], ['123', '124'])).
% 1.68/1.89  thf('126', plain, (![X56 : $i]: (r1_xboole_0 @ X56 @ k1_xboole_0)),
% 1.68/1.89      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.68/1.89  thf('127', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.89         (((X0) != (k2_xboole_0 @ X2 @ X1))
% 1.68/1.89          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.68/1.89          | ((X2) = (X0)))),
% 1.68/1.89      inference('demod', [status(thm)], ['125', '126'])).
% 1.68/1.89  thf('128', plain,
% 1.68/1.89      (![X1 : $i, X2 : $i]:
% 1.68/1.89         (((X2) = (k2_xboole_0 @ X2 @ X1))
% 1.68/1.89          | ~ (r1_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ X1)))),
% 1.68/1.89      inference('simplify', [status(thm)], ['127'])).
% 1.68/1.89  thf('129', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         (~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.68/1.89          | ((k4_xboole_0 @ X0 @ X1)
% 1.68/1.89              = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 1.68/1.89                 (k3_xboole_0 @ X0 @ X1))))),
% 1.68/1.89      inference('sup-', [status(thm)], ['115', '128'])).
% 1.68/1.89  thf('130', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((X1)
% 1.68/1.89           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.68/1.89      inference('demod', [status(thm)], ['99', '102', '111', '114'])).
% 1.68/1.89  thf('131', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         (~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.68/1.89          | ((k4_xboole_0 @ X0 @ X1) = (X0)))),
% 1.68/1.89      inference('demod', [status(thm)], ['129', '130'])).
% 1.68/1.89  thf('132', plain,
% 1.68/1.89      (((~ (r1_xboole_0 @ k1_xboole_0 @ sk_B)
% 1.68/1.89         | ((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_C)) = (sk_B))))
% 1.68/1.89         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup-', [status(thm)], ['96', '131'])).
% 1.68/1.89  thf('133', plain,
% 1.68/1.89      (![X46 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X46) = (k1_xboole_0))),
% 1.68/1.89      inference('cnf', [status(esa)], [t4_boole])).
% 1.68/1.89  thf('134', plain,
% 1.68/1.89      (![X69 : $i, X71 : $i]:
% 1.68/1.89         ((r1_xboole_0 @ X69 @ X71) | ((k4_xboole_0 @ X69 @ X71) != (X69)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.68/1.89  thf('135', plain,
% 1.68/1.89      (![X0 : $i]:
% 1.68/1.89         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.68/1.89      inference('sup-', [status(thm)], ['133', '134'])).
% 1.68/1.89  thf('136', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.68/1.89      inference('simplify', [status(thm)], ['135'])).
% 1.68/1.89  thf('137', plain,
% 1.68/1.89      ((((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_C)) = (sk_B)))
% 1.68/1.89         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('demod', [status(thm)], ['132', '136'])).
% 1.68/1.89  thf(t96_xboole_1, axiom,
% 1.68/1.89    (![A:$i,B:$i]:
% 1.68/1.89     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 1.68/1.89  thf('138', plain,
% 1.68/1.89      (![X81 : $i, X82 : $i]:
% 1.68/1.89         (r1_tarski @ (k4_xboole_0 @ X81 @ X82) @ (k5_xboole_0 @ X81 @ X82))),
% 1.68/1.89      inference('cnf', [status(esa)], [t96_xboole_1])).
% 1.68/1.89  thf('139', plain,
% 1.68/1.89      (((r1_tarski @ sk_B @ (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_C))))
% 1.68/1.89         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup+', [status(thm)], ['137', '138'])).
% 1.68/1.89  thf('140', plain,
% 1.68/1.89      (![X28 : $i, X30 : $i]:
% 1.68/1.89         (((k4_xboole_0 @ X28 @ X30) = (k1_xboole_0))
% 1.68/1.89          | ~ (r1_tarski @ X28 @ X30))),
% 1.68/1.89      inference('cnf', [status(esa)], [t37_xboole_1])).
% 1.68/1.89  thf('141', plain,
% 1.68/1.89      ((((k4_xboole_0 @ sk_B @ 
% 1.68/1.89          (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_C))) = (k1_xboole_0)))
% 1.68/1.89         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('sup-', [status(thm)], ['139', '140'])).
% 1.68/1.89  thf('142', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 1.68/1.89      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.68/1.89  thf('143', plain,
% 1.68/1.89      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12))
% 1.68/1.89           = (k2_xboole_0 @ (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)) @ 
% 1.68/1.89              (k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t102_xboole_1])).
% 1.68/1.89  thf('144', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1))
% 1.68/1.89           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 1.68/1.89              (k3_xboole_0 @ X0 @ X1)))),
% 1.68/1.89      inference('sup+', [status(thm)], ['142', '143'])).
% 1.68/1.89  thf('145', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.68/1.89      inference('demod', [status(thm)], ['9', '10'])).
% 1.68/1.89  thf('146', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.68/1.89      inference('demod', [status(thm)], ['118', '121', '122'])).
% 1.68/1.89  thf('147', plain,
% 1.68/1.89      (![X0 : $i, X1 : $i]:
% 1.68/1.89         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1))
% 1.68/1.89           = (k3_xboole_0 @ X0 @ X1))),
% 1.68/1.89      inference('demod', [status(thm)], ['144', '145', '146'])).
% 1.68/1.89  thf('148', plain,
% 1.68/1.89      ((((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_C)) = (k1_xboole_0)))
% 1.68/1.89         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.68/1.89      inference('demod', [status(thm)], ['141', '147'])).
% 1.68/1.89  thf('149', plain,
% 1.68/1.89      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))) | 
% 1.68/1.89       ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.68/1.89      inference('split', [status(esa)], ['72'])).
% 1.68/1.89  thf('150', plain, (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 1.68/1.89      inference('sat_resolution*', [status(thm)], ['22', '37', '38', '149'])).
% 1.68/1.89  thf('151', plain,
% 1.68/1.89      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_C)) = (k1_xboole_0))),
% 1.68/1.89      inference('simpl_trail', [status(thm)], ['148', '150'])).
% 1.68/1.89  thf('152', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.68/1.89      inference('demod', [status(thm)], ['118', '121', '122'])).
% 1.68/1.89  thf('153', plain,
% 1.68/1.89      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 1.68/1.89      inference('demod', [status(thm)], ['69', '70', '71', '151', '152'])).
% 1.68/1.89  thf('154', plain,
% 1.68/1.89      (![X28 : $i, X29 : $i]:
% 1.68/1.89         ((r1_tarski @ X28 @ X29)
% 1.68/1.89          | ((k4_xboole_0 @ X28 @ X29) != (k1_xboole_0)))),
% 1.68/1.89      inference('cnf', [status(esa)], [t37_xboole_1])).
% 1.68/1.89  thf('155', plain,
% 1.68/1.89      ((((k1_xboole_0) != (k1_xboole_0))
% 1.68/1.89        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 1.68/1.89      inference('sup-', [status(thm)], ['153', '154'])).
% 1.68/1.89  thf('156', plain, ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))),
% 1.68/1.89      inference('simplify', [status(thm)], ['155'])).
% 1.68/1.89  thf('157', plain, ($false), inference('demod', [status(thm)], ['40', '156'])).
% 1.68/1.89  
% 1.68/1.89  % SZS output end Refutation
% 1.68/1.89  
% 1.68/1.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
