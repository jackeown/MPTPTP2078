%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eBpXncmEtt

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:18 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 336 expanded)
%              Number of leaves         :   27 ( 111 expanded)
%              Depth                    :   18
%              Number of atoms          :  877 (2980 expanded)
%              Number of equality atoms :   86 ( 326 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X51: $i,X53: $i,X54: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X51 @ X53 ) @ X54 )
      | ~ ( r2_hidden @ X53 @ X54 )
      | ~ ( r2_hidden @ X51 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B_1 )
        | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['3','13'])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','20','21'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('23',plain,(
    ! [X48: $i,X49: $i] :
      ( ( X49 != X48 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X49 ) @ ( k1_tarski @ X48 ) )
       != ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('24',plain,(
    ! [X48: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X48 ) @ ( k1_tarski @ X48 ) )
     != ( k1_tarski @ X48 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('26',plain,(
    ! [X48: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X48 ) @ ( k1_tarski @ X48 ) )
     != ( k1_tarski @ X48 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('29',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','20','21'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('39',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','20','21'])).

thf('40',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
        | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','20','21'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','50'])).

thf('52',plain,
    ( ( k1_xboole_0
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','51'])).

thf('53',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['14','52'])).

thf('54',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','53'])).

thf('55',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','54'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('56',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X46 ) @ X47 )
      | ( r2_hidden @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('64',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('71',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('74',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('75',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','53','74'])).

thf('76',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['73','75'])).

thf('77',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['72','76'])).

thf('78',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['55','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eBpXncmEtt
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:36:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 653 iterations in 0.201s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(t67_zfmisc_1, conjecture,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.47/0.66       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i,B:$i]:
% 0.47/0.66        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.47/0.66          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.47/0.66  thf('0', plain,
% 0.47/0.66      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 0.47/0.66        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.47/0.66       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.47/0.66         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('4', plain,
% 0.47/0.67      (((r2_hidden @ sk_A @ sk_B_1)
% 0.47/0.67        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('5', plain,
% 0.47/0.67      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.47/0.67      inference('split', [status(esa)], ['4'])).
% 0.47/0.67  thf('6', plain,
% 0.47/0.67      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.47/0.67      inference('split', [status(esa)], ['4'])).
% 0.47/0.67  thf(t38_zfmisc_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.47/0.67       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.47/0.67  thf('7', plain,
% 0.47/0.67      (![X51 : $i, X53 : $i, X54 : $i]:
% 0.47/0.67         ((r1_tarski @ (k2_tarski @ X51 @ X53) @ X54)
% 0.47/0.67          | ~ (r2_hidden @ X53 @ X54)
% 0.47/0.67          | ~ (r2_hidden @ X51 @ X54))),
% 0.47/0.67      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.47/0.67  thf('8', plain,
% 0.47/0.67      ((![X0 : $i]:
% 0.47/0.67          (~ (r2_hidden @ X0 @ sk_B_1)
% 0.47/0.67           | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B_1)))
% 0.47/0.67         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.67  thf('9', plain,
% 0.47/0.67      (((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B_1))
% 0.47/0.67         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['5', '8'])).
% 0.47/0.67  thf(t69_enumset1, axiom,
% 0.47/0.67    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.47/0.67  thf('10', plain,
% 0.47/0.67      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.47/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.67  thf('11', plain,
% 0.47/0.67      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.47/0.67         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.47/0.67      inference('demod', [status(thm)], ['9', '10'])).
% 0.47/0.67  thf(l32_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.67  thf('12', plain,
% 0.47/0.67      (![X8 : $i, X10 : $i]:
% 0.47/0.67         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.47/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.47/0.67  thf('13', plain,
% 0.47/0.67      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))
% 0.47/0.67         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.67  thf('14', plain,
% 0.47/0.67      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.47/0.67             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.47/0.67      inference('sup+', [status(thm)], ['3', '13'])).
% 0.47/0.67  thf('15', plain,
% 0.47/0.67      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('split', [status(esa)], ['0'])).
% 0.47/0.67  thf(t48_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.67  thf('16', plain,
% 0.47/0.67      (![X13 : $i, X14 : $i]:
% 0.47/0.67         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.47/0.67           = (k3_xboole_0 @ X13 @ X14))),
% 0.47/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.67  thf('17', plain,
% 0.47/0.67      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.47/0.67          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['15', '16'])).
% 0.47/0.67  thf(idempotence_k3_xboole_0, axiom,
% 0.47/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.47/0.67  thf('18', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.47/0.67      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.47/0.67  thf(t100_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.47/0.67  thf('19', plain,
% 0.47/0.67      (![X11 : $i, X12 : $i]:
% 0.47/0.67         ((k4_xboole_0 @ X11 @ X12)
% 0.47/0.67           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.67  thf('20', plain,
% 0.47/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.47/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.47/0.67  thf(commutativity_k3_xboole_0, axiom,
% 0.47/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.47/0.67  thf('21', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.67  thf('22', plain,
% 0.47/0.67      ((((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.47/0.67          = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['17', '20', '21'])).
% 0.47/0.67  thf(t20_zfmisc_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.47/0.67         ( k1_tarski @ A ) ) <=>
% 0.47/0.67       ( ( A ) != ( B ) ) ))).
% 0.47/0.67  thf('23', plain,
% 0.47/0.67      (![X48 : $i, X49 : $i]:
% 0.47/0.67         (((X49) != (X48))
% 0.47/0.67          | ((k4_xboole_0 @ (k1_tarski @ X49) @ (k1_tarski @ X48))
% 0.47/0.67              != (k1_tarski @ X49)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.47/0.67  thf('24', plain,
% 0.47/0.67      (![X48 : $i]:
% 0.47/0.67         ((k4_xboole_0 @ (k1_tarski @ X48) @ (k1_tarski @ X48))
% 0.47/0.67           != (k1_tarski @ X48))),
% 0.47/0.67      inference('simplify', [status(thm)], ['23'])).
% 0.47/0.67  thf('25', plain,
% 0.47/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.47/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.47/0.67  thf('26', plain,
% 0.47/0.67      (![X48 : $i]:
% 0.47/0.67         ((k5_xboole_0 @ (k1_tarski @ X48) @ (k1_tarski @ X48))
% 0.47/0.67           != (k1_tarski @ X48))),
% 0.47/0.67      inference('demod', [status(thm)], ['24', '25'])).
% 0.47/0.67  thf('27', plain,
% 0.47/0.67      ((((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A)))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['22', '26'])).
% 0.47/0.67  thf(t7_xboole_0, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.67          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.47/0.67  thf('28', plain,
% 0.47/0.67      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.47/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.67  thf('29', plain,
% 0.47/0.67      ((((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.47/0.67          = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['17', '20', '21'])).
% 0.47/0.67  thf('30', plain,
% 0.47/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.47/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.47/0.67  thf('31', plain,
% 0.47/0.67      (![X13 : $i, X14 : $i]:
% 0.47/0.67         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.47/0.67           = (k3_xboole_0 @ X13 @ X14))),
% 0.47/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.67  thf('32', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.47/0.67           = (k3_xboole_0 @ X0 @ X0))),
% 0.47/0.67      inference('sup+', [status(thm)], ['30', '31'])).
% 0.47/0.67  thf('33', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.47/0.67      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.47/0.67  thf('34', plain,
% 0.47/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.47/0.67      inference('demod', [status(thm)], ['32', '33'])).
% 0.47/0.67  thf('35', plain,
% 0.47/0.67      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.47/0.67          (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))) = (k1_tarski @ sk_A)))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['29', '34'])).
% 0.47/0.67  thf('36', plain,
% 0.47/0.67      (![X13 : $i, X14 : $i]:
% 0.47/0.67         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.47/0.67           = (k3_xboole_0 @ X13 @ X14))),
% 0.47/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.67  thf('37', plain,
% 0.47/0.67      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.47/0.67          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.47/0.67             (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['35', '36'])).
% 0.47/0.67  thf('38', plain,
% 0.47/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.47/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.47/0.67  thf('39', plain,
% 0.47/0.67      ((((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.47/0.67          = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['17', '20', '21'])).
% 0.47/0.67  thf('40', plain,
% 0.47/0.67      ((((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.47/0.67          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.47/0.67             (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.47/0.67  thf('41', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.67  thf(t4_xboole_0, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.67            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.67       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.47/0.67            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.47/0.67  thf('42', plain,
% 0.47/0.67      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.47/0.67          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.47/0.67      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.47/0.67  thf('43', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.47/0.67          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.47/0.67      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.67  thf('44', plain,
% 0.47/0.67      ((![X0 : $i]:
% 0.47/0.67          (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.47/0.67           | ~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.47/0.67                (k1_tarski @ sk_A))))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['40', '43'])).
% 0.47/0.67  thf('45', plain,
% 0.47/0.67      ((((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.47/0.67          = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['17', '20', '21'])).
% 0.47/0.67  thf('46', plain,
% 0.47/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.47/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.47/0.67  thf(t79_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.47/0.67  thf('47', plain,
% 0.47/0.67      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.47/0.67      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.47/0.67  thf('48', plain, (![X0 : $i]: (r1_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 0.47/0.67      inference('sup+', [status(thm)], ['46', '47'])).
% 0.47/0.67  thf('49', plain,
% 0.47/0.67      (((r1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.47/0.67         (k1_tarski @ sk_A)))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['45', '48'])).
% 0.47/0.67  thf('50', plain,
% 0.47/0.67      ((![X0 : $i]:
% 0.47/0.67          ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['44', '49'])).
% 0.47/0.67  thf('51', plain,
% 0.47/0.67      ((((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['28', '50'])).
% 0.47/0.67  thf('52', plain,
% 0.47/0.67      ((((k1_xboole_0) != (k1_tarski @ sk_A)))
% 0.47/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['27', '51'])).
% 0.47/0.67  thf('53', plain,
% 0.47/0.67      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.47/0.67       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['14', '52'])).
% 0.47/0.67  thf('54', plain, (~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.47/0.67      inference('sat_resolution*', [status(thm)], ['2', '53'])).
% 0.47/0.67  thf('55', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.47/0.67      inference('simpl_trail', [status(thm)], ['1', '54'])).
% 0.47/0.67  thf(l27_zfmisc_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.47/0.67  thf('56', plain,
% 0.47/0.67      (![X46 : $i, X47 : $i]:
% 0.47/0.67         ((r1_xboole_0 @ (k1_tarski @ X46) @ X47) | (r2_hidden @ X46 @ X47))),
% 0.47/0.67      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.47/0.67  thf('57', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.67  thf('58', plain,
% 0.47/0.67      (![X3 : $i, X4 : $i]:
% 0.47/0.67         ((r1_xboole_0 @ X3 @ X4)
% 0.47/0.67          | (r2_hidden @ (sk_C @ X4 @ X3) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.47/0.67  thf('59', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.47/0.67          | (r1_xboole_0 @ X0 @ X1))),
% 0.47/0.67      inference('sup+', [status(thm)], ['57', '58'])).
% 0.47/0.67  thf('60', plain,
% 0.47/0.67      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.47/0.67          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.47/0.67      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.47/0.67  thf('61', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['59', '60'])).
% 0.47/0.67  thf('62', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['56', '61'])).
% 0.47/0.67  thf('63', plain,
% 0.47/0.67      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.47/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.67  thf('64', plain,
% 0.47/0.67      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.47/0.67          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.47/0.67      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.47/0.67  thf('65', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['63', '64'])).
% 0.47/0.67  thf('66', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((r2_hidden @ X0 @ X1)
% 0.47/0.67          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['62', '65'])).
% 0.47/0.67  thf('67', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.67  thf('68', plain,
% 0.47/0.67      (![X11 : $i, X12 : $i]:
% 0.47/0.67         ((k4_xboole_0 @ X11 @ X12)
% 0.47/0.67           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.67  thf('69', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((k4_xboole_0 @ X0 @ X1)
% 0.47/0.67           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.47/0.67      inference('sup+', [status(thm)], ['67', '68'])).
% 0.47/0.67  thf('70', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.47/0.67            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 0.47/0.67          | (r2_hidden @ X0 @ X1))),
% 0.47/0.67      inference('sup+', [status(thm)], ['66', '69'])).
% 0.47/0.67  thf(t5_boole, axiom,
% 0.47/0.67    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.67  thf('71', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.47/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.47/0.67  thf('72', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.47/0.67          | (r2_hidden @ X0 @ X1))),
% 0.47/0.67      inference('demod', [status(thm)], ['70', '71'])).
% 0.47/0.67  thf('73', plain,
% 0.47/0.67      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))
% 0.47/0.67         <= (~
% 0.47/0.67             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.67      inference('split', [status(esa)], ['4'])).
% 0.47/0.67  thf('74', plain,
% 0.47/0.67      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.47/0.67       ((r2_hidden @ sk_A @ sk_B_1))),
% 0.47/0.67      inference('split', [status(esa)], ['4'])).
% 0.47/0.67  thf('75', plain,
% 0.47/0.67      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.47/0.67      inference('sat_resolution*', [status(thm)], ['2', '53', '74'])).
% 0.47/0.67  thf('76', plain,
% 0.47/0.67      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A))),
% 0.47/0.67      inference('simpl_trail', [status(thm)], ['73', '75'])).
% 0.47/0.67  thf('77', plain,
% 0.47/0.67      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.47/0.67        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.47/0.67      inference('sup-', [status(thm)], ['72', '76'])).
% 0.47/0.67  thf('78', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.47/0.67      inference('simplify', [status(thm)], ['77'])).
% 0.47/0.67  thf('79', plain, ($false), inference('demod', [status(thm)], ['55', '78'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
