%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qhzpgQKyKE

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:50 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 540 expanded)
%              Number of leaves         :   20 ( 149 expanded)
%              Depth                    :   23
%              Number of atoms          :  807 (5630 expanded)
%              Number of equality atoms :   37 ( 300 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t64_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( A != C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_zfmisc_1])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference(split,[status(esa)],['1'])).

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

thf('3',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('4',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_3 ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,
    ( ( sk_A != sk_C_3 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A != sk_C_3 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19 != X18 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( sk_A = sk_C_3 )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_A = sk_C_3 )
   <= ( sk_A = sk_C_3 ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_3 ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
      & ( sk_A = sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A != sk_C_3 )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( sk_A = sk_C_3 )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X5 ) )
      | ( r2_hidden @ X2 @ X5 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('19',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X44 ) @ X45 )
      | ( r2_hidden @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        | ~ ( r1_xboole_0 @ sk_B @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('34',plain,
    ( ( r2_hidden @ sk_C_3 @ sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('35',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k3_xboole_0 @ X47 @ ( k1_tarski @ X46 ) )
        = ( k1_tarski @ X46 ) )
      | ~ ( r2_hidden @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('36',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) )
      = ( k1_tarski @ sk_C_3 ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_3 ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','40'])).

thf('42',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('43',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_A = sk_C_3 )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( sk_A != sk_C_3 )
   <= ( sk_A != sk_C_3 ) ),
    inference(split,[status(esa)],['6'])).

thf('46',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_3 )
      & ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
    | ( sk_A = sk_C_3 )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('49',plain,(
    r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['7','14','15','47','48'])).

thf('50',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_3 ) ) ),
    inference(simpl_trail,[status(thm)],['5','49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ sk_C_3 ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['7','14','15','47','48'])).

thf('61',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ) ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('63',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['7','14','15','47'])).

thf('64',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['62','63'])).

thf('65',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ),
    inference(clc,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('67',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ),
    inference(clc,[status(thm)],['61','64'])).

thf('68',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('69',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r2_hidden @ sk_C_3 @ sk_B ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k3_xboole_0 @ X47 @ ( k1_tarski @ X46 ) )
        = ( k1_tarski @ X46 ) )
      | ~ ( r2_hidden @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_3 ) )
    = ( k1_tarski @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_C_3 ) ),
    inference(demod,[status(thm)],['65','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['50','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qhzpgQKyKE
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 331 iterations in 0.151s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.60  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.40/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.60  thf(t79_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.40/0.60      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.40/0.60  thf(t64_zfmisc_1, conjecture,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.40/0.60       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.60        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.40/0.60          ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t64_zfmisc_1])).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      (((r2_hidden @ sk_A @ sk_B)
% 0.40/0.60        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))))
% 0.40/0.60         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))))),
% 0.40/0.60      inference('split', [status(esa)], ['1'])).
% 0.40/0.60  thf(t3_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.40/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.60            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X8 @ X6)
% 0.40/0.60          | ~ (r2_hidden @ X8 @ X9)
% 0.40/0.60          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.40/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      ((![X0 : $i]:
% 0.40/0.60          (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)) @ X0)
% 0.40/0.60           | ~ (r2_hidden @ sk_A @ X0)))
% 0.40/0.60         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_C_3)))
% 0.40/0.60         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['0', '4'])).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      ((((sk_A) != (sk_C_3))
% 0.40/0.60        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (~ (((sk_A) = (sk_C_3))) | 
% 0.40/0.60       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))))),
% 0.40/0.60      inference('split', [status(esa)], ['6'])).
% 0.40/0.60  thf(d1_tarski, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.60         (((X19) != (X18))
% 0.40/0.60          | (r2_hidden @ X19 @ X20)
% 0.40/0.60          | ((X20) != (k1_tarski @ X18)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.60  thf('9', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 0.40/0.60      inference('simplify', [status(thm)], ['8'])).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      ((((sk_A) = (sk_C_3))
% 0.40/0.60        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.40/0.60        | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('11', plain, ((((sk_A) = (sk_C_3))) <= ((((sk_A) = (sk_C_3))))),
% 0.40/0.60      inference('split', [status(esa)], ['10'])).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_C_3)))
% 0.40/0.60         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['0', '4'])).
% 0.40/0.61  thf('13', plain,
% 0.40/0.61      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.40/0.61         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))) & 
% 0.40/0.61             (((sk_A) = (sk_C_3))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      (~ (((sk_A) = (sk_C_3))) | 
% 0.40/0.61       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['9', '13'])).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      (~ ((r2_hidden @ sk_A @ sk_B)) | (((sk_A) = (sk_C_3))) | 
% 0.40/0.61       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))))),
% 0.40/0.61      inference('split', [status(esa)], ['10'])).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.61      inference('split', [status(esa)], ['1'])).
% 0.40/0.61  thf(t1_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.40/0.61       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.40/0.61         ((r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X5))
% 0.40/0.61          | (r2_hidden @ X2 @ X5)
% 0.40/0.61          | ~ (r2_hidden @ X2 @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      ((![X0 : $i]:
% 0.40/0.61          ((r2_hidden @ sk_A @ X0)
% 0.40/0.61           | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))))
% 0.40/0.61         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.61  thf(l27_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      (![X44 : $i, X45 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ (k1_tarski @ X44) @ X45) | (r2_hidden @ X44 @ X45))),
% 0.40/0.61      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      (![X6 : $i, X7 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.40/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (![X6 : $i, X7 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.40/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.61  thf('22', plain,
% 0.40/0.61      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X8 @ X6)
% 0.40/0.61          | ~ (r2_hidden @ X8 @ X9)
% 0.40/0.61          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.40/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.61  thf('23', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ X1 @ X0)
% 0.40/0.61          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.40/0.61          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.40/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.61  thf('24', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ X0 @ X1)
% 0.40/0.61          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.40/0.61          | (r1_xboole_0 @ X0 @ X1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['20', '23'])).
% 0.40/0.61  thf('25', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.40/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.40/0.61  thf('26', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['19', '25'])).
% 0.40/0.61  thf(t100_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.61  thf('27', plain,
% 0.40/0.61      (![X14 : $i, X15 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X14 @ X15)
% 0.40/0.61           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.61  thf('28', plain,
% 0.40/0.61      ((![X0 : $i]:
% 0.40/0.61          ((r2_hidden @ sk_A @ X0)
% 0.40/0.61           | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))))
% 0.40/0.61         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      ((![X0 : $i]:
% 0.40/0.61          ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.40/0.61           | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))))
% 0.40/0.61         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['27', '28'])).
% 0.40/0.61  thf(t4_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.61            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.61  thf('30', plain,
% 0.40/0.61      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.40/0.61          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.40/0.61      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.61  thf('31', plain,
% 0.40/0.61      ((![X0 : $i]:
% 0.40/0.61          ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.40/0.61           | ~ (r1_xboole_0 @ sk_B @ X0)))
% 0.40/0.61         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.61  thf('32', plain,
% 0.40/0.61      ((![X0 : $i]:
% 0.40/0.61          ((r2_hidden @ X0 @ sk_B)
% 0.40/0.61           | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ X0)))))
% 0.40/0.61         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['26', '31'])).
% 0.40/0.61  thf('33', plain,
% 0.40/0.61      ((~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))))),
% 0.40/0.61      inference('split', [status(esa)], ['10'])).
% 0.40/0.61  thf('34', plain,
% 0.40/0.61      (((r2_hidden @ sk_C_3 @ sk_B))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))) & 
% 0.40/0.61             ((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.40/0.61  thf(l31_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r2_hidden @ A @ B ) =>
% 0.40/0.61       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.40/0.61  thf('35', plain,
% 0.40/0.61      (![X46 : $i, X47 : $i]:
% 0.40/0.61         (((k3_xboole_0 @ X47 @ (k1_tarski @ X46)) = (k1_tarski @ X46))
% 0.40/0.61          | ~ (r2_hidden @ X46 @ X47))),
% 0.40/0.61      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.40/0.61  thf('36', plain,
% 0.40/0.61      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)) = (k1_tarski @ sk_C_3)))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))) & 
% 0.40/0.61             ((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.61  thf('37', plain,
% 0.40/0.61      (![X14 : $i, X15 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X14 @ X15)
% 0.40/0.61           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.61  thf('38', plain,
% 0.40/0.61      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))
% 0.40/0.61          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))) & 
% 0.40/0.61             ((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['36', '37'])).
% 0.40/0.61  thf('39', plain,
% 0.40/0.61      ((~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))))),
% 0.40/0.61      inference('split', [status(esa)], ['10'])).
% 0.40/0.61  thf('40', plain,
% 0.40/0.61      ((~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))) & 
% 0.40/0.61             ((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.61  thf('41', plain,
% 0.40/0.61      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_3)))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))) & 
% 0.40/0.61             ((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['18', '40'])).
% 0.40/0.61  thf('42', plain,
% 0.40/0.61      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X21 @ X20)
% 0.40/0.61          | ((X21) = (X18))
% 0.40/0.61          | ((X20) != (k1_tarski @ X18)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.61  thf('43', plain,
% 0.40/0.61      (![X18 : $i, X21 : $i]:
% 0.40/0.61         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['42'])).
% 0.40/0.61  thf('44', plain,
% 0.40/0.61      ((((sk_A) = (sk_C_3)))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))) & 
% 0.40/0.61             ((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['41', '43'])).
% 0.40/0.61  thf('45', plain, ((((sk_A) != (sk_C_3))) <= (~ (((sk_A) = (sk_C_3))))),
% 0.40/0.61      inference('split', [status(esa)], ['6'])).
% 0.40/0.61  thf('46', plain,
% 0.40/0.61      ((((sk_A) != (sk_A)))
% 0.40/0.61         <= (~ (((sk_A) = (sk_C_3))) & 
% 0.40/0.61             ~
% 0.40/0.61             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))) & 
% 0.40/0.61             ((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.61  thf('47', plain,
% 0.40/0.61      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))) | 
% 0.40/0.61       (((sk_A) = (sk_C_3))) | ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.40/0.61      inference('simplify', [status(thm)], ['46'])).
% 0.40/0.61  thf('48', plain,
% 0.40/0.61      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))) | 
% 0.40/0.61       ((r2_hidden @ sk_A @ sk_B))),
% 0.40/0.61      inference('split', [status(esa)], ['1'])).
% 0.40/0.61  thf('49', plain,
% 0.40/0.61      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))))),
% 0.40/0.61      inference('sat_resolution*', [status(thm)], ['7', '14', '15', '47', '48'])).
% 0.40/0.61  thf('50', plain, (~ (r2_hidden @ sk_A @ (k1_tarski @ sk_C_3))),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['5', '49'])).
% 0.40/0.61  thf('51', plain,
% 0.40/0.61      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))))
% 0.40/0.61         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))))),
% 0.40/0.61      inference('split', [status(esa)], ['1'])).
% 0.40/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.40/0.61  thf('52', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.61  thf('53', plain,
% 0.40/0.61      (![X14 : $i, X15 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X14 @ X15)
% 0.40/0.61           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.61  thf('54', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X0 @ X1)
% 0.40/0.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['52', '53'])).
% 0.40/0.61  thf('55', plain,
% 0.40/0.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.61         ((r2_hidden @ X2 @ X3)
% 0.40/0.61          | (r2_hidden @ X2 @ X4)
% 0.40/0.61          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X4)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.40/0.61  thf('56', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.40/0.61          | (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1))
% 0.40/0.61          | (r2_hidden @ X2 @ X1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.40/0.61  thf('57', plain,
% 0.40/0.61      ((((r2_hidden @ sk_A @ sk_B)
% 0.40/0.61         | (r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_tarski @ sk_C_3) @ sk_B))))
% 0.40/0.61         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['51', '56'])).
% 0.40/0.61  thf('58', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.61  thf('59', plain,
% 0.40/0.61      ((((r2_hidden @ sk_A @ sk_B)
% 0.40/0.61         | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))))
% 0.40/0.61         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))))),
% 0.40/0.61      inference('demod', [status(thm)], ['57', '58'])).
% 0.40/0.61  thf('60', plain,
% 0.40/0.61      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))))),
% 0.40/0.61      inference('sat_resolution*', [status(thm)], ['7', '14', '15', '47', '48'])).
% 0.40/0.61  thf('61', plain,
% 0.40/0.61      (((r2_hidden @ sk_A @ sk_B)
% 0.40/0.61        | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))))),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.40/0.61  thf('62', plain,
% 0.40/0.61      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.61      inference('split', [status(esa)], ['10'])).
% 0.40/0.61  thf('63', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.40/0.61      inference('sat_resolution*', [status(thm)], ['7', '14', '15', '47'])).
% 0.40/0.61  thf('64', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 0.40/0.61  thf('65', plain,
% 0.40/0.61      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))),
% 0.40/0.61      inference('clc', [status(thm)], ['61', '64'])).
% 0.40/0.61  thf('66', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['19', '25'])).
% 0.40/0.61  thf('67', plain,
% 0.40/0.61      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)))),
% 0.40/0.61      inference('clc', [status(thm)], ['61', '64'])).
% 0.40/0.61  thf('68', plain,
% 0.40/0.61      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.40/0.61          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.40/0.61      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.61  thf('69', plain, (~ (r1_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3))),
% 0.40/0.61      inference('sup-', [status(thm)], ['67', '68'])).
% 0.40/0.61  thf('70', plain, ((r2_hidden @ sk_C_3 @ sk_B)),
% 0.40/0.61      inference('sup-', [status(thm)], ['66', '69'])).
% 0.40/0.61  thf('71', plain,
% 0.40/0.61      (![X46 : $i, X47 : $i]:
% 0.40/0.61         (((k3_xboole_0 @ X47 @ (k1_tarski @ X46)) = (k1_tarski @ X46))
% 0.40/0.61          | ~ (r2_hidden @ X46 @ X47))),
% 0.40/0.61      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.40/0.61  thf('72', plain,
% 0.40/0.61      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_3)) = (k1_tarski @ sk_C_3))),
% 0.40/0.61      inference('sup-', [status(thm)], ['70', '71'])).
% 0.40/0.61  thf('73', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_C_3))),
% 0.40/0.61      inference('demod', [status(thm)], ['65', '72'])).
% 0.40/0.61  thf('74', plain, ($false), inference('demod', [status(thm)], ['50', '73'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
