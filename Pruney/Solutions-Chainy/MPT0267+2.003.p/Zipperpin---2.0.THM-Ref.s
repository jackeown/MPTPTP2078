%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YzYxQPZ1Dp

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:50 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 133 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  754 (1279 expanded)
%              Number of equality atoms :   36 (  67 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('0',plain,
    ( ( sk_A != sk_C_2 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != sk_C_2 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X21 != X20 )
      | ( r2_hidden @ X21 @ X22 )
      | ( X22
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X20: $i] :
      ( r2_hidden @ X20 @ ( k1_tarski @ X20 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( sk_A = sk_C_2 )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A = sk_C_2 )
   <= ( sk_A = sk_C_2 ) ),
    inference(split,[status(esa)],['4'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['7'])).

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

thf('9',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_2 ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
      & ( sk_A = sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,
    ( ( sk_A != sk_C_2 )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ sk_B )
        | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) )
        | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['22','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('43',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
    | ( sk_A = sk_C_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf('46',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('47',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X5 ) )
      | ( r2_hidden @ X2 @ X5 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 )
        | ~ ( r2_hidden @ sk_A @ X1 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('58',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_2 ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( X23 = X20 )
      | ( X22
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('60',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23 = X20 )
      | ~ ( r2_hidden @ X23 @ ( k1_tarski @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( sk_A = sk_C_2 )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,
    ( ( sk_A != sk_C_2 )
   <= ( sk_A != sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_2 )
      & ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
    | ( sk_A = sk_C_2 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','13','43','44','45','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YzYxQPZ1Dp
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:43:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 330 iterations in 0.103s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.56  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(t64_zfmisc_1, conjecture,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.37/0.56       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.56        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.37/0.56          ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t64_zfmisc_1])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      ((((sk_A) != (sk_C_2))
% 0.37/0.56        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (~ (((sk_A) = (sk_C_2))) | 
% 0.37/0.56       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf(d1_tarski, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.56         (((X21) != (X20))
% 0.37/0.56          | (r2_hidden @ X21 @ X22)
% 0.37/0.56          | ((X22) != (k1_tarski @ X20)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.56  thf('3', plain, (![X20 : $i]: (r2_hidden @ X20 @ (k1_tarski @ X20))),
% 0.37/0.56      inference('simplify', [status(thm)], ['2'])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      ((((sk_A) = (sk_C_2))
% 0.37/0.56        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.37/0.56        | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('5', plain, ((((sk_A) = (sk_C_2))) <= ((((sk_A) = (sk_C_2))))),
% 0.37/0.56      inference('split', [status(esa)], ['4'])).
% 0.37/0.56  thf(t79_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 0.37/0.56      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (((r2_hidden @ sk_A @ sk_B)
% 0.37/0.56        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.37/0.56      inference('split', [status(esa)], ['7'])).
% 0.37/0.56  thf(t3_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.37/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.56            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X8 @ X6)
% 0.37/0.56          | ~ (r2_hidden @ X8 @ X9)
% 0.37/0.56          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)) @ X0)
% 0.37/0.56           | ~ (r2_hidden @ sk_A @ X0)))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '10'])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.37/0.56             (((sk_A) = (sk_C_2))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '11'])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (~ (((sk_A) = (sk_C_2))) | 
% 0.37/0.56       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '12'])).
% 0.37/0.56  thf(t17_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 0.37/0.56      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.37/0.56  thf(t28_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X16 : $i, X17 : $i]:
% 0.37/0.56         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.37/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.37/0.56           = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.56  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.37/0.56           = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf(t100_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X12 @ X13)
% 0.37/0.56           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.56           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X12 @ X13)
% 0.37/0.56           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X1 @ X0)
% 0.37/0.56           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['20', '21'])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 0.37/0.56      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X8 @ X6)
% 0.37/0.56          | ~ (r2_hidden @ X8 @ X9)
% 0.37/0.56          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ X1 @ X0)
% 0.37/0.56          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.37/0.56          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.37/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ X0 @ X1)
% 0.37/0.56          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.37/0.56          | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['24', '27'])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['23', '29'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.37/0.56      inference('split', [status(esa)], ['7'])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X12 @ X13)
% 0.37/0.56           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf(t1_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.37/0.56       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.56         ((r2_hidden @ X2 @ X3)
% 0.37/0.56          | (r2_hidden @ X2 @ X4)
% 0.37/0.56          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X4)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.37/0.56          | (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.56          | (r2_hidden @ X2 @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      ((((r2_hidden @ sk_A @ sk_B)
% 0.37/0.56         | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['31', '34'])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X8 @ X6)
% 0.37/0.56          | ~ (r2_hidden @ X8 @ X9)
% 0.37/0.56          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          ((r2_hidden @ sk_A @ sk_B)
% 0.37/0.56           | ~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)) @ X0)
% 0.37/0.56           | ~ (r2_hidden @ sk_A @ X0)))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          (~ (r2_hidden @ sk_A @ 
% 0.37/0.56              (k4_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.37/0.56           | (r2_hidden @ sk_A @ sk_B)))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['30', '37'])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (((~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))
% 0.37/0.56         | (r2_hidden @ sk_A @ sk_B)))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['22', '38'])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.37/0.56      inference('split', [status(esa)], ['7'])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      (((r2_hidden @ sk_A @ sk_B))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.37/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.56      inference('split', [status(esa)], ['4'])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.56       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.56       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) | 
% 0.37/0.56       (((sk_A) = (sk_C_2)))),
% 0.37/0.56      inference('split', [status(esa)], ['4'])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.56       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.37/0.56      inference('split', [status(esa)], ['7'])).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.56      inference('split', [status(esa)], ['7'])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.37/0.56         ((r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X5))
% 0.37/0.56          | (r2_hidden @ X2 @ X5)
% 0.37/0.56          | ~ (r2_hidden @ X2 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.37/0.56  thf('48', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          ((r2_hidden @ sk_A @ X0)
% 0.37/0.56           | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.37/0.56  thf(l97_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         (r1_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k5_xboole_0 @ X10 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X12 @ X13)
% 0.37/0.56           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          ((r2_hidden @ sk_A @ X0)
% 0.37/0.56           | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.37/0.56           | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['50', '51'])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X8 @ X6)
% 0.37/0.56          | ~ (r2_hidden @ X8 @ X9)
% 0.37/0.56          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      ((![X0 : $i, X1 : $i]:
% 0.37/0.56          ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.37/0.56           | ~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ X1)
% 0.37/0.56           | ~ (r2_hidden @ sk_A @ X1)))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          (~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))
% 0.37/0.56           | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['49', '54'])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          ((r2_hidden @ sk_A @ X0)
% 0.37/0.56           | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['48', '55'])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      ((~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.37/0.56      inference('split', [status(esa)], ['4'])).
% 0.37/0.56  thf('58', plain,
% 0.37/0.56      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.37/0.56             ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X23 @ X22)
% 0.37/0.56          | ((X23) = (X20))
% 0.37/0.56          | ((X22) != (k1_tarski @ X20)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.56  thf('60', plain,
% 0.37/0.56      (![X20 : $i, X23 : $i]:
% 0.37/0.56         (((X23) = (X20)) | ~ (r2_hidden @ X23 @ (k1_tarski @ X20)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['59'])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      ((((sk_A) = (sk_C_2)))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.37/0.56             ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['58', '60'])).
% 0.37/0.56  thf('62', plain, ((((sk_A) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      ((((sk_A) != (sk_A)))
% 0.37/0.56         <= (~ (((sk_A) = (sk_C_2))) & 
% 0.37/0.56             ~
% 0.37/0.56             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.37/0.56             ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.56  thf('64', plain,
% 0.37/0.56      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.56       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) | 
% 0.37/0.56       (((sk_A) = (sk_C_2)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['63'])).
% 0.37/0.56  thf('65', plain, ($false),
% 0.37/0.56      inference('sat_resolution*', [status(thm)],
% 0.37/0.56                ['1', '13', '43', '44', '45', '64'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.40/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
