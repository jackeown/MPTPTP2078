%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GD2Db1vWyV

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:50 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 136 expanded)
%              Number of leaves         :   18 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  706 (1341 expanded)
%              Number of equality atoms :   32 (  62 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X17 != X16 )
      | ( r2_hidden @ X17 @ X18 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_tarski @ X16 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
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

thf('14',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('29',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['19','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(clc,[status(thm)],['18','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('33',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
    | ( sk_A = sk_C_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('41',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X5 ) )
      | ( r2_hidden @ X2 @ X5 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X5 ) )
      | ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_C_2 ) @ sk_B ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['38','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('50',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('51',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_2 ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( X19 = X16 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('56',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( sk_A = sk_C_2 )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,
    ( ( sk_A != sk_C_2 )
   <= ( sk_A != sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_2 )
      & ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
    | ( sk_A = sk_C_2 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','13','33','34','35','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GD2Db1vWyV
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.69  % Solved by: fo/fo7.sh
% 0.49/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.69  % done 689 iterations in 0.235s
% 0.49/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.69  % SZS output start Refutation
% 0.49/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.49/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.49/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.69  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.49/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.49/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.49/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.69  thf(t64_zfmisc_1, conjecture,
% 0.49/0.69    (![A:$i,B:$i,C:$i]:
% 0.49/0.69     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.49/0.69       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.49/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.69    (~( ![A:$i,B:$i,C:$i]:
% 0.49/0.69        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.49/0.69          ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ) )),
% 0.49/0.69    inference('cnf.neg', [status(esa)], [t64_zfmisc_1])).
% 0.49/0.69  thf('0', plain,
% 0.49/0.69      ((((sk_A) != (sk_C_2))
% 0.49/0.69        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('1', plain,
% 0.49/0.69      (~ (((sk_A) = (sk_C_2))) | 
% 0.49/0.69       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.49/0.69      inference('split', [status(esa)], ['0'])).
% 0.49/0.69  thf(d1_tarski, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.49/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.49/0.69  thf('2', plain,
% 0.49/0.69      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.49/0.69         (((X17) != (X16))
% 0.49/0.69          | (r2_hidden @ X17 @ X18)
% 0.49/0.69          | ((X18) != (k1_tarski @ X16)))),
% 0.49/0.69      inference('cnf', [status(esa)], [d1_tarski])).
% 0.49/0.69  thf('3', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_tarski @ X16))),
% 0.49/0.69      inference('simplify', [status(thm)], ['2'])).
% 0.49/0.69  thf('4', plain,
% 0.49/0.69      ((((sk_A) = (sk_C_2))
% 0.49/0.69        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.49/0.69        | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('5', plain, ((((sk_A) = (sk_C_2))) <= ((((sk_A) = (sk_C_2))))),
% 0.49/0.69      inference('split', [status(esa)], ['4'])).
% 0.49/0.69  thf(t79_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.49/0.69  thf('6', plain,
% 0.49/0.69      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 0.49/0.69      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.49/0.69  thf('7', plain,
% 0.49/0.69      (((r2_hidden @ sk_A @ sk_B)
% 0.49/0.69        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('8', plain,
% 0.49/0.69      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.49/0.69         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.49/0.69      inference('split', [status(esa)], ['7'])).
% 0.49/0.69  thf(t3_xboole_0, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.49/0.69            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.49/0.69       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.49/0.69            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.49/0.69  thf('9', plain,
% 0.49/0.69      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.49/0.69         (~ (r2_hidden @ X8 @ X6)
% 0.49/0.69          | ~ (r2_hidden @ X8 @ X9)
% 0.49/0.69          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.69  thf('10', plain,
% 0.49/0.69      ((![X0 : $i]:
% 0.49/0.69          (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)) @ X0)
% 0.49/0.69           | ~ (r2_hidden @ sk_A @ X0)))
% 0.49/0.69         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.49/0.69  thf('11', plain,
% 0.49/0.69      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.49/0.69         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['6', '10'])).
% 0.49/0.69  thf('12', plain,
% 0.49/0.69      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.49/0.69         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.49/0.69             (((sk_A) = (sk_C_2))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['5', '11'])).
% 0.49/0.69  thf('13', plain,
% 0.49/0.69      (~ (((sk_A) = (sk_C_2))) | 
% 0.49/0.69       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['3', '12'])).
% 0.49/0.69  thf('14', plain,
% 0.49/0.69      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.49/0.69         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.49/0.69      inference('split', [status(esa)], ['7'])).
% 0.49/0.69  thf(t100_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.49/0.69  thf('15', plain,
% 0.49/0.69      (![X10 : $i, X11 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X10 @ X11)
% 0.49/0.69           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.49/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.69  thf(t1_xboole_0, axiom,
% 0.49/0.69    (![A:$i,B:$i,C:$i]:
% 0.49/0.69     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.49/0.69       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.49/0.69  thf('16', plain,
% 0.49/0.69      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.49/0.69         ((r2_hidden @ X2 @ X3)
% 0.49/0.69          | (r2_hidden @ X2 @ X4)
% 0.49/0.69          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X4)))),
% 0.49/0.69      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.49/0.69  thf('17', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.69         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.49/0.69          | (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.49/0.69          | (r2_hidden @ X2 @ X1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['15', '16'])).
% 0.49/0.69  thf('18', plain,
% 0.49/0.69      ((((r2_hidden @ sk_A @ sk_B)
% 0.49/0.69         | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))
% 0.49/0.69         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['14', '17'])).
% 0.49/0.69  thf(t48_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.49/0.69  thf('19', plain,
% 0.49/0.69      (![X12 : $i, X13 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.49/0.69           = (k3_xboole_0 @ X12 @ X13))),
% 0.49/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.69  thf('20', plain,
% 0.49/0.69      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 0.49/0.69      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.49/0.69  thf('21', plain,
% 0.49/0.69      (![X6 : $i, X7 : $i]:
% 0.49/0.69         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.69  thf('22', plain,
% 0.49/0.69      (![X6 : $i, X7 : $i]:
% 0.49/0.69         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.69  thf('23', plain,
% 0.49/0.69      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.49/0.69         (~ (r2_hidden @ X8 @ X6)
% 0.49/0.69          | ~ (r2_hidden @ X8 @ X9)
% 0.49/0.69          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.69  thf('24', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.69         ((r1_xboole_0 @ X1 @ X0)
% 0.49/0.69          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.49/0.69          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.49/0.69      inference('sup-', [status(thm)], ['22', '23'])).
% 0.49/0.69  thf('25', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         ((r1_xboole_0 @ X0 @ X1)
% 0.49/0.69          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.49/0.69          | (r1_xboole_0 @ X0 @ X1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['21', '24'])).
% 0.49/0.69  thf('26', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.49/0.69      inference('simplify', [status(thm)], ['25'])).
% 0.49/0.69  thf('27', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['20', '26'])).
% 0.49/0.69  thf('28', plain,
% 0.49/0.69      ((![X0 : $i]:
% 0.49/0.69          (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)) @ X0)
% 0.49/0.69           | ~ (r2_hidden @ sk_A @ X0)))
% 0.49/0.69         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.49/0.69  thf('29', plain,
% 0.49/0.69      ((![X0 : $i]:
% 0.49/0.69          ~ (r2_hidden @ sk_A @ 
% 0.49/0.69             (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))
% 0.49/0.69         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.49/0.69  thf('30', plain,
% 0.49/0.69      ((~ (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.49/0.69         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['19', '29'])).
% 0.49/0.69  thf('31', plain,
% 0.49/0.69      (((r2_hidden @ sk_A @ sk_B))
% 0.49/0.69         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.49/0.69      inference('clc', [status(thm)], ['18', '30'])).
% 0.49/0.69  thf('32', plain,
% 0.49/0.69      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('split', [status(esa)], ['4'])).
% 0.49/0.69  thf('33', plain,
% 0.49/0.69      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.49/0.69       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['31', '32'])).
% 0.49/0.69  thf('34', plain,
% 0.49/0.69      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.49/0.69       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) | 
% 0.49/0.69       (((sk_A) = (sk_C_2)))),
% 0.49/0.69      inference('split', [status(esa)], ['4'])).
% 0.49/0.69  thf('35', plain,
% 0.49/0.69      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.49/0.69       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.49/0.69      inference('split', [status(esa)], ['7'])).
% 0.49/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.49/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.49/0.69  thf('36', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.69  thf('37', plain,
% 0.49/0.69      (![X10 : $i, X11 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X10 @ X11)
% 0.49/0.69           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.49/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.69  thf('38', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.49/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['36', '37'])).
% 0.49/0.69  thf('39', plain,
% 0.49/0.69      (![X10 : $i, X11 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X10 @ X11)
% 0.49/0.69           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.49/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.69  thf('40', plain,
% 0.49/0.69      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('split', [status(esa)], ['7'])).
% 0.49/0.69  thf('41', plain,
% 0.49/0.69      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.49/0.69         ((r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X5))
% 0.49/0.69          | (r2_hidden @ X2 @ X5)
% 0.49/0.69          | ~ (r2_hidden @ X2 @ X3))),
% 0.49/0.69      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.49/0.69  thf('42', plain,
% 0.49/0.69      ((![X0 : $i]:
% 0.49/0.69          ((r2_hidden @ sk_A @ X0)
% 0.49/0.69           | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))))
% 0.49/0.69         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['40', '41'])).
% 0.49/0.69  thf('43', plain,
% 0.49/0.69      ((![X0 : $i]:
% 0.49/0.69          ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.49/0.69           | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))))
% 0.49/0.69         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['39', '42'])).
% 0.49/0.69  thf('44', plain,
% 0.49/0.69      ((~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.49/0.69         <= (~
% 0.49/0.69             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.49/0.69      inference('split', [status(esa)], ['4'])).
% 0.49/0.69  thf('45', plain,
% 0.49/0.69      (((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.49/0.69         <= (~
% 0.49/0.69             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.49/0.69             ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['43', '44'])).
% 0.49/0.69  thf('46', plain,
% 0.49/0.69      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.49/0.69         ((r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X5))
% 0.49/0.69          | (r2_hidden @ X2 @ X3)
% 0.49/0.69          | ~ (r2_hidden @ X2 @ X5))),
% 0.49/0.69      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.49/0.69  thf('47', plain,
% 0.49/0.69      ((![X0 : $i]:
% 0.49/0.69          ((r2_hidden @ sk_A @ X0)
% 0.49/0.69           | (r2_hidden @ sk_A @ 
% 0.49/0.69              (k5_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))))
% 0.49/0.69         <= (~
% 0.49/0.69             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.49/0.69             ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['45', '46'])).
% 0.49/0.69  thf('48', plain,
% 0.49/0.69      ((((r2_hidden @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_C_2) @ sk_B))
% 0.49/0.69         | (r2_hidden @ sk_A @ (k1_tarski @ sk_C_2))))
% 0.49/0.69         <= (~
% 0.49/0.69             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.49/0.69             ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['38', '47'])).
% 0.49/0.69  thf('49', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['20', '26'])).
% 0.49/0.69  thf('50', plain,
% 0.49/0.69      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('split', [status(esa)], ['7'])).
% 0.49/0.69  thf('51', plain,
% 0.49/0.69      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.49/0.69         (~ (r2_hidden @ X8 @ X6)
% 0.49/0.69          | ~ (r2_hidden @ X8 @ X9)
% 0.49/0.69          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.69  thf('52', plain,
% 0.49/0.69      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_B @ X0) | ~ (r2_hidden @ sk_A @ X0)))
% 0.49/0.69         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['50', '51'])).
% 0.49/0.69  thf('53', plain,
% 0.49/0.69      ((![X0 : $i]: ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.49/0.69         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['49', '52'])).
% 0.49/0.69  thf('54', plain,
% 0.49/0.69      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.49/0.69         <= (~
% 0.49/0.69             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.49/0.69             ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('clc', [status(thm)], ['48', '53'])).
% 0.49/0.69  thf('55', plain,
% 0.49/0.69      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.49/0.69         (~ (r2_hidden @ X19 @ X18)
% 0.49/0.69          | ((X19) = (X16))
% 0.49/0.69          | ((X18) != (k1_tarski @ X16)))),
% 0.49/0.69      inference('cnf', [status(esa)], [d1_tarski])).
% 0.49/0.69  thf('56', plain,
% 0.49/0.69      (![X16 : $i, X19 : $i]:
% 0.49/0.69         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.49/0.69      inference('simplify', [status(thm)], ['55'])).
% 0.49/0.69  thf('57', plain,
% 0.49/0.69      ((((sk_A) = (sk_C_2)))
% 0.49/0.69         <= (~
% 0.49/0.69             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.49/0.69             ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['54', '56'])).
% 0.49/0.69  thf('58', plain, ((((sk_A) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 0.49/0.69      inference('split', [status(esa)], ['0'])).
% 0.49/0.69  thf('59', plain,
% 0.49/0.69      ((((sk_A) != (sk_A)))
% 0.49/0.69         <= (~ (((sk_A) = (sk_C_2))) & 
% 0.49/0.69             ~
% 0.49/0.69             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.49/0.69             ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['57', '58'])).
% 0.49/0.69  thf('60', plain,
% 0.49/0.69      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.49/0.69       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) | 
% 0.49/0.69       (((sk_A) = (sk_C_2)))),
% 0.49/0.69      inference('simplify', [status(thm)], ['59'])).
% 0.49/0.69  thf('61', plain, ($false),
% 0.49/0.69      inference('sat_resolution*', [status(thm)],
% 0.49/0.69                ['1', '13', '33', '34', '35', '60'])).
% 0.49/0.69  
% 0.49/0.69  % SZS output end Refutation
% 0.49/0.69  
% 0.49/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
