%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2TdrOCqscs

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:50 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 126 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  699 (1224 expanded)
%              Number of equality atoms :   32 (  62 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(clc,[status(thm)],['18','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
    | ( sk_A = sk_C_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('34',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X5 ) )
      | ( r2_hidden @ X2 @ X5 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X5 ) )
      | ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_C_2 ) @ sk_B ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['31','40'])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('45',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

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
    inference(clc,[status(thm)],['41','53'])).

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
    inference('sat_resolution*',[status(thm)],['1','13','26','27','28','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2TdrOCqscs
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:20:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.76  % Solved by: fo/fo7.sh
% 0.54/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.76  % done 630 iterations in 0.300s
% 0.54/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.76  % SZS output start Refutation
% 0.54/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.76  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.54/0.76  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.54/0.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.76  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.76  thf(t64_zfmisc_1, conjecture,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.54/0.76       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.54/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.76    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.76        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.54/0.76          ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ) )),
% 0.54/0.76    inference('cnf.neg', [status(esa)], [t64_zfmisc_1])).
% 0.54/0.76  thf('0', plain,
% 0.54/0.76      ((((sk_A) != (sk_C_2))
% 0.54/0.76        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('1', plain,
% 0.54/0.76      (~ (((sk_A) = (sk_C_2))) | 
% 0.54/0.76       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.54/0.76      inference('split', [status(esa)], ['0'])).
% 0.54/0.76  thf(d1_tarski, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.54/0.76       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.54/0.76  thf('2', plain,
% 0.54/0.76      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.54/0.76         (((X17) != (X16))
% 0.54/0.76          | (r2_hidden @ X17 @ X18)
% 0.54/0.76          | ((X18) != (k1_tarski @ X16)))),
% 0.54/0.76      inference('cnf', [status(esa)], [d1_tarski])).
% 0.54/0.76  thf('3', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_tarski @ X16))),
% 0.54/0.76      inference('simplify', [status(thm)], ['2'])).
% 0.54/0.76  thf('4', plain,
% 0.54/0.76      ((((sk_A) = (sk_C_2))
% 0.54/0.76        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.54/0.76        | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('5', plain, ((((sk_A) = (sk_C_2))) <= ((((sk_A) = (sk_C_2))))),
% 0.54/0.76      inference('split', [status(esa)], ['4'])).
% 0.54/0.76  thf(t79_xboole_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.54/0.76  thf('6', plain,
% 0.54/0.76      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 0.54/0.76      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.54/0.76  thf('7', plain,
% 0.54/0.76      (((r2_hidden @ sk_A @ sk_B)
% 0.54/0.76        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('8', plain,
% 0.54/0.76      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.54/0.76         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.54/0.76      inference('split', [status(esa)], ['7'])).
% 0.54/0.76  thf(t3_xboole_0, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.54/0.76            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.54/0.76       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.54/0.76            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.54/0.76  thf('9', plain,
% 0.54/0.76      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X8 @ X6)
% 0.54/0.76          | ~ (r2_hidden @ X8 @ X9)
% 0.54/0.76          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.54/0.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.76  thf('10', plain,
% 0.54/0.76      ((![X0 : $i]:
% 0.54/0.76          (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)) @ X0)
% 0.54/0.76           | ~ (r2_hidden @ sk_A @ X0)))
% 0.54/0.76         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.76  thf('11', plain,
% 0.54/0.76      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.54/0.76         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['6', '10'])).
% 0.54/0.76  thf('12', plain,
% 0.54/0.76      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.54/0.76         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.54/0.76             (((sk_A) = (sk_C_2))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['5', '11'])).
% 0.54/0.76  thf('13', plain,
% 0.54/0.76      (~ (((sk_A) = (sk_C_2))) | 
% 0.54/0.76       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['3', '12'])).
% 0.54/0.76  thf('14', plain,
% 0.54/0.76      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.54/0.76         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.54/0.76      inference('split', [status(esa)], ['7'])).
% 0.54/0.76  thf(t100_xboole_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.76  thf('15', plain,
% 0.54/0.76      (![X10 : $i, X11 : $i]:
% 0.54/0.76         ((k4_xboole_0 @ X10 @ X11)
% 0.54/0.76           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.76  thf(t1_xboole_0, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.54/0.76       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.54/0.76  thf('16', plain,
% 0.54/0.76      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.54/0.76         ((r2_hidden @ X2 @ X3)
% 0.54/0.76          | (r2_hidden @ X2 @ X4)
% 0.54/0.76          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X4)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.54/0.76  thf('17', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.54/0.76          | (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.54/0.76          | (r2_hidden @ X2 @ X1))),
% 0.54/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.54/0.76  thf('18', plain,
% 0.54/0.76      ((((r2_hidden @ sk_A @ sk_B)
% 0.54/0.76         | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))
% 0.54/0.76         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['14', '17'])).
% 0.54/0.76  thf(t47_xboole_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.54/0.76  thf('19', plain,
% 0.54/0.76      (![X12 : $i, X13 : $i]:
% 0.54/0.76         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.54/0.76           = (k4_xboole_0 @ X12 @ X13))),
% 0.54/0.76      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.54/0.76  thf('20', plain,
% 0.54/0.76      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 0.54/0.76      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.54/0.76  thf('21', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))),
% 0.54/0.76      inference('sup+', [status(thm)], ['19', '20'])).
% 0.54/0.76  thf('22', plain,
% 0.54/0.76      ((![X0 : $i]:
% 0.54/0.76          (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)) @ X0)
% 0.54/0.76           | ~ (r2_hidden @ sk_A @ X0)))
% 0.54/0.76         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.76  thf('23', plain,
% 0.54/0.76      ((~ (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.54/0.76         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['21', '22'])).
% 0.54/0.76  thf('24', plain,
% 0.54/0.76      (((r2_hidden @ sk_A @ sk_B))
% 0.54/0.76         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.54/0.76      inference('clc', [status(thm)], ['18', '23'])).
% 0.54/0.76  thf('25', plain,
% 0.54/0.76      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.54/0.76      inference('split', [status(esa)], ['4'])).
% 0.54/0.76  thf('26', plain,
% 0.54/0.76      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.54/0.76       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.76  thf('27', plain,
% 0.54/0.76      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.54/0.76       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) | 
% 0.54/0.76       (((sk_A) = (sk_C_2)))),
% 0.54/0.76      inference('split', [status(esa)], ['4'])).
% 0.54/0.76  thf('28', plain,
% 0.54/0.76      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.54/0.76       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.54/0.76      inference('split', [status(esa)], ['7'])).
% 0.54/0.76  thf(commutativity_k3_xboole_0, axiom,
% 0.54/0.76    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.54/0.76  thf('29', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.76  thf('30', plain,
% 0.54/0.76      (![X10 : $i, X11 : $i]:
% 0.54/0.76         ((k4_xboole_0 @ X10 @ X11)
% 0.54/0.76           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.76  thf('31', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         ((k4_xboole_0 @ X0 @ X1)
% 0.54/0.76           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['29', '30'])).
% 0.54/0.76  thf('32', plain,
% 0.54/0.76      (![X10 : $i, X11 : $i]:
% 0.54/0.76         ((k4_xboole_0 @ X10 @ X11)
% 0.54/0.76           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.76  thf('33', plain,
% 0.54/0.76      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.54/0.76      inference('split', [status(esa)], ['7'])).
% 0.54/0.76  thf('34', plain,
% 0.54/0.76      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.54/0.76         ((r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X5))
% 0.54/0.76          | (r2_hidden @ X2 @ X5)
% 0.54/0.76          | ~ (r2_hidden @ X2 @ X3))),
% 0.54/0.76      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.54/0.76  thf('35', plain,
% 0.54/0.76      ((![X0 : $i]:
% 0.54/0.76          ((r2_hidden @ sk_A @ X0)
% 0.54/0.76           | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))))
% 0.54/0.76         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['33', '34'])).
% 0.54/0.76  thf('36', plain,
% 0.54/0.76      ((![X0 : $i]:
% 0.54/0.76          ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.54/0.76           | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))))
% 0.54/0.76         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['32', '35'])).
% 0.54/0.76  thf('37', plain,
% 0.54/0.76      ((~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.54/0.76         <= (~
% 0.54/0.76             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.54/0.76      inference('split', [status(esa)], ['4'])).
% 0.54/0.76  thf('38', plain,
% 0.54/0.76      (((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.54/0.76         <= (~
% 0.54/0.76             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.54/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['36', '37'])).
% 0.54/0.76  thf('39', plain,
% 0.54/0.76      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.54/0.76         ((r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X5))
% 0.54/0.76          | (r2_hidden @ X2 @ X3)
% 0.54/0.76          | ~ (r2_hidden @ X2 @ X5))),
% 0.54/0.76      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.54/0.76  thf('40', plain,
% 0.54/0.76      ((![X0 : $i]:
% 0.54/0.76          ((r2_hidden @ sk_A @ X0)
% 0.54/0.76           | (r2_hidden @ sk_A @ 
% 0.54/0.76              (k5_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))))
% 0.54/0.76         <= (~
% 0.54/0.76             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.54/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['38', '39'])).
% 0.54/0.76  thf('41', plain,
% 0.54/0.76      ((((r2_hidden @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_C_2) @ sk_B))
% 0.54/0.76         | (r2_hidden @ sk_A @ (k1_tarski @ sk_C_2))))
% 0.54/0.76         <= (~
% 0.54/0.76             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.54/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['31', '40'])).
% 0.54/0.76  thf('42', plain,
% 0.54/0.76      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 0.54/0.76      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.54/0.76  thf('43', plain,
% 0.54/0.76      (![X6 : $i, X7 : $i]:
% 0.54/0.76         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.54/0.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.76  thf('44', plain,
% 0.54/0.76      (![X6 : $i, X7 : $i]:
% 0.54/0.76         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.54/0.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.76  thf('45', plain,
% 0.54/0.76      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X8 @ X6)
% 0.54/0.76          | ~ (r2_hidden @ X8 @ X9)
% 0.54/0.76          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.54/0.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.76  thf('46', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.76         ((r1_xboole_0 @ X1 @ X0)
% 0.54/0.76          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.54/0.76          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.54/0.76      inference('sup-', [status(thm)], ['44', '45'])).
% 0.54/0.76  thf('47', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         ((r1_xboole_0 @ X0 @ X1)
% 0.54/0.76          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.54/0.76          | (r1_xboole_0 @ X0 @ X1))),
% 0.54/0.76      inference('sup-', [status(thm)], ['43', '46'])).
% 0.54/0.76  thf('48', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.54/0.76      inference('simplify', [status(thm)], ['47'])).
% 0.54/0.76  thf('49', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['42', '48'])).
% 0.54/0.76  thf('50', plain,
% 0.54/0.76      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.54/0.76      inference('split', [status(esa)], ['7'])).
% 0.54/0.76  thf('51', plain,
% 0.54/0.76      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X8 @ X6)
% 0.54/0.76          | ~ (r2_hidden @ X8 @ X9)
% 0.54/0.76          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.54/0.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.76  thf('52', plain,
% 0.54/0.76      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_B @ X0) | ~ (r2_hidden @ sk_A @ X0)))
% 0.54/0.76         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['50', '51'])).
% 0.54/0.76  thf('53', plain,
% 0.54/0.76      ((![X0 : $i]: ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.54/0.76         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['49', '52'])).
% 0.54/0.76  thf('54', plain,
% 0.54/0.76      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.54/0.76         <= (~
% 0.54/0.76             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.54/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.54/0.76      inference('clc', [status(thm)], ['41', '53'])).
% 0.54/0.76  thf('55', plain,
% 0.54/0.76      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X19 @ X18)
% 0.54/0.76          | ((X19) = (X16))
% 0.54/0.76          | ((X18) != (k1_tarski @ X16)))),
% 0.54/0.76      inference('cnf', [status(esa)], [d1_tarski])).
% 0.54/0.76  thf('56', plain,
% 0.54/0.76      (![X16 : $i, X19 : $i]:
% 0.54/0.76         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.54/0.76      inference('simplify', [status(thm)], ['55'])).
% 0.54/0.76  thf('57', plain,
% 0.54/0.76      ((((sk_A) = (sk_C_2)))
% 0.54/0.76         <= (~
% 0.54/0.76             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.54/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['54', '56'])).
% 0.54/0.76  thf('58', plain, ((((sk_A) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 0.54/0.76      inference('split', [status(esa)], ['0'])).
% 0.54/0.76  thf('59', plain,
% 0.54/0.76      ((((sk_A) != (sk_A)))
% 0.54/0.76         <= (~ (((sk_A) = (sk_C_2))) & 
% 0.54/0.76             ~
% 0.54/0.76             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.54/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['57', '58'])).
% 0.54/0.76  thf('60', plain,
% 0.54/0.76      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.54/0.76       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) | 
% 0.54/0.76       (((sk_A) = (sk_C_2)))),
% 0.54/0.76      inference('simplify', [status(thm)], ['59'])).
% 0.54/0.76  thf('61', plain, ($false),
% 0.54/0.76      inference('sat_resolution*', [status(thm)],
% 0.54/0.76                ['1', '13', '26', '27', '28', '60'])).
% 0.54/0.76  
% 0.54/0.76  % SZS output end Refutation
% 0.54/0.76  
% 0.54/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
