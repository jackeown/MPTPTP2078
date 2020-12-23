%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YDf4nWQsFi

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 129 expanded)
%              Number of leaves         :   19 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  698 (1244 expanded)
%              Number of equality atoms :   35 (  66 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19 != X18 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
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
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X2 @ X3 ) ) ) ),
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

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
    | ( sk_A = sk_C_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X1 @ ( k5_xboole_0 @ X2 @ X4 ) )
      | ( r2_hidden @ X1 @ X4 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k5_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('49',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('50',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ~ ( r1_xboole_0 @ ( k5_xboole_0 @ sk_B @ X0 ) @ X1 )
        | ~ ( r2_hidden @ sk_A @ X1 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('54',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_2 ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_2 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('56',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
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
    inference('sat_resolution*',[status(thm)],['1','13','32','33','34','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YDf4nWQsFi
% 0.11/0.33  % Computer   : n023.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 20:24:36 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.34  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 218 iterations in 0.106s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.56  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.56  thf(t64_zfmisc_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.20/0.56       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.56        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.20/0.56          ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t64_zfmisc_1])).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      ((((sk_A) != (sk_C_2))
% 0.20/0.56        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (~ (((sk_A) = (sk_C_2))) | 
% 0.20/0.56       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf(d1_tarski, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.56         (((X19) != (X18))
% 0.20/0.56          | (r2_hidden @ X19 @ X20)
% 0.20/0.56          | ((X20) != (k1_tarski @ X18)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.56  thf('3', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 0.20/0.56      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      ((((sk_A) = (sk_C_2))
% 0.20/0.56        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.20/0.56        | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('5', plain, ((((sk_A) = (sk_C_2))) <= ((((sk_A) = (sk_C_2))))),
% 0.20/0.56      inference('split', [status(esa)], ['4'])).
% 0.20/0.56  thf(t79_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.20/0.56      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (((r2_hidden @ sk_A @ sk_B)
% 0.20/0.56        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.20/0.56      inference('split', [status(esa)], ['7'])).
% 0.20/0.56  thf(t3_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.56            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X7 @ X5)
% 0.20/0.56          | ~ (r2_hidden @ X7 @ X8)
% 0.20/0.56          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)) @ X0)
% 0.20/0.56           | ~ (r2_hidden @ sk_A @ X0)))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['6', '10'])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.20/0.56             (((sk_A) = (sk_C_2))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['5', '11'])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (~ (((sk_A) = (sk_C_2))) | 
% 0.20/0.56       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '12'])).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.20/0.56      inference('split', [status(esa)], ['7'])).
% 0.20/0.56  thf(t100_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X11 @ X12)
% 0.20/0.56           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.56  thf(t1_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.20/0.56       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.56         ((r2_hidden @ X1 @ X2)
% 0.20/0.56          | (r2_hidden @ X1 @ X3)
% 0.20/0.56          | ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X2 @ X3)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.56          | (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.56          | (r2_hidden @ X2 @ X1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      ((((r2_hidden @ sk_A @ sk_B)
% 0.20/0.56         | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['14', '17'])).
% 0.20/0.56  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.56  thf('19', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.56      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.56  thf(t16_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.56       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.56         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 0.20/0.56           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k3_xboole_0 @ X0 @ X1)
% 0.20/0.56           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X11 @ X12)
% 0.20/0.56           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.56           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X11 @ X12)
% 0.20/0.56           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X1 @ X0)
% 0.20/0.56           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.20/0.56      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)) @ X0)
% 0.20/0.56           | ~ (r2_hidden @ sk_A @ X0)))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (((r2_hidden @ sk_A @ sk_B))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '29'])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.56      inference('split', [status(esa)], ['4'])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.20/0.56       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.20/0.56       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) | 
% 0.20/0.56       (((sk_A) = (sk_C_2)))),
% 0.20/0.56      inference('split', [status(esa)], ['4'])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.20/0.56       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))),
% 0.20/0.56      inference('split', [status(esa)], ['7'])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X11 @ X12)
% 0.20/0.56           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.56      inference('split', [status(esa)], ['7'])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.56         ((r2_hidden @ X1 @ (k5_xboole_0 @ X2 @ X4))
% 0.20/0.56          | (r2_hidden @ X1 @ X4)
% 0.20/0.56          | ~ (r2_hidden @ X1 @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((r2_hidden @ sk_A @ X0)
% 0.20/0.56           | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.20/0.56           | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['35', '38'])).
% 0.20/0.56  thf(l97_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i]:
% 0.20/0.56         (r1_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k5_xboole_0 @ X9 @ X10))),
% 0.20/0.56      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X7 @ X5)
% 0.20/0.56          | ~ (r2_hidden @ X7 @ X8)
% 0.20/0.56          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         ((r1_xboole_0 @ X1 @ X0)
% 0.20/0.56          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.56          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.20/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.56          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.20/0.56          | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['41', '44'])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.56      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (r1_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['40', '46'])).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((r2_hidden @ sk_A @ X0)
% 0.20/0.56           | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X7 @ X5)
% 0.20/0.56          | ~ (r2_hidden @ X7 @ X8)
% 0.20/0.56          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      ((![X0 : $i, X1 : $i]:
% 0.20/0.56          ((r2_hidden @ sk_A @ X0)
% 0.20/0.56           | ~ (r1_xboole_0 @ (k5_xboole_0 @ sk_B @ X0) @ X1)
% 0.20/0.56           | ~ (r2_hidden @ sk_A @ X1)))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          (~ (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.20/0.56           | (r2_hidden @ sk_A @ X0)))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['47', '50'])).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.20/0.56           | (r2_hidden @ sk_A @ X0)))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['39', '51'])).
% 0.20/0.56  thf('53', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2))))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))))),
% 0.20/0.56      inference('split', [status(esa)], ['4'])).
% 0.20/0.56  thf('54', plain,
% 0.20/0.56      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.20/0.56             ((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.56  thf('55', plain,
% 0.20/0.56      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X21 @ X20)
% 0.20/0.56          | ((X21) = (X18))
% 0.20/0.56          | ((X20) != (k1_tarski @ X18)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.56  thf('56', plain,
% 0.20/0.56      (![X18 : $i, X21 : $i]:
% 0.20/0.56         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.56  thf('57', plain,
% 0.20/0.56      ((((sk_A) = (sk_C_2)))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.20/0.56             ((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['54', '56'])).
% 0.20/0.56  thf('58', plain, ((((sk_A) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      ((((sk_A) != (sk_A)))
% 0.20/0.56         <= (~ (((sk_A) = (sk_C_2))) & 
% 0.20/0.56             ~
% 0.20/0.56             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) & 
% 0.20/0.56             ((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.56  thf('60', plain,
% 0.20/0.56      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.20/0.56       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_2)))) | 
% 0.20/0.56       (((sk_A) = (sk_C_2)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.56  thf('61', plain, ($false),
% 0.20/0.56      inference('sat_resolution*', [status(thm)],
% 0.20/0.56                ['1', '13', '32', '33', '34', '60'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
