%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GXTEAjDUiK

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 233 expanded)
%              Number of leaves         :   14 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  857 (2412 expanded)
%              Number of equality atoms :   53 ( 154 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

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
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X9 ) )
      | ( r2_hidden @ X6 @ X9 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('4',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,
    ( ( sk_A = sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X13 != X12 )
      | ( r2_hidden @ X13 @ X14 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X12: $i] :
      ( r2_hidden @ X12 @ ( k1_tarski @ X12 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ~ ( r2_hidden @ sk_A @ sk_B )
      | ~ ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( sk_A != sk_C_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('36',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['7','24','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(simpl_trail,[status(thm)],['5','36'])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('39',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('42',plain,(
    ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['7','24','34'])).

thf('43',plain,(
    ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('46',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    sk_A = sk_C_1 ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,
    ( ( sk_A != sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( sk_A != sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('51',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('52',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['52'])).

thf('54',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['52'])).

thf('57',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['52'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['51','63'])).

thf('65',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('66',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('68',plain,
    ( ( ~ ( r2_hidden @ sk_A @ sk_B )
      | ~ ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('70',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X12: $i] :
      ( r2_hidden @ X12 @ ( k1_tarski @ X12 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('74',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
    | ( sk_A != sk_C_1 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    sk_A != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['50','74'])).

thf('76',plain,(
    sk_A != sk_C_1 ),
    inference(simpl_trail,[status(thm)],['49','75'])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GXTEAjDUiK
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 331 iterations in 0.131s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(t100_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X10 @ X11)
% 0.21/0.57           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.57  thf(t64_zfmisc_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.57       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.57        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.57          ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t64_zfmisc_1])).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (((r2_hidden @ sk_A @ sk_B)
% 0.21/0.57        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.21/0.57      inference('split', [status(esa)], ['1'])).
% 0.21/0.57  thf(t1_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.21/0.57       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.21/0.57         ((r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X9))
% 0.21/0.57          | (r2_hidden @ X6 @ X9)
% 0.21/0.58          | ~ (r2_hidden @ X6 @ X7))),
% 0.21/0.58      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      ((![X0 : $i]:
% 0.21/0.58          ((r2_hidden @ sk_A @ X0)
% 0.21/0.58           | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      ((![X0 : $i]:
% 0.21/0.58          ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.21/0.58           | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['0', '4'])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      ((((sk_A) = (sk_C_1))
% 0.21/0.58        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.21/0.58        | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('7', plain,
% 0.21/0.58      (~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) | 
% 0.21/0.58       ~ ((r2_hidden @ sk_A @ sk_B)) | (((sk_A) = (sk_C_1)))),
% 0.21/0.58      inference('split', [status(esa)], ['6'])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.21/0.58      inference('split', [status(esa)], ['1'])).
% 0.21/0.58  thf(d1_tarski, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.58         (((X13) != (X12))
% 0.21/0.58          | (r2_hidden @ X13 @ X14)
% 0.21/0.58          | ((X14) != (k1_tarski @ X12)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.58  thf('10', plain, (![X12 : $i]: (r2_hidden @ X12 @ (k1_tarski @ X12))),
% 0.21/0.58      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.58  thf(d4_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.58       ( ![D:$i]:
% 0.21/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.58           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.58          | ~ (r2_hidden @ X0 @ X2)
% 0.21/0.58          | (r2_hidden @ X0 @ X3)
% 0.21/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.21/0.58          | ~ (r2_hidden @ X0 @ X2)
% 0.21/0.58          | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.58          | (r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['8', '13'])).
% 0.21/0.58  thf('15', plain, ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (sk_C_1))))),
% 0.21/0.58      inference('split', [status(esa)], ['6'])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.21/0.58      inference('split', [status(esa)], ['1'])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.21/0.58             (((sk_A) = (sk_C_1))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      (![X10 : $i, X11 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X10 @ X11)
% 0.21/0.58           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X6 @ X7)
% 0.21/0.58          | ~ (r2_hidden @ X6 @ X8)
% 0.21/0.58          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.21/0.58          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.58          | ~ (r2_hidden @ X2 @ X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      (((~ (r2_hidden @ sk_A @ sk_B)
% 0.21/0.58         | ~ (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.21/0.58             (((sk_A) = (sk_C_1))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      ((~ (r2_hidden @ sk_A @ sk_B))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.21/0.58             ((r2_hidden @ sk_A @ sk_B)) & 
% 0.21/0.58             (((sk_A) = (sk_C_1))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['14', '21'])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.21/0.58      inference('split', [status(esa)], ['1'])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      (~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) | 
% 0.21/0.58       ~ ((r2_hidden @ sk_A @ sk_B)) | ~ (((sk_A) = (sk_C_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.21/0.58      inference('split', [status(esa)], ['1'])).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      (![X10 : $i, X11 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X10 @ X11)
% 0.21/0.58           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.58  thf('27', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.58         ((r2_hidden @ X6 @ X7)
% 0.21/0.58          | (r2_hidden @ X6 @ X8)
% 0.21/0.58          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.21/0.58          | (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.58          | (r2_hidden @ X2 @ X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.58          | (r2_hidden @ X4 @ X1)
% 0.21/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.58         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         ((r2_hidden @ X2 @ X1) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.58      inference('clc', [status(thm)], ['28', '30'])).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ sk_B))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['25', '31'])).
% 0.21/0.58  thf('33', plain,
% 0.21/0.58      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.21/0.58      inference('split', [status(esa)], ['6'])).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.21/0.58       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.21/0.58       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.21/0.58      inference('split', [status(esa)], ['1'])).
% 0.21/0.58  thf('36', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['7', '24', '34', '35'])).
% 0.21/0.58  thf('37', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.21/0.58          | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['5', '36'])).
% 0.21/0.58  thf('38', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.58          | (r2_hidden @ X4 @ X2)
% 0.21/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.58         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.21/0.58          | (r2_hidden @ sk_A @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['37', '39'])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      ((~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.21/0.58      inference('split', [status(esa)], ['6'])).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      (~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['7', '24', '34'])).
% 0.21/0.58  thf('43', plain,
% 0.21/0.58      (~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['41', '42'])).
% 0.21/0.58  thf('44', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['40', '43'])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X15 @ X14)
% 0.21/0.58          | ((X15) = (X12))
% 0.21/0.58          | ((X14) != (k1_tarski @ X12)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.58  thf('46', plain,
% 0.21/0.58      (![X12 : $i, X15 : $i]:
% 0.21/0.58         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.58  thf('47', plain, (((sk_A) = (sk_C_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['44', '46'])).
% 0.21/0.58  thf('48', plain,
% 0.21/0.58      ((((sk_A) != (sk_C_1))
% 0.21/0.58        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('49', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 0.21/0.58      inference('split', [status(esa)], ['48'])).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      (~ (((sk_A) = (sk_C_1))) | 
% 0.21/0.58       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.21/0.58      inference('split', [status(esa)], ['48'])).
% 0.21/0.58  thf('51', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ sk_B))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['25', '31'])).
% 0.21/0.58  thf('52', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.21/0.58         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.21/0.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.21/0.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.58  thf('53', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.58          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.58      inference('eq_fact', [status(thm)], ['52'])).
% 0.21/0.58  thf('54', plain,
% 0.21/0.58      (![X12 : $i, X15 : $i]:
% 0.21/0.58         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.58  thf('55', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.21/0.58          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.58  thf('56', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.58          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.58      inference('eq_fact', [status(thm)], ['52'])).
% 0.21/0.58  thf('57', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.21/0.58         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.21/0.58          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.21/0.58          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.21/0.58          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.58  thf('58', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.21/0.58          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.58          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.21/0.58          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.58  thf('59', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.21/0.58          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.58          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['58'])).
% 0.21/0.58  thf('60', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.58          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.58      inference('eq_fact', [status(thm)], ['52'])).
% 0.21/0.58  thf('61', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.21/0.58          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.21/0.58      inference('clc', [status(thm)], ['59', '60'])).
% 0.21/0.58  thf('62', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.58          | ((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.21/0.58          | ((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['55', '61'])).
% 0.21/0.58  thf('63', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.21/0.58          | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.58      inference('simplify', [status(thm)], ['62'])).
% 0.21/0.58  thf('64', plain,
% 0.21/0.58      ((((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['51', '63'])).
% 0.21/0.58  thf('65', plain, ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (sk_C_1))))),
% 0.21/0.58      inference('split', [status(esa)], ['6'])).
% 0.21/0.58  thf('66', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.21/0.58      inference('split', [status(esa)], ['1'])).
% 0.21/0.58  thf('67', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.21/0.58          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.58          | ~ (r2_hidden @ X2 @ X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.58  thf('68', plain,
% 0.21/0.58      (((~ (r2_hidden @ sk_A @ sk_B)
% 0.21/0.58         | ~ (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.58  thf('69', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ sk_B))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['25', '31'])).
% 0.21/0.58  thf('70', plain,
% 0.21/0.58      ((~ (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['68', '69'])).
% 0.21/0.58  thf('71', plain,
% 0.21/0.58      ((~ (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.21/0.58             (((sk_A) = (sk_C_1))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['65', '70'])).
% 0.21/0.58  thf('72', plain,
% 0.21/0.58      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.21/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.21/0.58             (((sk_A) = (sk_C_1))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['64', '71'])).
% 0.21/0.58  thf('73', plain, (![X12 : $i]: (r2_hidden @ X12 @ (k1_tarski @ X12))),
% 0.21/0.58      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.58  thf('74', plain,
% 0.21/0.58      (~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) | 
% 0.21/0.58       ~ (((sk_A) = (sk_C_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['72', '73'])).
% 0.21/0.58  thf('75', plain, (~ (((sk_A) = (sk_C_1)))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['50', '74'])).
% 0.21/0.58  thf('76', plain, (((sk_A) != (sk_C_1))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['49', '75'])).
% 0.21/0.58  thf('77', plain, ($false),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['47', '76'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
