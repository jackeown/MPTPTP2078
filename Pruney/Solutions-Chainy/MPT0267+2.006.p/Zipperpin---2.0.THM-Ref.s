%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U13nCOoUcb

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:50 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 239 expanded)
%              Number of leaves         :   20 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  907 (2260 expanded)
%              Number of equality atoms :   54 ( 171 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ( ( sk_A = sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
    | ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A != sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_A != sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

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
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('24',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['22','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','25'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('27',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X34 != X33 )
      | ( r2_hidden @ X34 @ X35 )
      | ( X35
       != ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('28',plain,(
    ! [X33: $i] :
      ( r2_hidden @ X33 @ ( k1_tarski @ X33 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( sk_A != sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('34',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X11 ) )
      | ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['22','24'])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('42',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('50',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('51',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X11 ) )
      | ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ X0 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('61',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('66',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('67',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','68'])).

thf('70',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','69'])).

thf('71',plain,(
    ! [X33: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X36 @ X35 )
      | ( X36 = X33 )
      | ( X35
       != ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('72',plain,(
    ! [X33: $i,X36: $i] :
      ( ( X36 = X33 )
      | ~ ( r2_hidden @ X36 @ ( k1_tarski @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_A = sk_C_1 )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('75',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_1 )
      & ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
    | ( sk_A = sk_C_1 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','29','47','48','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U13nCOoUcb
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.72/2.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.72/2.93  % Solved by: fo/fo7.sh
% 2.72/2.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.72/2.93  % done 2817 iterations in 2.516s
% 2.72/2.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.72/2.93  % SZS output start Refutation
% 2.72/2.93  thf(sk_B_type, type, sk_B: $i).
% 2.72/2.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.72/2.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.72/2.93  thf(sk_A_type, type, sk_A: $i).
% 2.72/2.93  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.72/2.93  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.72/2.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.72/2.93  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.72/2.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.72/2.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.72/2.93  thf(t64_zfmisc_1, conjecture,
% 2.72/2.93    (![A:$i,B:$i,C:$i]:
% 2.72/2.93     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 2.72/2.93       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 2.72/2.93  thf(zf_stmt_0, negated_conjecture,
% 2.72/2.93    (~( ![A:$i,B:$i,C:$i]:
% 2.72/2.93        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 2.72/2.93          ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ) )),
% 2.72/2.93    inference('cnf.neg', [status(esa)], [t64_zfmisc_1])).
% 2.72/2.93  thf('0', plain,
% 2.72/2.93      ((((sk_A) = (sk_C_1))
% 2.72/2.93        | ~ (r2_hidden @ sk_A @ sk_B)
% 2.72/2.93        | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('1', plain,
% 2.72/2.93      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 2.72/2.93       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) | 
% 2.72/2.93       (((sk_A) = (sk_C_1)))),
% 2.72/2.93      inference('split', [status(esa)], ['0'])).
% 2.72/2.93  thf('2', plain,
% 2.72/2.93      ((((sk_A) != (sk_C_1))
% 2.72/2.93        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('3', plain,
% 2.72/2.93      (~ (((sk_A) = (sk_C_1))) | 
% 2.72/2.93       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 2.72/2.93      inference('split', [status(esa)], ['2'])).
% 2.72/2.93  thf('4', plain, ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (sk_C_1))))),
% 2.72/2.93      inference('split', [status(esa)], ['0'])).
% 2.72/2.93  thf('5', plain,
% 2.72/2.93      (((r2_hidden @ sk_A @ sk_B)
% 2.72/2.93        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('6', plain,
% 2.72/2.93      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 2.72/2.93      inference('split', [status(esa)], ['5'])).
% 2.72/2.93  thf('7', plain,
% 2.72/2.93      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 2.72/2.93             (((sk_A) = (sk_C_1))))),
% 2.72/2.93      inference('sup+', [status(thm)], ['4', '6'])).
% 2.72/2.93  thf(t95_xboole_1, axiom,
% 2.72/2.93    (![A:$i,B:$i]:
% 2.72/2.93     ( ( k3_xboole_0 @ A @ B ) =
% 2.72/2.93       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 2.72/2.93  thf('8', plain,
% 2.72/2.93      (![X19 : $i, X20 : $i]:
% 2.72/2.93         ((k3_xboole_0 @ X19 @ X20)
% 2.72/2.93           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 2.72/2.93              (k2_xboole_0 @ X19 @ X20)))),
% 2.72/2.93      inference('cnf', [status(esa)], [t95_xboole_1])).
% 2.72/2.93  thf(t91_xboole_1, axiom,
% 2.72/2.93    (![A:$i,B:$i,C:$i]:
% 2.72/2.93     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 2.72/2.93       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 2.72/2.93  thf('9', plain,
% 2.72/2.93      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.72/2.93         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 2.72/2.93           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 2.72/2.93      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.72/2.93  thf('10', plain,
% 2.72/2.93      (![X19 : $i, X20 : $i]:
% 2.72/2.93         ((k3_xboole_0 @ X19 @ X20)
% 2.72/2.93           = (k5_xboole_0 @ X19 @ 
% 2.72/2.93              (k5_xboole_0 @ X20 @ (k2_xboole_0 @ X19 @ X20))))),
% 2.72/2.93      inference('demod', [status(thm)], ['8', '9'])).
% 2.72/2.93  thf(t92_xboole_1, axiom,
% 2.72/2.93    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 2.72/2.93  thf('11', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 2.72/2.93      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.72/2.93  thf('12', plain,
% 2.72/2.93      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.72/2.93         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 2.72/2.93           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 2.72/2.93      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.72/2.93  thf('13', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 2.72/2.93           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.72/2.93      inference('sup+', [status(thm)], ['11', '12'])).
% 2.72/2.93  thf(commutativity_k5_xboole_0, axiom,
% 2.72/2.93    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 2.72/2.93  thf('14', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.72/2.93      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.72/2.93  thf(t5_boole, axiom,
% 2.72/2.93    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.72/2.93  thf('15', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 2.72/2.93      inference('cnf', [status(esa)], [t5_boole])).
% 2.72/2.93  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.72/2.93      inference('sup+', [status(thm)], ['14', '15'])).
% 2.72/2.93  thf('17', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.72/2.93      inference('demod', [status(thm)], ['13', '16'])).
% 2.72/2.93  thf('18', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 2.72/2.93           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.72/2.93      inference('sup+', [status(thm)], ['10', '17'])).
% 2.72/2.93  thf(t100_xboole_1, axiom,
% 2.72/2.93    (![A:$i,B:$i]:
% 2.72/2.93     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.72/2.93  thf('19', plain,
% 2.72/2.93      (![X12 : $i, X13 : $i]:
% 2.72/2.93         ((k4_xboole_0 @ X12 @ X13)
% 2.72/2.93           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 2.72/2.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.72/2.93  thf('20', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 2.72/2.93           = (k4_xboole_0 @ X1 @ X0))),
% 2.72/2.93      inference('demod', [status(thm)], ['18', '19'])).
% 2.72/2.93  thf(t1_xboole_0, axiom,
% 2.72/2.93    (![A:$i,B:$i,C:$i]:
% 2.72/2.93     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 2.72/2.93       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 2.72/2.93  thf('21', plain,
% 2.72/2.93      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.72/2.93         (~ (r2_hidden @ X8 @ X9)
% 2.72/2.93          | ~ (r2_hidden @ X8 @ X10)
% 2.72/2.93          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 2.72/2.93      inference('cnf', [status(esa)], [t1_xboole_0])).
% 2.72/2.93  thf('22', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.93         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 2.72/2.93          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 2.72/2.93          | ~ (r2_hidden @ X2 @ X0))),
% 2.72/2.93      inference('sup-', [status(thm)], ['20', '21'])).
% 2.72/2.93  thf(d3_xboole_0, axiom,
% 2.72/2.93    (![A:$i,B:$i,C:$i]:
% 2.72/2.93     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 2.72/2.93       ( ![D:$i]:
% 2.72/2.93         ( ( r2_hidden @ D @ C ) <=>
% 2.72/2.93           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.72/2.93  thf('23', plain,
% 2.72/2.93      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.72/2.93         (~ (r2_hidden @ X2 @ X3)
% 2.72/2.93          | (r2_hidden @ X2 @ X4)
% 2.72/2.93          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 2.72/2.93      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.72/2.93  thf('24', plain,
% 2.72/2.93      (![X2 : $i, X3 : $i, X5 : $i]:
% 2.72/2.93         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 2.72/2.93      inference('simplify', [status(thm)], ['23'])).
% 2.72/2.93  thf('25', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.93         (~ (r2_hidden @ X2 @ X0)
% 2.72/2.93          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.72/2.93      inference('clc', [status(thm)], ['22', '24'])).
% 2.72/2.93  thf('26', plain,
% 2.72/2.93      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 2.72/2.93             (((sk_A) = (sk_C_1))))),
% 2.72/2.93      inference('sup-', [status(thm)], ['7', '25'])).
% 2.72/2.93  thf(d1_tarski, axiom,
% 2.72/2.93    (![A:$i,B:$i]:
% 2.72/2.93     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 2.72/2.93       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 2.72/2.93  thf('27', plain,
% 2.72/2.93      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.72/2.93         (((X34) != (X33))
% 2.72/2.93          | (r2_hidden @ X34 @ X35)
% 2.72/2.93          | ((X35) != (k1_tarski @ X33)))),
% 2.72/2.93      inference('cnf', [status(esa)], [d1_tarski])).
% 2.72/2.93  thf('28', plain, (![X33 : $i]: (r2_hidden @ X33 @ (k1_tarski @ X33))),
% 2.72/2.93      inference('simplify', [status(thm)], ['27'])).
% 2.72/2.93  thf('29', plain,
% 2.72/2.93      (~ (((sk_A) = (sk_C_1))) | 
% 2.72/2.93       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 2.72/2.93      inference('demod', [status(thm)], ['26', '28'])).
% 2.72/2.93  thf('30', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 2.72/2.93           = (k4_xboole_0 @ X1 @ X0))),
% 2.72/2.93      inference('demod', [status(thm)], ['18', '19'])).
% 2.72/2.93  thf('31', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.72/2.93      inference('demod', [status(thm)], ['13', '16'])).
% 2.72/2.93  thf('32', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         ((k2_xboole_0 @ X1 @ X0)
% 2.72/2.93           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.72/2.93      inference('sup+', [status(thm)], ['30', '31'])).
% 2.72/2.93  thf('33', plain,
% 2.72/2.93      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 2.72/2.93      inference('split', [status(esa)], ['5'])).
% 2.72/2.93  thf('34', plain,
% 2.72/2.93      (![X8 : $i, X9 : $i, X11 : $i]:
% 2.72/2.93         ((r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X11))
% 2.72/2.93          | (r2_hidden @ X8 @ X9)
% 2.72/2.93          | ~ (r2_hidden @ X8 @ X11))),
% 2.72/2.93      inference('cnf', [status(esa)], [t1_xboole_0])).
% 2.72/2.93  thf('35', plain,
% 2.72/2.93      ((![X0 : $i]:
% 2.72/2.93          ((r2_hidden @ sk_A @ X0)
% 2.72/2.93           | (r2_hidden @ sk_A @ 
% 2.72/2.93              (k5_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 2.72/2.93      inference('sup-', [status(thm)], ['33', '34'])).
% 2.72/2.93  thf('36', plain,
% 2.72/2.93      ((((r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))
% 2.72/2.93         | (r2_hidden @ sk_A @ (k1_tarski @ sk_C_1))))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 2.72/2.93      inference('sup+', [status(thm)], ['32', '35'])).
% 2.72/2.93  thf('37', plain,
% 2.72/2.93      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 2.72/2.93      inference('split', [status(esa)], ['5'])).
% 2.72/2.93  thf('38', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.93         (~ (r2_hidden @ X2 @ X0)
% 2.72/2.93          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.72/2.93      inference('clc', [status(thm)], ['22', '24'])).
% 2.72/2.93  thf('39', plain,
% 2.72/2.93      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 2.72/2.93      inference('sup-', [status(thm)], ['37', '38'])).
% 2.72/2.93  thf('40', plain,
% 2.72/2.93      (((r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 2.72/2.93      inference('clc', [status(thm)], ['36', '39'])).
% 2.72/2.93  thf('41', plain,
% 2.72/2.93      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.72/2.93         (~ (r2_hidden @ X6 @ X4)
% 2.72/2.93          | (r2_hidden @ X6 @ X5)
% 2.72/2.93          | (r2_hidden @ X6 @ X3)
% 2.72/2.93          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 2.72/2.93      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.72/2.93  thf('42', plain,
% 2.72/2.93      (![X3 : $i, X5 : $i, X6 : $i]:
% 2.72/2.93         ((r2_hidden @ X6 @ X3)
% 2.72/2.93          | (r2_hidden @ X6 @ X5)
% 2.72/2.93          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['41'])).
% 2.72/2.93  thf('43', plain,
% 2.72/2.93      ((((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_tarski @ sk_C_1))))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 2.72/2.93      inference('sup-', [status(thm)], ['40', '42'])).
% 2.72/2.93  thf('44', plain,
% 2.72/2.93      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 2.72/2.93      inference('sup-', [status(thm)], ['37', '38'])).
% 2.72/2.93  thf('45', plain,
% 2.72/2.93      (((r2_hidden @ sk_A @ sk_B))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 2.72/2.93      inference('clc', [status(thm)], ['43', '44'])).
% 2.72/2.93  thf('46', plain,
% 2.72/2.93      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 2.72/2.93      inference('split', [status(esa)], ['0'])).
% 2.72/2.93  thf('47', plain,
% 2.72/2.93      (((r2_hidden @ sk_A @ sk_B)) | 
% 2.72/2.93       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 2.72/2.93      inference('sup-', [status(thm)], ['45', '46'])).
% 2.72/2.93  thf('48', plain,
% 2.72/2.93      (((r2_hidden @ sk_A @ sk_B)) | 
% 2.72/2.93       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 2.72/2.93      inference('split', [status(esa)], ['5'])).
% 2.72/2.93  thf('49', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.72/2.93      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.72/2.93  thf('50', plain,
% 2.72/2.93      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 2.72/2.93      inference('split', [status(esa)], ['5'])).
% 2.72/2.93  thf('51', plain,
% 2.72/2.93      (![X8 : $i, X9 : $i, X11 : $i]:
% 2.72/2.93         ((r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X11))
% 2.72/2.93          | (r2_hidden @ X8 @ X9)
% 2.72/2.93          | ~ (r2_hidden @ X8 @ X11))),
% 2.72/2.93      inference('cnf', [status(esa)], [t1_xboole_0])).
% 2.72/2.93  thf('52', plain,
% 2.72/2.93      ((![X0 : $i]:
% 2.72/2.93          ((r2_hidden @ sk_A @ X0)
% 2.72/2.93           | (r2_hidden @ sk_A @ (k5_xboole_0 @ X0 @ sk_B))))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ sk_B)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['50', '51'])).
% 2.72/2.93  thf('53', plain,
% 2.72/2.93      ((![X0 : $i]:
% 2.72/2.93          ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))
% 2.72/2.93           | (r2_hidden @ sk_A @ X0)))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ sk_B)))),
% 2.72/2.93      inference('sup+', [status(thm)], ['49', '52'])).
% 2.72/2.93  thf('54', plain,
% 2.72/2.93      (![X12 : $i, X13 : $i]:
% 2.72/2.93         ((k4_xboole_0 @ X12 @ X13)
% 2.72/2.93           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 2.72/2.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.72/2.93  thf('55', plain,
% 2.72/2.93      ((![X0 : $i]:
% 2.72/2.93          ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))
% 2.72/2.93           | (r2_hidden @ sk_A @ X0)))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ sk_B)))),
% 2.72/2.93      inference('sup+', [status(thm)], ['49', '52'])).
% 2.72/2.93  thf('56', plain,
% 2.72/2.93      ((![X0 : $i]:
% 2.72/2.93          ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 2.72/2.93           | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ sk_B)))),
% 2.72/2.93      inference('sup+', [status(thm)], ['54', '55'])).
% 2.72/2.93  thf('57', plain,
% 2.72/2.93      ((~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 2.72/2.93         <= (~
% 2.72/2.93             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 2.72/2.93      inference('split', [status(esa)], ['0'])).
% 2.72/2.93  thf('58', plain,
% 2.72/2.93      (((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 2.72/2.93         <= (~
% 2.72/2.93             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 2.72/2.93             ((r2_hidden @ sk_A @ sk_B)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['56', '57'])).
% 2.72/2.93  thf('59', plain,
% 2.72/2.93      (![X19 : $i, X20 : $i]:
% 2.72/2.93         ((k3_xboole_0 @ X19 @ X20)
% 2.72/2.93           = (k5_xboole_0 @ X19 @ 
% 2.72/2.93              (k5_xboole_0 @ X20 @ (k2_xboole_0 @ X19 @ X20))))),
% 2.72/2.93      inference('demod', [status(thm)], ['8', '9'])).
% 2.72/2.93  thf('60', plain,
% 2.72/2.93      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.72/2.93         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 2.72/2.93           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 2.72/2.93      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.72/2.93  thf('61', plain,
% 2.72/2.93      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.72/2.93         (~ (r2_hidden @ X8 @ X9)
% 2.72/2.93          | ~ (r2_hidden @ X8 @ X10)
% 2.72/2.93          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 2.72/2.93      inference('cnf', [status(esa)], [t1_xboole_0])).
% 2.72/2.93  thf('62', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.93         (~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))
% 2.72/2.93          | ~ (r2_hidden @ X3 @ X0)
% 2.72/2.93          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ X1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['60', '61'])).
% 2.72/2.93  thf('63', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.93         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.72/2.93          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 2.72/2.93          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['59', '62'])).
% 2.72/2.93  thf('64', plain,
% 2.72/2.93      (((~ (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))
% 2.72/2.93         | ~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))
% 2.72/2.93         <= (~
% 2.72/2.93             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 2.72/2.93             ((r2_hidden @ sk_A @ sk_B)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['58', '63'])).
% 2.72/2.93  thf('65', plain,
% 2.72/2.93      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 2.72/2.93      inference('split', [status(esa)], ['5'])).
% 2.72/2.93  thf('66', plain,
% 2.72/2.93      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.72/2.93         (~ (r2_hidden @ X2 @ X5)
% 2.72/2.93          | (r2_hidden @ X2 @ X4)
% 2.72/2.93          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 2.72/2.93      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.72/2.93  thf('67', plain,
% 2.72/2.93      (![X2 : $i, X3 : $i, X5 : $i]:
% 2.72/2.93         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 2.72/2.93      inference('simplify', [status(thm)], ['66'])).
% 2.72/2.93  thf('68', plain,
% 2.72/2.93      ((![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))
% 2.72/2.93         <= (((r2_hidden @ sk_A @ sk_B)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['65', '67'])).
% 2.72/2.93  thf('69', plain,
% 2.72/2.93      ((~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 2.72/2.93         <= (~
% 2.72/2.93             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 2.72/2.93             ((r2_hidden @ sk_A @ sk_B)))),
% 2.72/2.93      inference('demod', [status(thm)], ['64', '68'])).
% 2.72/2.93  thf('70', plain,
% 2.72/2.93      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 2.72/2.93         <= (~
% 2.72/2.93             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 2.72/2.93             ((r2_hidden @ sk_A @ sk_B)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['53', '69'])).
% 2.72/2.93  thf('71', plain,
% 2.72/2.93      (![X33 : $i, X35 : $i, X36 : $i]:
% 2.72/2.93         (~ (r2_hidden @ X36 @ X35)
% 2.72/2.93          | ((X36) = (X33))
% 2.72/2.93          | ((X35) != (k1_tarski @ X33)))),
% 2.72/2.93      inference('cnf', [status(esa)], [d1_tarski])).
% 2.72/2.93  thf('72', plain,
% 2.72/2.93      (![X33 : $i, X36 : $i]:
% 2.72/2.93         (((X36) = (X33)) | ~ (r2_hidden @ X36 @ (k1_tarski @ X33)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['71'])).
% 2.72/2.93  thf('73', plain,
% 2.72/2.93      ((((sk_A) = (sk_C_1)))
% 2.72/2.93         <= (~
% 2.72/2.93             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 2.72/2.93             ((r2_hidden @ sk_A @ sk_B)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['70', '72'])).
% 2.72/2.93  thf('74', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 2.72/2.93      inference('split', [status(esa)], ['2'])).
% 2.72/2.93  thf('75', plain,
% 2.72/2.93      ((((sk_A) != (sk_A)))
% 2.72/2.93         <= (~ (((sk_A) = (sk_C_1))) & 
% 2.72/2.93             ~
% 2.72/2.93             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 2.72/2.93             ((r2_hidden @ sk_A @ sk_B)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['73', '74'])).
% 2.72/2.93  thf('76', plain,
% 2.72/2.93      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 2.72/2.93       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) | 
% 2.72/2.93       (((sk_A) = (sk_C_1)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['75'])).
% 2.72/2.93  thf('77', plain, ($false),
% 2.72/2.93      inference('sat_resolution*', [status(thm)],
% 2.72/2.93                ['1', '3', '29', '47', '48', '76'])).
% 2.72/2.93  
% 2.72/2.93  % SZS output end Refutation
% 2.72/2.93  
% 2.72/2.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
