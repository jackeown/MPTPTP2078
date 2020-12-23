%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JF0F0gVfvx

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:40 EST 2020

% Result     : Theorem 4.16s
% Output     : Refutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :  138 (1034 expanded)
%              Number of leaves         :   14 ( 259 expanded)
%              Depth                    :   23
%              Number of atoms          : 1420 (12607 expanded)
%              Number of equality atoms :   57 ( 544 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t1_xboole_0,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ ( A @ ( k5_xboole_0 @ ( B @ C ) ) ) )
    <=> ~ ( ( r2_hidden @ ( A @ B ) )
        <=> ( r2_hidden @ ( A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ ( A @ ( k5_xboole_0 @ ( B @ C ) ) ) )
      <=> ~ ( ( r2_hidden @ ( A @ B ) )
          <=> ( r2_hidden @ ( A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_xboole_0])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ ( sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ ( sk_A @ sk_C ) )
   <= ( r2_hidden @ ( sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ ( sk_A @ sk_B ) )
   <= ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('5',plain,
    ( ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) )
   <= ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( X18 @ X19 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X18 @ X19 ) @ ( k4_xboole_0 @ ( X19 @ X18 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            | ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( X10 @ X8 ) )
      | ( r2_hidden @ ( X10 @ X9 ) )
      | ( r2_hidden @ ( X10 @ X7 ) )
      | ( X8
       != ( k2_xboole_0 @ ( X9 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ ( X10 @ X7 ) )
      | ( r2_hidden @ ( X10 @ X9 ) )
      | ~ ( r2_hidden @ ( X10 @ ( k2_xboole_0 @ ( X9 @ X7 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( X2 @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( X2 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( X2 @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( ( r2_hidden @ ( sk_A @ ( k4_xboole_0 @ ( sk_C @ sk_B ) ) ) )
      | ( r2_hidden @ ( sk_A @ ( k4_xboole_0 @ ( sk_B @ sk_C ) ) ) ) )
   <= ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            & ~ ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( X16 @ X15 ) )
      | ~ ( r2_hidden @ ( X16 @ X14 ) )
      | ( X15
       != ( k4_xboole_0 @ ( X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( X16 @ X14 ) )
      | ~ ( r2_hidden @ ( X16 @ ( k4_xboole_0 @ ( X13 @ X14 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( r2_hidden @ ( sk_A @ ( k4_xboole_0 @ ( sk_B @ sk_C ) ) ) )
      | ~ ( r2_hidden @ ( sk_A @ sk_B ) ) )
   <= ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( sk_A @ ( k4_xboole_0 @ ( sk_B @ sk_C ) ) ) )
   <= ( ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) )
      & ( r2_hidden @ ( sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( X16 @ X14 ) )
      | ~ ( r2_hidden @ ( X16 @ ( k4_xboole_0 @ ( X13 @ X14 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('16',plain,
    ( ~ ( r2_hidden @ ( sk_A @ sk_C ) )
   <= ( ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) )
      & ( r2_hidden @ ( sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ ( sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_A @ sk_C ) )
    | ~ ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( r2_hidden @ ( sk_A @ sk_B ) )
   <= ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( X12 @ X13 ) )
      | ( r2_hidden @ ( X12 @ X14 ) )
      | ( r2_hidden @ ( X12 @ X15 ) )
      | ( X15
       != ( k4_xboole_0 @ ( X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( X12 @ ( k4_xboole_0 @ ( X13 @ X14 ) ) ) )
      | ( r2_hidden @ ( X12 @ X14 ) )
      | ~ ( r2_hidden @ ( X12 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_A @ X0 ) )
        | ( r2_hidden @ ( sk_A @ ( k4_xboole_0 @ ( sk_B @ X0 ) ) ) ) )
   <= ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_A @ sk_B ) )
   <= ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('24',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( X6 @ X7 ) )
      | ( r2_hidden @ ( X6 @ X8 ) )
      | ( X8
       != ( k2_xboole_0 @ ( X9 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('25',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ ( X6 @ ( k2_xboole_0 @ ( X9 @ X7 ) ) ) )
      | ~ ( r2_hidden @ ( X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( sk_A @ ( k2_xboole_0 @ ( X0 @ sk_B ) ) ) )
   <= ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( X12 @ ( k4_xboole_0 @ ( X13 @ X14 ) ) ) )
      | ( r2_hidden @ ( X12 @ X14 ) )
      | ~ ( r2_hidden @ ( X12 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('28',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( sk_A @ X1 ) )
        | ( r2_hidden @ ( sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( X0 @ sk_B ) @ X1 ) ) ) ) )
   <= ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( X18 @ X19 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X18 @ X19 ) @ ( k4_xboole_0 @ ( X19 @ X18 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('30',plain,(
    ! [X7: $i,X9: $i,X11: $i] :
      ( ( X11
        = ( k2_xboole_0 @ ( X9 @ X7 ) ) )
      | ( r2_hidden @ ( sk_D @ ( X11 @ ( X7 @ X9 ) ) @ X7 ) )
      | ( r2_hidden @ ( sk_D @ ( X11 @ ( X7 @ X9 ) ) @ X9 ) )
      | ( r2_hidden @ ( sk_D @ ( X11 @ ( X7 @ X9 ) ) @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( X0 @ ( X0 @ X1 ) ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( X0 @ ( X0 @ X1 ) ) @ X1 ) )
      | ( X0
        = ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('32',plain,(
    ! [X7: $i,X9: $i,X11: $i] :
      ( ( X11
        = ( k2_xboole_0 @ ( X9 @ X7 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( X11 @ ( X7 @ X9 ) ) @ X7 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( X11 @ ( X7 @ X9 ) ) @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ ( X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( X0 @ ( X0 @ X1 ) ) @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( X0 @ ( X0 @ X1 ) ) @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( X0 @ ( X0 @ X1 ) ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( X0 @ ( X0 @ X1 ) ) @ X1 ) )
      | ( X0
        = ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( X0 @ ( X0 @ X1 ) ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( X0 @ ( X0 @ X1 ) ) @ X1 ) )
      | ( X0
        = ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ ( X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( X0 @ ( X0 @ X1 ) ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ ( X6 @ ( k2_xboole_0 @ ( X9 @ X7 ) ) ) )
      | ~ ( r2_hidden @ ( X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( X0 @ X1 ) ) )
      | ( r2_hidden @ ( sk_D @ ( X1 @ ( X1 @ X0 ) ) @ ( k2_xboole_0 @ ( X2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( X2 @ ( X2 @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ) @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ( X2
        = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X0 @ X1 ) @ X2 ) ) ) ) ),
    inference('sup+',[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ ( X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( X0 @ ( X0 @ X1 ) ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('41',plain,(
    ! [X7: $i,X9: $i,X11: $i] :
      ( ( X11
        = ( k2_xboole_0 @ ( X9 @ X7 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( X11 @ ( X7 @ X9 ) ) @ X9 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( X11 @ ( X7 @ X9 ) ) @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( X0 @ X1 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( X1 @ ( X1 @ X0 ) ) @ X1 ) )
      | ( X1
        = ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( X1 @ ( X1 @ X0 ) ) @ X1 ) )
      | ( X1
        = ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ ( X1 @ X0 ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X0 @ X1 ) @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) ) )
      | ( ( k5_xboole_0 @ ( X1 @ X0 ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X0 @ X1 ) @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( X3 @ X2 ) )
      = ( k2_xboole_0 @ ( X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( X3 @ X2 ) )
      = ( k2_xboole_0 @ ( X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ ( X1 @ X0 ) )
        = ( k2_xboole_0 @ ( k5_xboole_0 @ ( X1 @ X0 ) @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ) )
      | ( ( k5_xboole_0 @ ( X1 @ X0 ) )
        = ( k2_xboole_0 @ ( k5_xboole_0 @ ( X1 @ X0 ) @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ ( X1 @ X0 ) @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ( X17
        = ( k4_xboole_0 @ ( X13 @ X14 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( X17 @ ( X14 @ X13 ) ) @ X13 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( X17 @ ( X14 @ X13 ) ) @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( X0 @ ( X1 @ X0 ) ) @ X0 ) )
      | ( X0
        = ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['49'])).

thf('51',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ ( X6 @ ( k2_xboole_0 @ ( X9 @ X7 ) ) ) )
      | ~ ( r2_hidden @ ( X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k4_xboole_0 @ ( X0 @ X1 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( X0 @ ( X1 @ X0 ) ) @ ( k2_xboole_0 @ ( X2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( X0 @ ( X1 @ X0 ) ) @ X0 ) )
      | ( X0
        = ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['49'])).

thf('54',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ( X17
        = ( k4_xboole_0 @ ( X13 @ X14 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( X17 @ ( X14 @ X13 ) ) @ X14 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( X17 @ ( X14 @ X13 ) ) @ X13 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( X17 @ ( X14 @ X13 ) ) @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ ( X0 @ X1 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( X0 @ ( X1 @ X0 ) ) @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( X0 @ ( X1 @ X0 ) ) @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( X0 @ ( X1 @ X0 ) ) @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( X0 @ ( X1 @ X0 ) ) @ X0 ) )
      | ( X0
        = ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( X0 @ ( X1 @ X0 ) ) @ X0 ) )
      | ( X0
        = ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['49'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ ( X0 @ X1 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( X0 @ ( X1 @ X0 ) ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( X16 @ X14 ) )
      | ~ ( r2_hidden @ ( X16 @ ( k4_xboole_0 @ ( X13 @ X14 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ ( X2 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( X2 @ ( k4_xboole_0 @ ( X1 @ X0 ) @ X2 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k4_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X2 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ) )
      | ( X0
        = ( k4_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X2 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X0
      = ( k4_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X2 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( X16 @ X14 ) )
      | ~ ( r2_hidden @ ( X16 @ ( k4_xboole_0 @ ( X13 @ X14 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( X3 @ X0 ) )
      | ~ ( r2_hidden @ ( X3 @ ( k4_xboole_0 @ ( X2 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( X3 @ ( k4_xboole_0 @ ( X2 @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) ) ) )
      | ~ ( r2_hidden @ ( X3 @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['48','64'])).

thf('66',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) )
        | ~ ( r2_hidden @ ( sk_A @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ) )
   <= ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_A @ X0 ) )
        | ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( X0 @ sk_B ) ) ) ) )
   <= ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','66'])).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( X18 @ X19 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X18 @ X19 ) @ ( k4_xboole_0 @ ( X19 @ X18 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( X3 @ X2 ) )
      = ( k2_xboole_0 @ ( X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( X0 @ X1 ) ) )
      | ( r2_hidden @ ( sk_D @ ( X1 @ ( X1 @ X0 ) ) @ ( k2_xboole_0 @ ( X2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( X1 @ ( X1 @ X0 ) ) @ X1 ) )
      | ( X1
        = ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( X1 @ X0 ) )
        = ( k2_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) )
      | ( ( k2_xboole_0 @ ( X1 @ X0 ) )
        = ( k2_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X1 @ X0 ) )
      = ( k2_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ X1 ) )
      = ( k2_xboole_0 @ ( X1 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['69','73'])).

thf('75',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ ( X10 @ X7 ) )
      | ( r2_hidden @ ( X10 @ X9 ) )
      | ~ ( r2_hidden @ ( X10 @ ( k2_xboole_0 @ ( X9 @ X7 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( X2 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( X2 @ X0 ) )
      | ( r2_hidden @ ( X2 @ ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( X6 @ X9 ) )
      | ( r2_hidden @ ( X6 @ X8 ) )
      | ( X8
       != ( k2_xboole_0 @ ( X9 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('78',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ ( X6 @ ( k2_xboole_0 @ ( X9 @ X7 ) ) ) )
      | ~ ( r2_hidden @ ( X6 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( X2 @ ( k2_xboole_0 @ ( X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( X2 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( X2 @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( X0 @ X1 ) @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['68','79'])).

thf('81',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( X18 @ X19 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X18 @ X19 ) @ ( k4_xboole_0 @ ( X19 @ X18 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( X2 @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( X2 @ ( k5_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_A @ X0 ) )
        | ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ X0 ) ) ) ) )
   <= ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','82'])).

thf('84',plain,
    ( ~ ( r2_hidden @ ( sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ~ ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) )
   <= ~ ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,
    ( ~ ( r2_hidden @ ( sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_A @ sk_C ) )
    | ~ ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) )
    | ( r2_hidden @ ( sk_A @ sk_C ) )
    | ~ ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['86'])).

thf('88',plain,
    ( ~ ( r2_hidden @ ( sk_A @ sk_C ) )
    | ~ ( r2_hidden @ ( sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('89',plain,
    ( ~ ( r2_hidden @ ( sk_A @ sk_C ) )
    | ~ ( r2_hidden @ ( sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( ( r2_hidden @ ( sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_A @ sk_C ) )
    | ~ ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference(split,[status(esa)],['84'])).

thf('91',plain,
    ( ( ( r2_hidden @ ( sk_A @ ( k4_xboole_0 @ ( sk_C @ sk_B ) ) ) )
      | ( r2_hidden @ ( sk_A @ ( k4_xboole_0 @ ( sk_B @ sk_C ) ) ) ) )
   <= ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('92',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( X16 @ X15 ) )
      | ( r2_hidden @ ( X16 @ X13 ) )
      | ( X15
       != ( k4_xboole_0 @ ( X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('93',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ ( X16 @ X13 ) )
      | ~ ( r2_hidden @ ( X16 @ ( k4_xboole_0 @ ( X13 @ X14 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( ( r2_hidden @ ( sk_A @ ( k4_xboole_0 @ ( sk_B @ sk_C ) ) ) )
      | ( r2_hidden @ ( sk_A @ sk_C ) ) )
   <= ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ ( X16 @ X13 ) )
      | ~ ( r2_hidden @ ( X16 @ ( k4_xboole_0 @ ( X13 @ X14 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('96',plain,
    ( ( ( r2_hidden @ ( sk_A @ sk_C ) )
      | ( r2_hidden @ ( sk_A @ sk_B ) ) )
   <= ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( r2_hidden @ ( sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ ( sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,
    ( ( r2_hidden @ ( sk_A @ sk_B ) )
   <= ( ~ ( r2_hidden @ ( sk_A @ sk_C ) )
      & ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( r2_hidden @ ( sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('100',plain,
    ( ( r2_hidden @ ( sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_A @ sk_C ) )
    | ~ ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['87','88','89','90','100'])).

thf('102',plain,(
    ~ ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['85','101'])).

thf('103',plain,
    ( ( r2_hidden @ ( sk_A @ sk_C ) )
   <= ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','102'])).

thf('104',plain,
    ( ~ ( r2_hidden @ ( sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ ( sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('105',plain,
    ( ( r2_hidden @ ( sk_A @ sk_C ) )
    | ~ ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['17','18','105'])).

thf('107',plain,(
    ~ ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','106'])).

thf('108',plain,
    ( ( r2_hidden @ ( sk_A @ sk_C ) )
   <= ( r2_hidden @ ( sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('109',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( X12 @ ( k4_xboole_0 @ ( X13 @ X14 ) ) ) )
      | ( r2_hidden @ ( X12 @ X14 ) )
      | ~ ( r2_hidden @ ( X12 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_A @ X0 ) )
        | ( r2_hidden @ ( sk_A @ ( k4_xboole_0 @ ( sk_C @ X0 ) ) ) ) )
   <= ( r2_hidden @ ( sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) )
    | ~ ( r2_hidden @ ( sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['84'])).

thf('112',plain,
    ( ( r2_hidden @ ( sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('113',plain,
    ( ( r2_hidden @ ( sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('114',plain,(
    r2_hidden @ ( sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['87','111','112','17','18','105','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_A @ ( k4_xboole_0 @ ( sk_C @ X0 ) ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['110','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_A @ ( k4_xboole_0 @ ( sk_C @ X0 ) ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['110','114'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( X3 @ ( k4_xboole_0 @ ( X2 @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) ) ) )
      | ~ ( r2_hidden @ ( X3 @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['48','64'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_A @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( X0 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    ~ ( r2_hidden @ ( sk_A @ ( k5_xboole_0 @ ( sk_B @ sk_C ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['85','101'])).

thf('121',plain,(
    r2_hidden @ ( sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['107','121'])).

%------------------------------------------------------------------------------
