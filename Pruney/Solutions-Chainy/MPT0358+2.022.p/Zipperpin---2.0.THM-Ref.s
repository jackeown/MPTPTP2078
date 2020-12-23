%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gVkUq78EoV

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 696 expanded)
%              Number of leaves         :   28 ( 193 expanded)
%              Depth                    :   20
%              Number of atoms          :  965 (7310 expanded)
%              Number of equality atoms :   86 ( 654 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('0',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
        = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['3','7'])).

thf('9',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('10',plain,
    ( ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X32: $i] :
      ( ( k1_subset_1 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('12',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['12'])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['16'])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['16'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X22 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('35',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('39',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X32: $i] :
      ( ( k1_subset_1 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('44',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['12'])).

thf('47',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('49',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','50'])).

thf('52',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['15','51'])).

thf('53',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['14','52'])).

thf('54',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','53'])).

thf('55',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['15','51','55'])).

thf('57',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['54','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('59',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X33 @ X34 )
        = ( k4_xboole_0 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('60',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('62',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('64',plain,(
    ! [X35: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('65',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['63','64'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('66',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( r1_tarski @ X27 @ X25 )
      | ( X26
       != ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('67',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_tarski @ X27 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('70',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['60','74'])).

thf('76',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['57','75'])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('78',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('82',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['15','51','55'])).

thf('83',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
      | ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('90',plain,
    ( ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
      | ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
        = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['15','51','55'])).

thf('92',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
    | ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['83','92'])).

thf('94',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['14','52'])).

thf('95',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['80','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gVkUq78EoV
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.59  % Solved by: fo/fo7.sh
% 0.20/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.59  % done 437 iterations in 0.137s
% 0.20/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.59  % SZS output start Refutation
% 0.20/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.59  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.59  thf(t38_subset_1, conjecture,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.59       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.59         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.59    (~( ![A:$i,B:$i]:
% 0.20/0.59        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.59          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.59            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.20/0.59    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.20/0.59  thf('0', plain,
% 0.20/0.59      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.20/0.59        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('1', plain,
% 0.20/0.59      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.20/0.59         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.59      inference('split', [status(esa)], ['0'])).
% 0.20/0.59  thf(t28_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.59  thf('2', plain,
% 0.20/0.59      (![X20 : $i, X21 : $i]:
% 0.20/0.59         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.20/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.59  thf('3', plain,
% 0.20/0.59      ((((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 0.20/0.59         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.59  thf(t7_xboole_0, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.59          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.59  thf('4', plain,
% 0.20/0.59      (![X14 : $i]:
% 0.20/0.59         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.20/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.59  thf(d4_xboole_0, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.59       ( ![D:$i]:
% 0.20/0.59         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.59           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.59  thf('5', plain,
% 0.20/0.59      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.59          | (r2_hidden @ X6 @ X4)
% 0.20/0.59          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.59  thf('6', plain,
% 0.20/0.59      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.59         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.59  thf('7', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.59          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.59  thf('8', plain,
% 0.20/0.59      ((((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.20/0.59         | ((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.20/0.59             = (k1_xboole_0))))
% 0.20/0.59         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.59      inference('sup+', [status(thm)], ['3', '7'])).
% 0.20/0.59  thf('9', plain,
% 0.20/0.59      ((((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 0.20/0.59         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.59  thf('10', plain,
% 0.20/0.59      ((((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.20/0.59         | ((sk_B_1) = (k1_xboole_0))))
% 0.20/0.59         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.59  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.59  thf('11', plain, (![X32 : $i]: ((k1_subset_1 @ X32) = (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.59  thf('12', plain,
% 0.20/0.59      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.20/0.59        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('13', plain,
% 0.20/0.59      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.20/0.59         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.59      inference('split', [status(esa)], ['12'])).
% 0.20/0.59  thf('14', plain,
% 0.20/0.59      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.59  thf('15', plain,
% 0.20/0.59      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.20/0.59       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.59      inference('split', [status(esa)], ['12'])).
% 0.20/0.59  thf('16', plain,
% 0.20/0.59      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.20/0.59         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.20/0.59          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.20/0.59          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.20/0.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.59  thf('17', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.59          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.59      inference('eq_fact', [status(thm)], ['16'])).
% 0.20/0.59  thf('18', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.59          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.59      inference('eq_fact', [status(thm)], ['16'])).
% 0.20/0.59  thf('19', plain,
% 0.20/0.59      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.20/0.59         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.20/0.59          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.20/0.59          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.20/0.59          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.20/0.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.59  thf('20', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.20/0.59          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.59          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.20/0.59          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.59  thf('21', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.20/0.59          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.59          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.59  thf('22', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.59          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.59      inference('eq_fact', [status(thm)], ['16'])).
% 0.20/0.59  thf('23', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.20/0.59          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.20/0.59      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.59  thf('24', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (((X0) = (k3_xboole_0 @ X0 @ X0)) | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['17', '23'])).
% 0.20/0.59  thf('25', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.59  thf('26', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.59  thf(t100_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.59  thf('27', plain,
% 0.20/0.59      (![X18 : $i, X19 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ X18 @ X19)
% 0.20/0.59           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.59  thf('28', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.59      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.59  thf('29', plain,
% 0.20/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['25', '28'])).
% 0.20/0.59  thf(t36_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.59  thf('30', plain,
% 0.20/0.59      (![X22 : $i, X23 : $i]: (r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X22)),
% 0.20/0.59      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.59  thf('31', plain, (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 0.20/0.59      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.59  thf('32', plain,
% 0.20/0.59      (![X14 : $i]:
% 0.20/0.59         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.20/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.59  thf('33', plain,
% 0.20/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['25', '28'])).
% 0.20/0.59  thf(d5_xboole_0, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.59       ( ![D:$i]:
% 0.20/0.59         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.59           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.59  thf('34', plain,
% 0.20/0.59      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X12 @ X11)
% 0.20/0.59          | (r2_hidden @ X12 @ X9)
% 0.20/0.59          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.20/0.59      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.59  thf('35', plain,
% 0.20/0.59      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.20/0.59         ((r2_hidden @ X12 @ X9)
% 0.20/0.59          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.59  thf('36', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.59  thf('37', plain,
% 0.20/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['25', '28'])).
% 0.20/0.59  thf('38', plain,
% 0.20/0.59      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X12 @ X11)
% 0.20/0.59          | ~ (r2_hidden @ X12 @ X10)
% 0.20/0.59          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.20/0.59      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.59  thf('39', plain,
% 0.20/0.59      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X12 @ X10)
% 0.20/0.59          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.59  thf('40', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.20/0.59          | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['37', '39'])).
% 0.20/0.59  thf('41', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.59      inference('clc', [status(thm)], ['36', '40'])).
% 0.20/0.59  thf('42', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['32', '41'])).
% 0.20/0.59  thf('43', plain, (![X32 : $i]: ((k1_subset_1 @ X32) = (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.59  thf('44', plain,
% 0.20/0.59      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.20/0.59         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.59      inference('split', [status(esa)], ['0'])).
% 0.20/0.59  thf('45', plain,
% 0.20/0.59      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.59      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.59  thf('46', plain,
% 0.20/0.59      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.20/0.59         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.59      inference('split', [status(esa)], ['12'])).
% 0.20/0.59  thf('47', plain,
% 0.20/0.59      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.59         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.20/0.59             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.59  thf('48', plain,
% 0.20/0.59      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.59      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.59  thf('49', plain,
% 0.20/0.59      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.59         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.20/0.59             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.59      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.59  thf('50', plain,
% 0.20/0.59      ((![X0 : $i]:
% 0.20/0.59          ~ (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ 
% 0.20/0.59             (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.59         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.20/0.59             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['42', '49'])).
% 0.20/0.59  thf('51', plain,
% 0.20/0.59      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.20/0.59       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['31', '50'])).
% 0.20/0.59  thf('52', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.20/0.59      inference('sat_resolution*', [status(thm)], ['15', '51'])).
% 0.20/0.59  thf('53', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.59      inference('simpl_trail', [status(thm)], ['14', '52'])).
% 0.20/0.59  thf('54', plain,
% 0.20/0.59      (((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.20/0.59         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.59      inference('simplify_reflect-', [status(thm)], ['10', '53'])).
% 0.20/0.59  thf('55', plain,
% 0.20/0.59      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.20/0.59       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.20/0.59      inference('split', [status(esa)], ['0'])).
% 0.20/0.59  thf('56', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.59      inference('sat_resolution*', [status(thm)], ['15', '51', '55'])).
% 0.20/0.59  thf('57', plain,
% 0.20/0.59      ((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.20/0.59      inference('simpl_trail', [status(thm)], ['54', '56'])).
% 0.20/0.59  thf('58', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(d5_subset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.59       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.59  thf('59', plain,
% 0.20/0.59      (![X33 : $i, X34 : $i]:
% 0.20/0.59         (((k3_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))
% 0.20/0.59          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 0.20/0.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.59  thf('60', plain,
% 0.20/0.59      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.59  thf('61', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(d2_subset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.59       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.59  thf('62', plain,
% 0.20/0.59      (![X29 : $i, X30 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X29 @ X30)
% 0.20/0.59          | (r2_hidden @ X29 @ X30)
% 0.20/0.59          | (v1_xboole_0 @ X30))),
% 0.20/0.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.59  thf('63', plain,
% 0.20/0.59      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.59        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.59  thf(fc1_subset_1, axiom,
% 0.20/0.59    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.59  thf('64', plain, (![X35 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 0.20/0.59      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.59  thf('65', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.59      inference('clc', [status(thm)], ['63', '64'])).
% 0.20/0.59  thf(d1_zfmisc_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.59  thf('66', plain,
% 0.20/0.59      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X27 @ X26)
% 0.20/0.59          | (r1_tarski @ X27 @ X25)
% 0.20/0.59          | ((X26) != (k1_zfmisc_1 @ X25)))),
% 0.20/0.59      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.59  thf('67', plain,
% 0.20/0.59      (![X25 : $i, X27 : $i]:
% 0.20/0.59         ((r1_tarski @ X27 @ X25) | ~ (r2_hidden @ X27 @ (k1_zfmisc_1 @ X25)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['66'])).
% 0.20/0.59  thf('68', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.20/0.59      inference('sup-', [status(thm)], ['65', '67'])).
% 0.20/0.59  thf('69', plain,
% 0.20/0.59      (![X20 : $i, X21 : $i]:
% 0.20/0.59         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.20/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.59  thf('70', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.59  thf('71', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.59  thf('72', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['70', '71'])).
% 0.20/0.59  thf('73', plain,
% 0.20/0.59      (![X18 : $i, X19 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ X18 @ X19)
% 0.20/0.59           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.59  thf('74', plain,
% 0.20/0.59      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['72', '73'])).
% 0.20/0.59  thf('75', plain,
% 0.20/0.59      (((k3_subset_1 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['60', '74'])).
% 0.20/0.59  thf('76', plain,
% 0.20/0.59      ((r2_hidden @ (sk_B @ sk_B_1) @ (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['57', '75'])).
% 0.20/0.59  thf('77', plain,
% 0.20/0.59      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['72', '73'])).
% 0.20/0.59  thf('78', plain,
% 0.20/0.59      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X12 @ X10)
% 0.20/0.59          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.59  thf('79', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_A @ sk_B_1))
% 0.20/0.59          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.59  thf('80', plain, (~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.20/0.59      inference('sup-', [status(thm)], ['76', '79'])).
% 0.20/0.59  thf('81', plain,
% 0.20/0.59      ((((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 0.20/0.59         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.59  thf('82', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.59      inference('sat_resolution*', [status(thm)], ['15', '51', '55'])).
% 0.20/0.59  thf('83', plain,
% 0.20/0.59      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.20/0.59      inference('simpl_trail', [status(thm)], ['81', '82'])).
% 0.20/0.59  thf('84', plain,
% 0.20/0.59      ((((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 0.20/0.59         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.59  thf('85', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.59  thf('86', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.59          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.59  thf('87', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1)
% 0.20/0.59          | ((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup+', [status(thm)], ['85', '86'])).
% 0.20/0.59  thf('88', plain,
% 0.20/0.59      ((((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)
% 0.20/0.59         | ((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.20/0.59             = (k1_xboole_0))))
% 0.20/0.59         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.59      inference('sup+', [status(thm)], ['84', '87'])).
% 0.20/0.59  thf('89', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.59  thf('90', plain,
% 0.20/0.59      ((((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)
% 0.20/0.59         | ((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.20/0.59             = (k1_xboole_0))))
% 0.20/0.59         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.59      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.59  thf('91', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.59      inference('sat_resolution*', [status(thm)], ['15', '51', '55'])).
% 0.20/0.59  thf('92', plain,
% 0.20/0.59      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)
% 0.20/0.59        | ((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.20/0.59            = (k1_xboole_0)))),
% 0.20/0.59      inference('simpl_trail', [status(thm)], ['90', '91'])).
% 0.20/0.59  thf('93', plain,
% 0.20/0.59      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['83', '92'])).
% 0.20/0.59  thf('94', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.59      inference('simpl_trail', [status(thm)], ['14', '52'])).
% 0.20/0.59  thf('95', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.20/0.59      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 0.20/0.59  thf('96', plain, ($false), inference('demod', [status(thm)], ['80', '95'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
