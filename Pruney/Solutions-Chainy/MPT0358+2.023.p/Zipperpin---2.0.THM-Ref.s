%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JsXeu1qkLq

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:25 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  120 (2238 expanded)
%              Number of leaves         :   25 ( 597 expanded)
%              Depth                    :   32
%              Number of atoms          :  890 (25615 expanded)
%              Number of equality atoms :   89 (2247 expanded)
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

thf('2',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('9',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('34',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','36'])).

thf('40',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','37'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ( ( k4_xboole_0 @ X15 @ X16 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('49',plain,(
    ! [X32: $i] :
      ( ( k1_subset_1 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('50',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('53',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('55',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','56','57'])).

thf('59',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','58'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('60',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('63',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('67',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X32: $i] :
      ( ( k1_subset_1 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('69',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('70',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','56'])).

thf('72',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['70','71'])).

thf('73',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('75',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('76',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('81',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['70','71'])).

thf('83',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('85',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X33 @ X34 )
        = ( k4_xboole_0 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('86',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('90',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['88','91'])).

thf('93',plain,(
    $false ),
    inference('sup-',[status(thm)],['83','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JsXeu1qkLq
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 15:13:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.63  % Solved by: fo/fo7.sh
% 0.37/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.63  % done 420 iterations in 0.153s
% 0.37/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.63  % SZS output start Refutation
% 0.37/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.63  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.63  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.37/0.63  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.63  thf(t38_subset_1, conjecture,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.63       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.37/0.63         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.37/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.63    (~( ![A:$i,B:$i]:
% 0.37/0.63        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.63          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.37/0.63            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.37/0.63    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.37/0.63  thf('0', plain,
% 0.37/0.63      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.37/0.63        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('1', plain,
% 0.37/0.63      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.37/0.63         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.37/0.63      inference('split', [status(esa)], ['0'])).
% 0.37/0.63  thf('2', plain,
% 0.37/0.63      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.37/0.63        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('3', plain,
% 0.37/0.63      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.37/0.63       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('split', [status(esa)], ['2'])).
% 0.37/0.63  thf(d4_xboole_0, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.37/0.63       ( ![D:$i]:
% 0.37/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.63           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.63  thf('4', plain,
% 0.37/0.63      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.37/0.63         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.37/0.63          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.37/0.63          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.37/0.63      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.63  thf('5', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.37/0.63          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.63      inference('eq_fact', [status(thm)], ['4'])).
% 0.37/0.63  thf(t7_xboole_0, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.63          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.63  thf('6', plain,
% 0.37/0.63      (![X14 : $i]:
% 0.37/0.63         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.37/0.63      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.63  thf('7', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.37/0.63          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.63      inference('eq_fact', [status(thm)], ['4'])).
% 0.37/0.63  thf('8', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.37/0.63          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.63      inference('eq_fact', [status(thm)], ['4'])).
% 0.37/0.63  thf('9', plain,
% 0.37/0.63      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.37/0.63         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.37/0.63          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.37/0.63          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.37/0.63          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.37/0.63      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.63  thf('10', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.37/0.63          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.37/0.63          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.37/0.63          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.63  thf('11', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.37/0.63          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.37/0.63          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.63      inference('simplify', [status(thm)], ['10'])).
% 0.37/0.63  thf('12', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.37/0.63          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.63      inference('eq_fact', [status(thm)], ['4'])).
% 0.37/0.63  thf('13', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.37/0.63          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.37/0.63      inference('clc', [status(thm)], ['11', '12'])).
% 0.37/0.63  thf('14', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (((X0) = (k3_xboole_0 @ X0 @ X0)) | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['7', '13'])).
% 0.37/0.63  thf('15', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.63      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.63  thf('16', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.63  thf(t100_xboole_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.63  thf('17', plain,
% 0.37/0.63      (![X18 : $i, X19 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X18 @ X19)
% 0.37/0.63           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.37/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.63  thf('18', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.63      inference('sup+', [status(thm)], ['16', '17'])).
% 0.37/0.63  thf('19', plain,
% 0.37/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['15', '18'])).
% 0.37/0.63  thf(d5_xboole_0, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.37/0.63       ( ![D:$i]:
% 0.37/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.63           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.37/0.63  thf('20', plain,
% 0.37/0.63      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X12 @ X11)
% 0.37/0.63          | ~ (r2_hidden @ X12 @ X10)
% 0.37/0.63          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.37/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.63  thf('21', plain,
% 0.37/0.63      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X12 @ X10)
% 0.37/0.63          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.37/0.63      inference('simplify', [status(thm)], ['20'])).
% 0.37/0.63  thf('22', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.37/0.63          | ~ (r2_hidden @ X1 @ X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['19', '21'])).
% 0.37/0.63  thf('23', plain,
% 0.37/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['15', '18'])).
% 0.37/0.63  thf(t48_xboole_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.63  thf('24', plain,
% 0.37/0.63      (![X22 : $i, X23 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.37/0.63           = (k3_xboole_0 @ X22 @ X23))),
% 0.37/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.63  thf('25', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.37/0.63           = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['23', '24'])).
% 0.37/0.63  thf('26', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.63      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.63  thf('27', plain,
% 0.37/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.37/0.63      inference('demod', [status(thm)], ['25', '26'])).
% 0.37/0.63  thf('28', plain,
% 0.37/0.63      (![X22 : $i, X23 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.37/0.63           = (k3_xboole_0 @ X22 @ X23))),
% 0.37/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.63  thf('29', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X0 @ X0)
% 0.37/0.63           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.37/0.63      inference('sup+', [status(thm)], ['27', '28'])).
% 0.37/0.63  thf('30', plain,
% 0.37/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['15', '18'])).
% 0.37/0.63  thf('31', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((k5_xboole_0 @ X0 @ X0)
% 0.37/0.63           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.37/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.37/0.63  thf('32', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.63  thf('33', plain,
% 0.37/0.63      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X6 @ X5)
% 0.37/0.63          | (r2_hidden @ X6 @ X4)
% 0.37/0.63          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.37/0.63      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.63  thf('34', plain,
% 0.37/0.63      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.37/0.63         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.37/0.63      inference('simplify', [status(thm)], ['33'])).
% 0.37/0.63  thf('35', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['32', '34'])).
% 0.37/0.63  thf('36', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['31', '35'])).
% 0.37/0.63  thf('37', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.63      inference('clc', [status(thm)], ['22', '36'])).
% 0.37/0.63  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['6', '37'])).
% 0.37/0.63  thf('39', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.63      inference('clc', [status(thm)], ['22', '36'])).
% 0.37/0.63  thf('40', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.37/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.63  thf('41', plain,
% 0.37/0.63      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['5', '40'])).
% 0.37/0.63  thf('42', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.63      inference('sup+', [status(thm)], ['16', '17'])).
% 0.37/0.63  thf('43', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.63           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['41', '42'])).
% 0.37/0.63  thf('44', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['6', '37'])).
% 0.37/0.63  thf('45', plain,
% 0.37/0.63      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.37/0.63  thf(l32_xboole_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.63  thf('46', plain,
% 0.37/0.63      (![X15 : $i, X16 : $i]:
% 0.37/0.63         ((r1_tarski @ X15 @ X16)
% 0.37/0.63          | ((k4_xboole_0 @ X15 @ X16) != (k1_xboole_0)))),
% 0.37/0.63      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.63  thf('47', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.63  thf('48', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.63      inference('simplify', [status(thm)], ['47'])).
% 0.37/0.63  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.63  thf('49', plain, (![X32 : $i]: ((k1_subset_1 @ X32) = (k1_xboole_0))),
% 0.37/0.63      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.37/0.63  thf('50', plain,
% 0.37/0.63      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.37/0.63         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.63      inference('split', [status(esa)], ['0'])).
% 0.37/0.63  thf('51', plain,
% 0.37/0.63      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.63      inference('sup+', [status(thm)], ['49', '50'])).
% 0.37/0.63  thf('52', plain,
% 0.37/0.63      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.37/0.63         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.37/0.63      inference('split', [status(esa)], ['2'])).
% 0.37/0.63  thf('53', plain,
% 0.37/0.63      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.37/0.63         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.37/0.63             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['51', '52'])).
% 0.37/0.63  thf('54', plain,
% 0.37/0.63      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.63      inference('sup+', [status(thm)], ['49', '50'])).
% 0.37/0.63  thf('55', plain,
% 0.37/0.63      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.37/0.63         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.37/0.63             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.63      inference('demod', [status(thm)], ['53', '54'])).
% 0.37/0.63  thf('56', plain,
% 0.37/0.63      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.37/0.63       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['48', '55'])).
% 0.37/0.63  thf('57', plain,
% 0.37/0.63      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.37/0.63       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.37/0.63      inference('split', [status(esa)], ['0'])).
% 0.37/0.63  thf('58', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('sat_resolution*', [status(thm)], ['3', '56', '57'])).
% 0.37/0.63  thf('59', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.37/0.63      inference('simpl_trail', [status(thm)], ['1', '58'])).
% 0.37/0.63  thf(t28_xboole_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.63  thf('60', plain,
% 0.37/0.63      (![X20 : $i, X21 : $i]:
% 0.37/0.63         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.37/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.63  thf('61', plain,
% 0.37/0.63      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['59', '60'])).
% 0.37/0.63  thf('62', plain,
% 0.37/0.63      (![X14 : $i]:
% 0.37/0.63         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.37/0.63      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.63  thf('63', plain,
% 0.37/0.63      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.37/0.63         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.37/0.63      inference('simplify', [status(thm)], ['33'])).
% 0.37/0.63  thf('64', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.63          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.63  thf('65', plain,
% 0.37/0.63      (((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.37/0.63        | ((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.37/0.63            = (k1_xboole_0)))),
% 0.37/0.63      inference('sup+', [status(thm)], ['61', '64'])).
% 0.37/0.63  thf('66', plain,
% 0.37/0.63      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['59', '60'])).
% 0.37/0.63  thf('67', plain,
% 0.37/0.63      (((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.37/0.63        | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.63      inference('demod', [status(thm)], ['65', '66'])).
% 0.37/0.63  thf('68', plain, (![X32 : $i]: ((k1_subset_1 @ X32) = (k1_xboole_0))),
% 0.37/0.63      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.37/0.63  thf('69', plain,
% 0.37/0.63      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.37/0.63         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.63      inference('split', [status(esa)], ['2'])).
% 0.37/0.63  thf('70', plain,
% 0.37/0.63      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['68', '69'])).
% 0.37/0.63  thf('71', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.37/0.63      inference('sat_resolution*', [status(thm)], ['3', '56'])).
% 0.37/0.63  thf('72', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.37/0.63      inference('simpl_trail', [status(thm)], ['70', '71'])).
% 0.37/0.63  thf('73', plain,
% 0.37/0.63      ((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.37/0.63      inference('simplify_reflect-', [status(thm)], ['67', '72'])).
% 0.37/0.63  thf('74', plain,
% 0.37/0.63      (![X14 : $i]:
% 0.37/0.63         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.37/0.63      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.63  thf('75', plain,
% 0.37/0.63      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X2 @ X3)
% 0.37/0.63          | ~ (r2_hidden @ X2 @ X4)
% 0.37/0.63          | (r2_hidden @ X2 @ X5)
% 0.37/0.63          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.37/0.63      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.63  thf('76', plain,
% 0.37/0.63      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.63         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 0.37/0.63          | ~ (r2_hidden @ X2 @ X4)
% 0.37/0.63          | ~ (r2_hidden @ X2 @ X3))),
% 0.37/0.63      inference('simplify', [status(thm)], ['75'])).
% 0.37/0.63  thf('77', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (((X0) = (k1_xboole_0))
% 0.37/0.63          | ~ (r2_hidden @ (sk_B @ X0) @ X1)
% 0.37/0.63          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['74', '76'])).
% 0.37/0.63  thf('78', plain,
% 0.37/0.63      (((r2_hidden @ (sk_B @ sk_B_1) @ 
% 0.37/0.63         (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 0.37/0.63        | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['73', '77'])).
% 0.37/0.63  thf('79', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.63  thf('80', plain,
% 0.37/0.63      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['59', '60'])).
% 0.37/0.63  thf('81', plain,
% 0.37/0.63      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.63      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.37/0.63  thf('82', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.37/0.63      inference('simpl_trail', [status(thm)], ['70', '71'])).
% 0.37/0.63  thf('83', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.37/0.63      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.37/0.63  thf('84', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(d5_subset_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.63       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.37/0.63  thf('85', plain,
% 0.37/0.63      (![X33 : $i, X34 : $i]:
% 0.37/0.63         (((k3_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))
% 0.37/0.63          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 0.37/0.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.37/0.63  thf('86', plain,
% 0.37/0.63      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['84', '85'])).
% 0.37/0.63  thf('87', plain,
% 0.37/0.63      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X12 @ X10)
% 0.37/0.63          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.37/0.63      inference('simplify', [status(thm)], ['20'])).
% 0.37/0.63  thf('88', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.37/0.63          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['86', '87'])).
% 0.37/0.63  thf('89', plain,
% 0.37/0.63      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['59', '60'])).
% 0.37/0.63  thf('90', plain,
% 0.37/0.63      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.37/0.63         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.37/0.63      inference('simplify', [status(thm)], ['33'])).
% 0.37/0.63  thf('91', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.37/0.63          | (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['89', '90'])).
% 0.37/0.63  thf('92', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.37/0.63      inference('clc', [status(thm)], ['88', '91'])).
% 0.37/0.63  thf('93', plain, ($false), inference('sup-', [status(thm)], ['83', '92'])).
% 0.37/0.63  
% 0.37/0.63  % SZS output end Refutation
% 0.37/0.63  
% 0.48/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
