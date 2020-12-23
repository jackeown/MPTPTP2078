%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cXtBaPG41m

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 262 expanded)
%              Number of leaves         :   24 (  79 expanded)
%              Depth                    :   19
%              Number of atoms          :  720 (2726 expanded)
%              Number of equality atoms :   72 ( 242 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','23'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('25',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','23'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ( ( k4_xboole_0 @ X15 @ X16 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('37',plain,(
    ! [X30: $i] :
      ( ( k1_subset_1 @ X30 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('38',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','39'])).

thf('44',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['38'])).

thf('47',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('48',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['38'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('50',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B_1 )
        | ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('56',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k4_xboole_0 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('57',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('62',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X30: $i] :
      ( ( k1_subset_1 @ X30 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('64',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B_1
       != ( k1_subset_1 @ sk_A ) )
      & ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','45','46','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cXtBaPG41m
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:37:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 228 iterations in 0.086s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(t38_subset_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.53         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.53            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.20/0.53        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.20/0.53       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf(d4_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.53       ( ![D:$i]:
% 0.20/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.53           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.20/0.53         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.20/0.53          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.20/0.53          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.53          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('eq_fact', [status(thm)], ['2'])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.53          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('eq_fact', [status(thm)], ['2'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.53          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('eq_fact', [status(thm)], ['2'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.20/0.53         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.20/0.53          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.20/0.53          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.20/0.53          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.20/0.53          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.53          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.20/0.53          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.20/0.53          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.53          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.53          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('eq_fact', [status(thm)], ['2'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.20/0.53          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.20/0.53      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((X0) = (k3_xboole_0 @ X0 @ X0)) | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '10'])).
% 0.20/0.53  thf('12', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.53  thf(t100_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X18 @ X19)
% 0.20/0.53           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.53           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['12', '15'])).
% 0.20/0.53  thf(d5_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.53       ( ![D:$i]:
% 0.20/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X12 @ X11)
% 0.20/0.53          | (r2_hidden @ X12 @ X9)
% 0.20/0.53          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.20/0.53         ((r2_hidden @ X12 @ X9)
% 0.20/0.53          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['12', '15'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X12 @ X11)
% 0.20/0.53          | ~ (r2_hidden @ X12 @ X10)
% 0.20/0.53          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X12 @ X10)
% 0.20/0.53          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('clc', [status(thm)], ['19', '23'])).
% 0.20/0.53  thf(t7_xboole_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X14 : $i]:
% 0.20/0.53         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('clc', [status(thm)], ['19', '23'])).
% 0.20/0.53  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf('28', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.53      inference('demod', [status(thm)], ['24', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.53           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.53           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf(l32_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         ((r1_tarski @ X15 @ X16)
% 0.20/0.53          | ((k4_xboole_0 @ X15 @ X16) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.53  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('37', plain, (![X30 : $i]: ((k1_subset_1 @ X30) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.20/0.53        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.20/0.53         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['37', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.20/0.53             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['37', '39'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.20/0.53             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.20/0.53       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['36', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.20/0.53       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['38'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X14 : $i]:
% 0.20/0.53         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.20/0.53         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['38'])).
% 0.20/0.53  thf(t28_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      ((((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 0.20/0.53         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.53          | (r2_hidden @ X6 @ X4)
% 0.20/0.53          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.53         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (r2_hidden @ X0 @ sk_B_1)
% 0.20/0.53           | (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))))
% 0.20/0.53         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['50', '52'])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (((((sk_B_1) = (k1_xboole_0))
% 0.20/0.53         | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))))
% 0.20/0.53         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['47', '53'])).
% 0.20/0.53  thf('55', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d5_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X31 : $i, X32 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))
% 0.20/0.53          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X12 @ X10)
% 0.20/0.53          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (((((sk_B_1) = (k1_xboole_0)) | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)))
% 0.20/0.53         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['54', '59'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (![X14 : $i]:
% 0.20/0.53         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_xboole_0)))
% 0.20/0.53         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.53      inference('clc', [status(thm)], ['60', '61'])).
% 0.20/0.53  thf('63', plain, (![X30 : $i]: ((k1_subset_1 @ X30) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) & 
% 0.20/0.53             ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['62', '65'])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.20/0.53       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['66'])).
% 0.20/0.53  thf('68', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['1', '45', '46', '67'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
