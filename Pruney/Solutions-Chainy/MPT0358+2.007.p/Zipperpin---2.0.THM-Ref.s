%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TjSQ8UVWUO

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:22 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 316 expanded)
%              Number of leaves         :   31 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  707 (2501 expanded)
%              Number of equality atoms :   65 ( 244 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('1',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

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

thf('7',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B_1 )
        | ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ( X15 != X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X16: $i] :
      ( r1_tarski @ X16 @ X16 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_tarski @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X37: $i] :
      ( ( k1_subset_1 @ X37 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('17',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('18',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('22',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('25',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['9','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['7','25'])).

thf('27',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('29',plain,(
    ! [X37: $i] :
      ( ( k1_subset_1 @ X37 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('30',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['9','23'])).

thf('32',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['27','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('36',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ X35 )
      | ( r2_hidden @ X34 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('40',plain,(
    ! [X40: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('41',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('42',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X32 @ X31 )
      | ( r1_tarski @ X32 @ X30 )
      | ( X31
       != ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('43',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ X32 @ X30 )
      | ~ ( r2_hidden @ X32 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['46','47'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['36','50'])).

thf('52',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','51'])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('55',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['46','47'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','31'])).

thf('66',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('68',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('69',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['46','47'])).

thf('73',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','31'])).

thf('75',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['57','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TjSQ8UVWUO
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:22:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 458 iterations in 0.131s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.41/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.41/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(t7_xboole_0, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.41/0.59          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      (![X14 : $i]:
% 0.41/0.59         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.41/0.59  thf(t38_subset_1, conjecture,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.59       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.41/0.59         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i,B:$i]:
% 0.41/0.59        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.59          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.41/0.59            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.41/0.59        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.41/0.59         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.41/0.59      inference('split', [status(esa)], ['1'])).
% 0.41/0.59  thf(t28_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (![X23 : $i, X24 : $i]:
% 0.41/0.59         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.41/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      ((((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 0.41/0.59         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.59  thf(d4_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.41/0.59       ( ![D:$i]:
% 0.41/0.59         ( ( r2_hidden @ D @ C ) <=>
% 0.41/0.59           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X6 @ X5)
% 0.41/0.59          | (r2_hidden @ X6 @ X4)
% 0.41/0.59          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.41/0.59         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      ((![X0 : $i]:
% 0.41/0.59          (~ (r2_hidden @ X0 @ sk_B_1)
% 0.41/0.59           | (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))))
% 0.41/0.59         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['4', '6'])).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.41/0.59        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.41/0.59       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.41/0.59      inference('split', [status(esa)], ['8'])).
% 0.41/0.59  thf(t46_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      (![X25 : $i, X26 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X25 @ (k2_xboole_0 @ X25 @ X26)) = (k1_xboole_0))),
% 0.41/0.59      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.41/0.59  thf(d10_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]: ((r1_tarski @ X15 @ X16) | ((X15) != (X16)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.59  thf('12', plain, (![X16 : $i]: (r1_tarski @ X16 @ X16)),
% 0.41/0.59      inference('simplify', [status(thm)], ['11'])).
% 0.41/0.59  thf(t106_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.41/0.59       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.59         ((r1_tarski @ X20 @ X21)
% 0.41/0.59          | ~ (r1_tarski @ X20 @ (k4_xboole_0 @ X21 @ X22)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 0.41/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.59  thf('15', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.41/0.59      inference('sup+', [status(thm)], ['10', '14'])).
% 0.41/0.59  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.41/0.59  thf('16', plain, (![X37 : $i]: ((k1_subset_1 @ X37) = (k1_xboole_0))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.41/0.59         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.41/0.59      inference('split', [status(esa)], ['1'])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.41/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.41/0.59         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.41/0.59      inference('split', [status(esa)], ['8'])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.41/0.59         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.41/0.59             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.41/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.41/0.59         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.41/0.59             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.41/0.59      inference('demod', [status(thm)], ['20', '21'])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.41/0.59       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['15', '22'])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.41/0.59       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.41/0.59      inference('split', [status(esa)], ['1'])).
% 0.41/0.59  thf('25', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['9', '23', '24'])).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.41/0.59          | (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['7', '25'])).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      ((((sk_B_1) = (k1_xboole_0))
% 0.41/0.59        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['0', '26'])).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.41/0.59         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.41/0.59      inference('split', [status(esa)], ['8'])).
% 0.41/0.59  thf('29', plain, (![X37 : $i]: ((k1_subset_1 @ X37) = (k1_xboole_0))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.41/0.59      inference('demod', [status(thm)], ['28', '29'])).
% 0.41/0.59  thf('31', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['9', '23'])).
% 0.41/0.59  thf('32', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf('33', plain,
% 0.41/0.59      ((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.41/0.59      inference('simplify_reflect-', [status(thm)], ['27', '32'])).
% 0.41/0.59  thf('34', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(d5_subset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.59       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      (![X38 : $i, X39 : $i]:
% 0.41/0.59         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 0.41/0.59          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.59  thf('37', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(d2_subset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( v1_xboole_0 @ A ) =>
% 0.41/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.41/0.59       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.59  thf('38', plain,
% 0.41/0.59      (![X34 : $i, X35 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X34 @ X35)
% 0.41/0.59          | (r2_hidden @ X34 @ X35)
% 0.41/0.59          | (v1_xboole_0 @ X35))),
% 0.41/0.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.59  thf('39', plain,
% 0.41/0.59      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.59        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.41/0.59  thf(fc1_subset_1, axiom,
% 0.41/0.59    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.59  thf('40', plain, (![X40 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 0.41/0.59      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.41/0.59  thf('41', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.59      inference('clc', [status(thm)], ['39', '40'])).
% 0.41/0.59  thf(d1_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.41/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X32 @ X31)
% 0.41/0.59          | (r1_tarski @ X32 @ X30)
% 0.41/0.59          | ((X31) != (k1_zfmisc_1 @ X30)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.41/0.59  thf('43', plain,
% 0.41/0.59      (![X30 : $i, X32 : $i]:
% 0.41/0.59         ((r1_tarski @ X32 @ X30) | ~ (r2_hidden @ X32 @ (k1_zfmisc_1 @ X30)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['42'])).
% 0.41/0.59  thf('44', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.41/0.59      inference('sup-', [status(thm)], ['41', '43'])).
% 0.41/0.59  thf('45', plain,
% 0.41/0.59      (![X23 : $i, X24 : $i]:
% 0.41/0.59         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.41/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.59  thf('46', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.41/0.59  thf('47', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.59  thf('48', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.41/0.59      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.59  thf(t100_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.41/0.59  thf('49', plain,
% 0.41/0.59      (![X18 : $i, X19 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X18 @ X19)
% 0.41/0.59           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.59  thf('50', plain,
% 0.41/0.59      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.41/0.59      inference('sup+', [status(thm)], ['48', '49'])).
% 0.41/0.59  thf('51', plain,
% 0.41/0.59      (((k3_subset_1 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.41/0.59      inference('sup+', [status(thm)], ['36', '50'])).
% 0.41/0.59  thf('52', plain,
% 0.41/0.59      ((r2_hidden @ (sk_B @ sk_B_1) @ (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.41/0.59      inference('demod', [status(thm)], ['33', '51'])).
% 0.41/0.59  thf('53', plain,
% 0.41/0.59      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.41/0.59      inference('sup+', [status(thm)], ['48', '49'])).
% 0.41/0.59  thf(d5_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.41/0.59       ( ![D:$i]:
% 0.41/0.59         ( ( r2_hidden @ D @ C ) <=>
% 0.41/0.59           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.41/0.59  thf('54', plain,
% 0.41/0.59      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X12 @ X11)
% 0.41/0.59          | ~ (r2_hidden @ X12 @ X10)
% 0.41/0.59          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.41/0.59  thf('55', plain,
% 0.41/0.59      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X12 @ X10)
% 0.41/0.59          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['54'])).
% 0.41/0.59  thf('56', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_A @ sk_B_1))
% 0.41/0.59          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['53', '55'])).
% 0.41/0.59  thf('57', plain, (~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.41/0.59      inference('sup-', [status(thm)], ['52', '56'])).
% 0.41/0.59  thf('58', plain,
% 0.41/0.59      (![X14 : $i]:
% 0.41/0.59         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.41/0.59  thf('59', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.41/0.59      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.59  thf('60', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.59  thf('61', plain,
% 0.41/0.59      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.41/0.59         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.41/0.59  thf('62', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['60', '61'])).
% 0.41/0.59  thf('63', plain,
% 0.41/0.59      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | (r2_hidden @ X0 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['59', '62'])).
% 0.41/0.59  thf('64', plain,
% 0.41/0.59      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['58', '63'])).
% 0.41/0.59  thf('65', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf('66', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)),
% 0.41/0.59      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.41/0.59  thf('67', plain,
% 0.41/0.59      (![X14 : $i]:
% 0.41/0.59         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.41/0.59  thf('68', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X2 @ X3)
% 0.41/0.59          | ~ (r2_hidden @ X2 @ X4)
% 0.41/0.59          | (r2_hidden @ X2 @ X5)
% 0.41/0.59          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.41/0.59  thf('69', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.59         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 0.41/0.59          | ~ (r2_hidden @ X2 @ X4)
% 0.41/0.59          | ~ (r2_hidden @ X2 @ X3))),
% 0.41/0.59      inference('simplify', [status(thm)], ['68'])).
% 0.41/0.59  thf('70', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (((X0) = (k1_xboole_0))
% 0.41/0.59          | ~ (r2_hidden @ (sk_B @ X0) @ X1)
% 0.41/0.59          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['67', '69'])).
% 0.41/0.59  thf('71', plain,
% 0.41/0.59      (((r2_hidden @ (sk_B @ sk_B_1) @ (k3_xboole_0 @ sk_A @ sk_B_1))
% 0.41/0.59        | ((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['66', '70'])).
% 0.41/0.59  thf('72', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.41/0.59      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.59  thf('73', plain,
% 0.41/0.59      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['71', '72'])).
% 0.41/0.59  thf('74', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf('75', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.41/0.59      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.41/0.59  thf('76', plain, ($false), inference('demod', [status(thm)], ['57', '75'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
