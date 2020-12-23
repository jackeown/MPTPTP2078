%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1nrrAzBWcq

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:26 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 282 expanded)
%              Number of leaves         :   28 (  86 expanded)
%              Depth                    :   16
%              Number of atoms          :  720 (2267 expanded)
%              Number of equality atoms :   74 ( 243 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','22'])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','23'])).

thf('25',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['25'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X26: $i] :
      ( ( k1_subset_1 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('28',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('29',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('33',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('34',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['32','33'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('35',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( r1_tarski @ X21 @ X19 )
      | ( X20
       != ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('36',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ X21 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','37'])).

thf('39',plain,(
    ! [X26: $i] :
      ( ( k1_subset_1 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X31: $i] :
      ( ( k2_subset_1 @ X31 )
      = ( k3_subset_1 @ X31 @ ( k1_subset_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('41',plain,(
    ! [X27: $i] :
      ( ( k2_subset_1 @ X27 )
      = X27 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('42',plain,(
    ! [X31: $i] :
      ( X31
      = ( k3_subset_1 @ X31 @ ( k1_subset_1 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('48',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','49'])).

thf('51',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('52',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['26','50','51'])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','52'])).

thf('54',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','57'])).

thf('59',plain,(
    ! [X26: $i] :
      ( ( k1_subset_1 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('60',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('61',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['26','50'])).

thf('63',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('66',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['67'])).

thf('69',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['64','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('71',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('72',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','75'])).

thf('77',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['61','62'])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1nrrAzBWcq
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.69  % Solved by: fo/fo7.sh
% 0.46/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.69  % done 689 iterations in 0.239s
% 0.46/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.69  % SZS output start Refutation
% 0.46/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.69  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.46/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.69  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.69  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.46/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(t7_xboole_0, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.69          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.69  thf('0', plain,
% 0.46/0.69      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.46/0.69      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.69  thf(t38_subset_1, conjecture,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.46/0.69         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.46/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.69    (~( ![A:$i,B:$i]:
% 0.46/0.69        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.46/0.69            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.46/0.69    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.46/0.69  thf('1', plain,
% 0.46/0.69      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.46/0.69        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('2', plain,
% 0.46/0.69      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.46/0.69         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.46/0.69      inference('split', [status(esa)], ['1'])).
% 0.46/0.69  thf(t28_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.69  thf('3', plain,
% 0.46/0.69      (![X12 : $i, X13 : $i]:
% 0.46/0.69         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.46/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.69  thf('4', plain,
% 0.46/0.69      ((((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 0.46/0.69         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.69  thf(t100_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.69  thf('5', plain,
% 0.46/0.69      (![X10 : $i, X11 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X10 @ X11)
% 0.46/0.69           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.69  thf('6', plain,
% 0.46/0.69      ((((k4_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.46/0.69          = (k5_xboole_0 @ sk_B_1 @ sk_B_1)))
% 0.46/0.69         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.46/0.69      inference('sup+', [status(thm)], ['4', '5'])).
% 0.46/0.69  thf('7', plain,
% 0.46/0.69      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.46/0.69      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.69  thf(d5_xboole_0, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.46/0.69       ( ![D:$i]:
% 0.46/0.69         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.69           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.46/0.69  thf('8', plain,
% 0.46/0.69      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X4 @ X3)
% 0.46/0.69          | (r2_hidden @ X4 @ X1)
% 0.46/0.69          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.69  thf('9', plain,
% 0.46/0.69      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.46/0.69         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['8'])).
% 0.46/0.69  thf('10', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.46/0.69          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.46/0.69      inference('sup-', [status(thm)], ['7', '9'])).
% 0.46/0.69  thf('11', plain,
% 0.46/0.69      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.46/0.69      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.69  thf('12', plain,
% 0.46/0.69      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X4 @ X3)
% 0.46/0.69          | ~ (r2_hidden @ X4 @ X2)
% 0.46/0.69          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.69  thf('13', plain,
% 0.46/0.69      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X4 @ X2)
% 0.46/0.69          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.69  thf('14', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.46/0.69          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['11', '13'])).
% 0.46/0.69  thf('15', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.46/0.69          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['10', '14'])).
% 0.46/0.69  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.69      inference('simplify', [status(thm)], ['15'])).
% 0.46/0.69  thf('17', plain,
% 0.46/0.69      (![X10 : $i, X11 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X10 @ X11)
% 0.46/0.69           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.69  thf('18', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.46/0.69      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.69  thf(d10_xboole_0, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.69  thf('19', plain,
% 0.46/0.69      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.69  thf('20', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.46/0.69      inference('simplify', [status(thm)], ['19'])).
% 0.46/0.69  thf('21', plain,
% 0.46/0.69      (![X12 : $i, X13 : $i]:
% 0.46/0.69         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.46/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.69  thf('22', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.69  thf('23', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.69      inference('demod', [status(thm)], ['18', '22'])).
% 0.46/0.69  thf('24', plain,
% 0.46/0.69      ((((k4_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 0.46/0.69         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.46/0.69      inference('demod', [status(thm)], ['6', '23'])).
% 0.46/0.69  thf('25', plain,
% 0.46/0.69      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.46/0.69        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('26', plain,
% 0.46/0.69      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.46/0.69       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.46/0.69      inference('split', [status(esa)], ['25'])).
% 0.46/0.69  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.69  thf('27', plain, (![X26 : $i]: ((k1_subset_1 @ X26) = (k1_xboole_0))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.46/0.69  thf('28', plain,
% 0.46/0.69      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.46/0.69         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.69      inference('split', [status(esa)], ['1'])).
% 0.46/0.69  thf('29', plain,
% 0.46/0.69      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.69      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.69  thf('30', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(d2_subset_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( v1_xboole_0 @ A ) =>
% 0.46/0.69         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.46/0.69       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.69         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.69  thf('31', plain,
% 0.46/0.69      (![X23 : $i, X24 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X23 @ X24)
% 0.46/0.69          | (r2_hidden @ X23 @ X24)
% 0.46/0.69          | (v1_xboole_0 @ X24))),
% 0.46/0.69      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.69  thf('32', plain,
% 0.46/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.69        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.69  thf(fc1_subset_1, axiom,
% 0.46/0.69    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.69  thf('33', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.69  thf('34', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.69      inference('clc', [status(thm)], ['32', '33'])).
% 0.46/0.69  thf(d1_zfmisc_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.46/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.46/0.69  thf('35', plain,
% 0.46/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X21 @ X20)
% 0.46/0.69          | (r1_tarski @ X21 @ X19)
% 0.46/0.69          | ((X20) != (k1_zfmisc_1 @ X19)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.69  thf('36', plain,
% 0.46/0.69      (![X19 : $i, X21 : $i]:
% 0.46/0.69         ((r1_tarski @ X21 @ X19) | ~ (r2_hidden @ X21 @ (k1_zfmisc_1 @ X19)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['35'])).
% 0.46/0.69  thf('37', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.46/0.69      inference('sup-', [status(thm)], ['34', '36'])).
% 0.46/0.69  thf('38', plain,
% 0.46/0.69      (((r1_tarski @ k1_xboole_0 @ sk_A))
% 0.46/0.69         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.69      inference('sup+', [status(thm)], ['29', '37'])).
% 0.46/0.69  thf('39', plain, (![X26 : $i]: ((k1_subset_1 @ X26) = (k1_xboole_0))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.46/0.69  thf(t22_subset_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.46/0.69  thf('40', plain,
% 0.46/0.69      (![X31 : $i]:
% 0.46/0.69         ((k2_subset_1 @ X31) = (k3_subset_1 @ X31 @ (k1_subset_1 @ X31)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.46/0.69  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.46/0.69  thf('41', plain, (![X27 : $i]: ((k2_subset_1 @ X27) = (X27))),
% 0.46/0.69      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.69  thf('42', plain,
% 0.46/0.69      (![X31 : $i]: ((X31) = (k3_subset_1 @ X31 @ (k1_subset_1 @ X31)))),
% 0.46/0.69      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.69  thf('43', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['39', '42'])).
% 0.46/0.69  thf('44', plain,
% 0.46/0.69      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.69      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.69  thf('45', plain,
% 0.46/0.69      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.46/0.69         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.46/0.69      inference('split', [status(esa)], ['25'])).
% 0.46/0.69  thf('46', plain,
% 0.46/0.69      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.46/0.69         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.46/0.69             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.69  thf('47', plain,
% 0.46/0.69      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.69      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.69  thf('48', plain,
% 0.46/0.69      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.46/0.69         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.46/0.69             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.69      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.69  thf('49', plain,
% 0.46/0.69      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.46/0.69         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.46/0.69             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['43', '48'])).
% 0.46/0.69  thf('50', plain,
% 0.46/0.69      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.46/0.69       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['38', '49'])).
% 0.46/0.69  thf('51', plain,
% 0.46/0.69      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.46/0.69       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['1'])).
% 0.46/0.69  thf('52', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.46/0.69      inference('sat_resolution*', [status(thm)], ['26', '50', '51'])).
% 0.46/0.69  thf('53', plain,
% 0.46/0.69      (((k4_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.46/0.69      inference('simpl_trail', [status(thm)], ['24', '52'])).
% 0.46/0.69  thf('54', plain,
% 0.46/0.69      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.46/0.69      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.69  thf('55', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.69          | (r2_hidden @ X0 @ X2)
% 0.46/0.69          | (r2_hidden @ X0 @ X3)
% 0.46/0.69          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.69  thf('56', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.46/0.69          | (r2_hidden @ X0 @ X2)
% 0.46/0.69          | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.69      inference('simplify', [status(thm)], ['55'])).
% 0.46/0.69  thf('57', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         (((X0) = (k1_xboole_0))
% 0.46/0.69          | (r2_hidden @ (sk_B @ X0) @ X1)
% 0.46/0.69          | (r2_hidden @ (sk_B @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['54', '56'])).
% 0.46/0.69  thf('58', plain,
% 0.46/0.69      (((r2_hidden @ (sk_B @ sk_B_1) @ k1_xboole_0)
% 0.46/0.69        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.46/0.69        | ((sk_B_1) = (k1_xboole_0)))),
% 0.46/0.69      inference('sup+', [status(thm)], ['53', '57'])).
% 0.46/0.69  thf('59', plain, (![X26 : $i]: ((k1_subset_1 @ X26) = (k1_xboole_0))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.46/0.69  thf('60', plain,
% 0.46/0.69      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.46/0.69         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.69      inference('split', [status(esa)], ['25'])).
% 0.46/0.69  thf('61', plain,
% 0.46/0.69      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.69  thf('62', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.46/0.69      inference('sat_resolution*', [status(thm)], ['26', '50'])).
% 0.46/0.69  thf('63', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.69      inference('simpl_trail', [status(thm)], ['61', '62'])).
% 0.46/0.69  thf('64', plain,
% 0.46/0.69      (((r2_hidden @ (sk_B @ sk_B_1) @ k1_xboole_0)
% 0.46/0.69        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.46/0.69      inference('simplify_reflect-', [status(thm)], ['58', '63'])).
% 0.46/0.69  thf('65', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.69      inference('simplify', [status(thm)], ['15'])).
% 0.46/0.69  thf('66', plain,
% 0.46/0.69      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X4 @ X2)
% 0.46/0.69          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.69  thf('67', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.69  thf('68', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.69      inference('condensation', [status(thm)], ['67'])).
% 0.46/0.69  thf('69', plain,
% 0.46/0.69      ((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.46/0.69      inference('clc', [status(thm)], ['64', '68'])).
% 0.46/0.69  thf('70', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(d5_subset_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.46/0.69  thf('71', plain,
% 0.46/0.69      (![X28 : $i, X29 : $i]:
% 0.46/0.69         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 0.46/0.69          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.69  thf('72', plain,
% 0.46/0.69      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.46/0.69      inference('sup-', [status(thm)], ['70', '71'])).
% 0.46/0.69  thf('73', plain,
% 0.46/0.69      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X4 @ X2)
% 0.46/0.69          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.69  thf('74', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.46/0.69          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.46/0.69      inference('sup-', [status(thm)], ['72', '73'])).
% 0.46/0.69  thf('75', plain, (~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.46/0.69      inference('sup-', [status(thm)], ['69', '74'])).
% 0.46/0.69  thf('76', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['0', '75'])).
% 0.46/0.69  thf('77', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.69      inference('simpl_trail', [status(thm)], ['61', '62'])).
% 0.46/0.69  thf('78', plain, ($false),
% 0.46/0.69      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.46/0.69  
% 0.46/0.69  % SZS output end Refutation
% 0.46/0.69  
% 0.54/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
