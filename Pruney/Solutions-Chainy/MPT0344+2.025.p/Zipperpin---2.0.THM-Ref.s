%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qQXbiH3PuV

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:41 EST 2020

% Result     : Theorem 4.00s
% Output     : Refutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 421 expanded)
%              Number of leaves         :   38 ( 143 expanded)
%              Depth                    :   16
%              Number of atoms          :  750 (3161 expanded)
%              Number of equality atoms :   79 ( 283 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X21 @ X21 @ X22 @ X23 )
      = ( k1_enumset1 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t10_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ~ ( ( B != k1_xboole_0 )
            & ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ~ ( r2_hidden @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_subset_1])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( r2_hidden @ X57 @ X58 )
      | ( r2_hidden @ X57 @ X59 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( r2_hidden @ X54 @ X55 )
      | ( m1_subset_1 @ X54 @ X55 )
      | ( v1_xboole_0 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('17',plain,(
    ! [X60: $i] :
      ( ~ ( r2_hidden @ X60 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X60 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['15','20'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','23'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('25',plain,(
    ! [X46: $i,X48: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X46 ) @ X48 )
      | ~ ( r2_hidden @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('26',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('28',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X12 @ X13 @ X14 ) @ ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k4_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k3_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ ( sk_B @ sk_B_1 ) @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ ( sk_B @ sk_B_1 ) @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','38'])).

thf('40',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['4','39'])).

thf('41',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('42',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('44',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('45',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('49',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('52',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('53',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42','43','60','63'])).

thf('65',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('66',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X52 != X51 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X52 ) @ ( k1_tarski @ X51 ) )
       != ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('67',plain,(
    ! [X51: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X51 ) @ ( k1_tarski @ X51 ) )
     != ( k1_tarski @ X51 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
 != ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('71',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('72',plain,(
    ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qQXbiH3PuV
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.00/4.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.00/4.21  % Solved by: fo/fo7.sh
% 4.00/4.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.00/4.21  % done 5444 iterations in 3.757s
% 4.00/4.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.00/4.21  % SZS output start Refutation
% 4.00/4.21  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 4.00/4.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.00/4.21  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 4.00/4.21  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.00/4.21  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.00/4.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.00/4.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.00/4.21  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.00/4.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.00/4.21  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.00/4.21  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 4.00/4.21  thf(sk_B_type, type, sk_B: $i > $i).
% 4.00/4.21  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 4.00/4.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.00/4.21  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.00/4.21  thf(sk_A_type, type, sk_A: $i).
% 4.00/4.21  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.00/4.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.00/4.21  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.00/4.21  thf(t71_enumset1, axiom,
% 4.00/4.21    (![A:$i,B:$i,C:$i]:
% 4.00/4.21     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 4.00/4.21  thf('0', plain,
% 4.00/4.21      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.00/4.21         ((k2_enumset1 @ X21 @ X21 @ X22 @ X23)
% 4.00/4.21           = (k1_enumset1 @ X21 @ X22 @ X23))),
% 4.00/4.21      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.00/4.21  thf(t70_enumset1, axiom,
% 4.00/4.21    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 4.00/4.21  thf('1', plain,
% 4.00/4.21      (![X19 : $i, X20 : $i]:
% 4.00/4.21         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 4.00/4.21      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.00/4.21  thf('2', plain,
% 4.00/4.21      (![X0 : $i, X1 : $i]:
% 4.00/4.21         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 4.00/4.21      inference('sup+', [status(thm)], ['0', '1'])).
% 4.00/4.21  thf(t69_enumset1, axiom,
% 4.00/4.21    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.00/4.21  thf('3', plain, (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 4.00/4.21      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.00/4.21  thf('4', plain,
% 4.00/4.21      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 4.00/4.21      inference('sup+', [status(thm)], ['2', '3'])).
% 4.00/4.21  thf('5', plain,
% 4.00/4.21      (![X19 : $i, X20 : $i]:
% 4.00/4.21         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 4.00/4.21      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.00/4.21  thf(t7_xboole_0, axiom,
% 4.00/4.21    (![A:$i]:
% 4.00/4.21     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.00/4.21          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 4.00/4.21  thf('6', plain,
% 4.00/4.21      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 4.00/4.21      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.00/4.21  thf(t10_subset_1, conjecture,
% 4.00/4.21    (![A:$i,B:$i]:
% 4.00/4.21     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.00/4.21       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 4.00/4.21            ( ![C:$i]:
% 4.00/4.21              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 4.00/4.21  thf(zf_stmt_0, negated_conjecture,
% 4.00/4.21    (~( ![A:$i,B:$i]:
% 4.00/4.21        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.00/4.21          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 4.00/4.21               ( ![C:$i]:
% 4.00/4.21                 ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ) )),
% 4.00/4.21    inference('cnf.neg', [status(esa)], [t10_subset_1])).
% 4.00/4.21  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 4.00/4.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.21  thf(l3_subset_1, axiom,
% 4.00/4.21    (![A:$i,B:$i]:
% 4.00/4.21     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.00/4.21       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 4.00/4.21  thf('8', plain,
% 4.00/4.21      (![X57 : $i, X58 : $i, X59 : $i]:
% 4.00/4.21         (~ (r2_hidden @ X57 @ X58)
% 4.00/4.21          | (r2_hidden @ X57 @ X59)
% 4.00/4.21          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X59)))),
% 4.00/4.21      inference('cnf', [status(esa)], [l3_subset_1])).
% 4.00/4.21  thf('9', plain,
% 4.00/4.21      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 4.00/4.21      inference('sup-', [status(thm)], ['7', '8'])).
% 4.00/4.21  thf('10', plain,
% 4.00/4.21      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 4.00/4.21      inference('sup-', [status(thm)], ['6', '9'])).
% 4.00/4.21  thf('11', plain, (((sk_B_1) != (k1_xboole_0))),
% 4.00/4.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.21  thf('12', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)),
% 4.00/4.21      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 4.00/4.21  thf('13', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)),
% 4.00/4.21      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 4.00/4.21  thf(d2_subset_1, axiom,
% 4.00/4.21    (![A:$i,B:$i]:
% 4.00/4.21     ( ( ( v1_xboole_0 @ A ) =>
% 4.00/4.21         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 4.00/4.21       ( ( ~( v1_xboole_0 @ A ) ) =>
% 4.00/4.21         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 4.00/4.21  thf('14', plain,
% 4.00/4.21      (![X54 : $i, X55 : $i]:
% 4.00/4.21         (~ (r2_hidden @ X54 @ X55)
% 4.00/4.21          | (m1_subset_1 @ X54 @ X55)
% 4.00/4.21          | (v1_xboole_0 @ X55))),
% 4.00/4.21      inference('cnf', [status(esa)], [d2_subset_1])).
% 4.00/4.21  thf('15', plain,
% 4.00/4.21      (((v1_xboole_0 @ sk_A) | (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A))),
% 4.00/4.21      inference('sup-', [status(thm)], ['13', '14'])).
% 4.00/4.21  thf('16', plain,
% 4.00/4.21      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 4.00/4.21      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.00/4.21  thf('17', plain,
% 4.00/4.21      (![X60 : $i]:
% 4.00/4.21         (~ (r2_hidden @ X60 @ sk_B_1) | ~ (m1_subset_1 @ X60 @ sk_A))),
% 4.00/4.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.21  thf('18', plain,
% 4.00/4.21      ((((sk_B_1) = (k1_xboole_0)) | ~ (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A))),
% 4.00/4.21      inference('sup-', [status(thm)], ['16', '17'])).
% 4.00/4.21  thf('19', plain, (((sk_B_1) != (k1_xboole_0))),
% 4.00/4.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.21  thf('20', plain, (~ (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A)),
% 4.00/4.21      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 4.00/4.21  thf('21', plain, ((v1_xboole_0 @ sk_A)),
% 4.00/4.21      inference('clc', [status(thm)], ['15', '20'])).
% 4.00/4.21  thf(l13_xboole_0, axiom,
% 4.00/4.21    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.00/4.21  thf('22', plain,
% 4.00/4.21      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.00/4.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.00/4.21  thf('23', plain, (((sk_A) = (k1_xboole_0))),
% 4.00/4.21      inference('sup-', [status(thm)], ['21', '22'])).
% 4.00/4.21  thf('24', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ k1_xboole_0)),
% 4.00/4.21      inference('demod', [status(thm)], ['12', '23'])).
% 4.00/4.21  thf(l1_zfmisc_1, axiom,
% 4.00/4.21    (![A:$i,B:$i]:
% 4.00/4.21     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 4.00/4.21  thf('25', plain,
% 4.00/4.21      (![X46 : $i, X48 : $i]:
% 4.00/4.21         ((r1_tarski @ (k1_tarski @ X46) @ X48) | ~ (r2_hidden @ X46 @ X48))),
% 4.00/4.21      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 4.00/4.21  thf('26', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ k1_xboole_0)),
% 4.00/4.21      inference('sup-', [status(thm)], ['24', '25'])).
% 4.00/4.21  thf(t3_xboole_1, axiom,
% 4.00/4.21    (![A:$i]:
% 4.00/4.21     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.00/4.21  thf('27', plain,
% 4.00/4.21      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 4.00/4.21      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.00/4.21  thf('28', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 4.00/4.21      inference('sup-', [status(thm)], ['26', '27'])).
% 4.00/4.21  thf('29', plain,
% 4.00/4.21      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 4.00/4.21      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.00/4.21  thf('30', plain,
% 4.00/4.21      (![X19 : $i, X20 : $i]:
% 4.00/4.21         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 4.00/4.21      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.00/4.21  thf(l62_enumset1, axiom,
% 4.00/4.21    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.00/4.21     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 4.00/4.21       ( k2_xboole_0 @
% 4.00/4.21         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 4.00/4.21  thf('31', plain,
% 4.00/4.21      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 4.00/4.21         ((k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 4.00/4.21           = (k2_xboole_0 @ (k1_enumset1 @ X12 @ X13 @ X14) @ 
% 4.00/4.21              (k1_enumset1 @ X15 @ X16 @ X17)))),
% 4.00/4.21      inference('cnf', [status(esa)], [l62_enumset1])).
% 4.00/4.21  thf('32', plain,
% 4.00/4.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.21         ((k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 4.00/4.21           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 4.00/4.21              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 4.00/4.21      inference('sup+', [status(thm)], ['30', '31'])).
% 4.00/4.21  thf(t73_enumset1, axiom,
% 4.00/4.21    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 4.00/4.21     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 4.00/4.21       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 4.00/4.21  thf('33', plain,
% 4.00/4.21      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 4.00/4.21         ((k4_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 @ X32)
% 4.00/4.21           = (k3_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32))),
% 4.00/4.21      inference('cnf', [status(esa)], [t73_enumset1])).
% 4.00/4.21  thf('34', plain,
% 4.00/4.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.21         ((k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 4.00/4.21           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 4.00/4.21              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 4.00/4.21      inference('demod', [status(thm)], ['32', '33'])).
% 4.00/4.21  thf('35', plain,
% 4.00/4.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.00/4.21         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 4.00/4.21           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 4.00/4.21      inference('sup+', [status(thm)], ['29', '34'])).
% 4.00/4.21  thf(t72_enumset1, axiom,
% 4.00/4.21    (![A:$i,B:$i,C:$i,D:$i]:
% 4.00/4.21     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 4.00/4.21  thf('36', plain,
% 4.00/4.21      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 4.00/4.21         ((k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27)
% 4.00/4.21           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 4.00/4.21      inference('cnf', [status(esa)], [t72_enumset1])).
% 4.00/4.21  thf('37', plain,
% 4.00/4.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.00/4.21         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 4.00/4.21           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 4.00/4.21      inference('demod', [status(thm)], ['35', '36'])).
% 4.00/4.21  thf('38', plain,
% 4.00/4.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.21         ((k2_enumset1 @ (sk_B @ sk_B_1) @ X2 @ X1 @ X0)
% 4.00/4.21           = (k2_xboole_0 @ k1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 4.00/4.21      inference('sup+', [status(thm)], ['28', '37'])).
% 4.00/4.21  thf('39', plain,
% 4.00/4.21      (![X0 : $i, X1 : $i]:
% 4.00/4.21         ((k2_enumset1 @ (sk_B @ sk_B_1) @ X1 @ X1 @ X0)
% 4.00/4.21           = (k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0)))),
% 4.00/4.21      inference('sup+', [status(thm)], ['5', '38'])).
% 4.00/4.21  thf('40', plain,
% 4.00/4.21      (((k1_tarski @ (sk_B @ sk_B_1))
% 4.00/4.21         = (k2_xboole_0 @ k1_xboole_0 @ 
% 4.00/4.21            (k2_tarski @ (sk_B @ sk_B_1) @ (sk_B @ sk_B_1))))),
% 4.00/4.21      inference('sup+', [status(thm)], ['4', '39'])).
% 4.00/4.21  thf('41', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 4.00/4.21      inference('sup-', [status(thm)], ['26', '27'])).
% 4.00/4.21  thf('42', plain,
% 4.00/4.21      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 4.00/4.21      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.00/4.21  thf('43', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 4.00/4.21      inference('sup-', [status(thm)], ['26', '27'])).
% 4.00/4.21  thf(t92_xboole_1, axiom,
% 4.00/4.21    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 4.00/4.21  thf('44', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 4.00/4.21      inference('cnf', [status(esa)], [t92_xboole_1])).
% 4.00/4.21  thf('45', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 4.00/4.21      inference('cnf', [status(esa)], [t92_xboole_1])).
% 4.00/4.21  thf(t91_xboole_1, axiom,
% 4.00/4.21    (![A:$i,B:$i,C:$i]:
% 4.00/4.21     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 4.00/4.21       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 4.00/4.21  thf('46', plain,
% 4.00/4.21      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.00/4.21         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 4.00/4.21           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 4.00/4.21      inference('cnf', [status(esa)], [t91_xboole_1])).
% 4.00/4.21  thf('47', plain,
% 4.00/4.21      (![X0 : $i, X1 : $i]:
% 4.00/4.21         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 4.00/4.21           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.00/4.21      inference('sup+', [status(thm)], ['45', '46'])).
% 4.00/4.21  thf('48', plain,
% 4.00/4.21      (![X0 : $i]:
% 4.00/4.21         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 4.00/4.21      inference('sup+', [status(thm)], ['44', '47'])).
% 4.00/4.21  thf(t5_boole, axiom,
% 4.00/4.21    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.00/4.21  thf('49', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 4.00/4.21      inference('cnf', [status(esa)], [t5_boole])).
% 4.00/4.21  thf('50', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.00/4.21      inference('demod', [status(thm)], ['48', '49'])).
% 4.00/4.21  thf(t95_xboole_1, axiom,
% 4.00/4.21    (![A:$i,B:$i]:
% 4.00/4.21     ( ( k3_xboole_0 @ A @ B ) =
% 4.00/4.21       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 4.00/4.21  thf('51', plain,
% 4.00/4.21      (![X10 : $i, X11 : $i]:
% 4.00/4.21         ((k3_xboole_0 @ X10 @ X11)
% 4.00/4.21           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 4.00/4.21              (k2_xboole_0 @ X10 @ X11)))),
% 4.00/4.21      inference('cnf', [status(esa)], [t95_xboole_1])).
% 4.00/4.21  thf('52', plain,
% 4.00/4.21      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.00/4.21         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 4.00/4.21           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 4.00/4.21      inference('cnf', [status(esa)], [t91_xboole_1])).
% 4.00/4.21  thf('53', plain,
% 4.00/4.21      (![X10 : $i, X11 : $i]:
% 4.00/4.21         ((k3_xboole_0 @ X10 @ X11)
% 4.00/4.21           = (k5_xboole_0 @ X10 @ 
% 4.00/4.21              (k5_xboole_0 @ X11 @ (k2_xboole_0 @ X10 @ X11))))),
% 4.00/4.21      inference('demod', [status(thm)], ['51', '52'])).
% 4.00/4.21  thf('54', plain,
% 4.00/4.21      (![X0 : $i]:
% 4.00/4.21         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 4.00/4.21           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 4.00/4.21      inference('sup+', [status(thm)], ['50', '53'])).
% 4.00/4.21  thf('55', plain,
% 4.00/4.21      (![X0 : $i, X1 : $i]:
% 4.00/4.21         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 4.00/4.21           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.00/4.21      inference('sup+', [status(thm)], ['45', '46'])).
% 4.00/4.21  thf('56', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.00/4.21      inference('demod', [status(thm)], ['48', '49'])).
% 4.00/4.21  thf('57', plain,
% 4.00/4.21      (![X0 : $i, X1 : $i]:
% 4.00/4.21         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.00/4.21      inference('demod', [status(thm)], ['55', '56'])).
% 4.00/4.21  thf('58', plain,
% 4.00/4.21      (![X0 : $i]:
% 4.00/4.21         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 4.00/4.21           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 4.00/4.21      inference('sup+', [status(thm)], ['54', '57'])).
% 4.00/4.21  thf(t100_xboole_1, axiom,
% 4.00/4.21    (![A:$i,B:$i]:
% 4.00/4.21     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.00/4.21  thf('59', plain,
% 4.00/4.21      (![X2 : $i, X3 : $i]:
% 4.00/4.21         ((k4_xboole_0 @ X2 @ X3)
% 4.00/4.21           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 4.00/4.21      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.00/4.21  thf('60', plain,
% 4.00/4.21      (![X0 : $i]:
% 4.00/4.21         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 4.00/4.21      inference('demod', [status(thm)], ['58', '59'])).
% 4.00/4.21  thf('61', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.00/4.21      inference('demod', [status(thm)], ['48', '49'])).
% 4.00/4.21  thf('62', plain,
% 4.00/4.21      (![X2 : $i, X3 : $i]:
% 4.00/4.21         ((k4_xboole_0 @ X2 @ X3)
% 4.00/4.21           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 4.00/4.21      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.00/4.21  thf('63', plain,
% 4.00/4.21      (![X0 : $i]:
% 4.00/4.21         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 4.00/4.21      inference('sup+', [status(thm)], ['61', '62'])).
% 4.00/4.21  thf('64', plain,
% 4.00/4.21      (((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 4.00/4.21      inference('demod', [status(thm)], ['40', '41', '42', '43', '60', '63'])).
% 4.00/4.21  thf('65', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 4.00/4.21      inference('sup-', [status(thm)], ['26', '27'])).
% 4.00/4.21  thf(t20_zfmisc_1, axiom,
% 4.00/4.21    (![A:$i,B:$i]:
% 4.00/4.21     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 4.00/4.21         ( k1_tarski @ A ) ) <=>
% 4.00/4.21       ( ( A ) != ( B ) ) ))).
% 4.00/4.21  thf('66', plain,
% 4.00/4.21      (![X51 : $i, X52 : $i]:
% 4.00/4.21         (((X52) != (X51))
% 4.00/4.21          | ((k4_xboole_0 @ (k1_tarski @ X52) @ (k1_tarski @ X51))
% 4.00/4.21              != (k1_tarski @ X52)))),
% 4.00/4.21      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 4.00/4.21  thf('67', plain,
% 4.00/4.21      (![X51 : $i]:
% 4.00/4.21         ((k4_xboole_0 @ (k1_tarski @ X51) @ (k1_tarski @ X51))
% 4.00/4.21           != (k1_tarski @ X51))),
% 4.00/4.21      inference('simplify', [status(thm)], ['66'])).
% 4.00/4.21  thf('68', plain,
% 4.00/4.21      (((k4_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)) @ k1_xboole_0)
% 4.00/4.21         != (k1_tarski @ (sk_B @ sk_B_1)))),
% 4.00/4.21      inference('sup-', [status(thm)], ['65', '67'])).
% 4.00/4.21  thf('69', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 4.00/4.21      inference('sup-', [status(thm)], ['26', '27'])).
% 4.00/4.21  thf('70', plain,
% 4.00/4.21      (![X0 : $i]:
% 4.00/4.21         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 4.00/4.21      inference('sup+', [status(thm)], ['61', '62'])).
% 4.00/4.21  thf('71', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 4.00/4.21      inference('sup-', [status(thm)], ['26', '27'])).
% 4.00/4.21  thf('72', plain,
% 4.00/4.21      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 4.00/4.21      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 4.00/4.21  thf('73', plain, ($false),
% 4.00/4.21      inference('simplify_reflect-', [status(thm)], ['64', '72'])).
% 4.00/4.21  
% 4.00/4.21  % SZS output end Refutation
% 4.00/4.21  
% 4.06/4.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
