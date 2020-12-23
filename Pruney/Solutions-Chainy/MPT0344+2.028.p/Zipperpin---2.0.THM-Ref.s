%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qMUrjppFt9

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:42 EST 2020

% Result     : Theorem 35.75s
% Output     : Refutation 35.75s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 364 expanded)
%              Number of leaves         :   40 ( 126 expanded)
%              Depth                    :   15
%              Number of atoms          :  806 (2774 expanded)
%              Number of equality atoms :   80 ( 245 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
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

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( r2_hidden @ X58 @ X59 )
      | ( r2_hidden @ X58 @ X60 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X55 @ X56 )
      | ( m1_subset_1 @ X55 @ X56 )
      | ( v1_xboole_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('11',plain,(
    ! [X61: $i] :
      ( ~ ( r2_hidden @ X61 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X61 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['9','14'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('17',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['6','17'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('19',plain,(
    ! [X47: $i,X49: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X47 ) @ X49 )
      | ~ ( r2_hidden @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('20',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('22',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('27',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('28',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k5_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k2_tarski @ X12 @ X13 ) @ ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t57_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('33',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k5_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 )
      = ( k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('39',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','46'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ X3 ) @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','50'])).

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('53',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('54',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','56'])).

thf('58',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['22','57'])).

thf('59',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf('64',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('65',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53 != X52 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X53 ) @ ( k1_tarski @ X52 ) )
       != ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('66',plain,(
    ! [X52: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X52 ) @ ( k1_tarski @ X52 ) )
     != ( k1_tarski @ X52 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
 != ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('69',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('70',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('72',plain,(
    ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['63','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qMUrjppFt9
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 35.75/35.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 35.75/35.92  % Solved by: fo/fo7.sh
% 35.75/35.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 35.75/35.92  % done 23379 iterations in 35.489s
% 35.75/35.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 35.75/35.92  % SZS output start Refutation
% 35.75/35.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 35.75/35.92  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 35.75/35.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 35.75/35.92  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 35.75/35.92  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 35.75/35.92  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 35.75/35.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 35.75/35.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 35.75/35.92  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 35.75/35.92  thf(sk_B_type, type, sk_B: $i > $i).
% 35.75/35.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 35.75/35.92  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 35.75/35.92  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 35.75/35.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 35.75/35.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 35.75/35.92  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 35.75/35.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 35.75/35.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 35.75/35.92  thf(sk_A_type, type, sk_A: $i).
% 35.75/35.92  thf(sk_B_1_type, type, sk_B_1: $i).
% 35.75/35.92  thf(t7_xboole_0, axiom,
% 35.75/35.92    (![A:$i]:
% 35.75/35.92     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 35.75/35.92          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 35.75/35.92  thf('0', plain,
% 35.75/35.92      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 35.75/35.92      inference('cnf', [status(esa)], [t7_xboole_0])).
% 35.75/35.92  thf(t10_subset_1, conjecture,
% 35.75/35.92    (![A:$i,B:$i]:
% 35.75/35.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 35.75/35.92       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 35.75/35.92            ( ![C:$i]:
% 35.75/35.92              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 35.75/35.92  thf(zf_stmt_0, negated_conjecture,
% 35.75/35.92    (~( ![A:$i,B:$i]:
% 35.75/35.92        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 35.75/35.92          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 35.75/35.92               ( ![C:$i]:
% 35.75/35.92                 ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ) )),
% 35.75/35.92    inference('cnf.neg', [status(esa)], [t10_subset_1])).
% 35.75/35.92  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 35.75/35.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/35.92  thf(l3_subset_1, axiom,
% 35.75/35.92    (![A:$i,B:$i]:
% 35.75/35.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 35.75/35.92       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 35.75/35.92  thf('2', plain,
% 35.75/35.92      (![X58 : $i, X59 : $i, X60 : $i]:
% 35.75/35.92         (~ (r2_hidden @ X58 @ X59)
% 35.75/35.92          | (r2_hidden @ X58 @ X60)
% 35.75/35.92          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ X60)))),
% 35.75/35.92      inference('cnf', [status(esa)], [l3_subset_1])).
% 35.75/35.92  thf('3', plain,
% 35.75/35.92      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 35.75/35.92      inference('sup-', [status(thm)], ['1', '2'])).
% 35.75/35.92  thf('4', plain,
% 35.75/35.92      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 35.75/35.92      inference('sup-', [status(thm)], ['0', '3'])).
% 35.75/35.92  thf('5', plain, (((sk_B_1) != (k1_xboole_0))),
% 35.75/35.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/35.92  thf('6', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)),
% 35.75/35.92      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 35.75/35.92  thf('7', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)),
% 35.75/35.92      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 35.75/35.92  thf(d2_subset_1, axiom,
% 35.75/35.92    (![A:$i,B:$i]:
% 35.75/35.92     ( ( ( v1_xboole_0 @ A ) =>
% 35.75/35.92         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 35.75/35.92       ( ( ~( v1_xboole_0 @ A ) ) =>
% 35.75/35.92         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 35.75/35.92  thf('8', plain,
% 35.75/35.92      (![X55 : $i, X56 : $i]:
% 35.75/35.92         (~ (r2_hidden @ X55 @ X56)
% 35.75/35.92          | (m1_subset_1 @ X55 @ X56)
% 35.75/35.92          | (v1_xboole_0 @ X56))),
% 35.75/35.92      inference('cnf', [status(esa)], [d2_subset_1])).
% 35.75/35.92  thf('9', plain,
% 35.75/35.92      (((v1_xboole_0 @ sk_A) | (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A))),
% 35.75/35.92      inference('sup-', [status(thm)], ['7', '8'])).
% 35.75/35.92  thf('10', plain,
% 35.75/35.92      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 35.75/35.92      inference('cnf', [status(esa)], [t7_xboole_0])).
% 35.75/35.92  thf('11', plain,
% 35.75/35.92      (![X61 : $i]:
% 35.75/35.92         (~ (r2_hidden @ X61 @ sk_B_1) | ~ (m1_subset_1 @ X61 @ sk_A))),
% 35.75/35.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/35.92  thf('12', plain,
% 35.75/35.92      ((((sk_B_1) = (k1_xboole_0)) | ~ (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A))),
% 35.75/35.92      inference('sup-', [status(thm)], ['10', '11'])).
% 35.75/35.92  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 35.75/35.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/35.92  thf('14', plain, (~ (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A)),
% 35.75/35.92      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 35.75/35.92  thf('15', plain, ((v1_xboole_0 @ sk_A)),
% 35.75/35.92      inference('clc', [status(thm)], ['9', '14'])).
% 35.75/35.92  thf(l13_xboole_0, axiom,
% 35.75/35.92    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 35.75/35.92  thf('16', plain,
% 35.75/35.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 35.75/35.92      inference('cnf', [status(esa)], [l13_xboole_0])).
% 35.75/35.92  thf('17', plain, (((sk_A) = (k1_xboole_0))),
% 35.75/35.92      inference('sup-', [status(thm)], ['15', '16'])).
% 35.75/35.92  thf('18', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ k1_xboole_0)),
% 35.75/35.92      inference('demod', [status(thm)], ['6', '17'])).
% 35.75/35.92  thf(l1_zfmisc_1, axiom,
% 35.75/35.92    (![A:$i,B:$i]:
% 35.75/35.92     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 35.75/35.92  thf('19', plain,
% 35.75/35.92      (![X47 : $i, X49 : $i]:
% 35.75/35.92         ((r1_tarski @ (k1_tarski @ X47) @ X49) | ~ (r2_hidden @ X47 @ X49))),
% 35.75/35.92      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 35.75/35.92  thf('20', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ k1_xboole_0)),
% 35.75/35.92      inference('sup-', [status(thm)], ['18', '19'])).
% 35.75/35.92  thf(t3_xboole_1, axiom,
% 35.75/35.92    (![A:$i]:
% 35.75/35.92     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 35.75/35.92  thf('21', plain,
% 35.75/35.92      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 35.75/35.92      inference('cnf', [status(esa)], [t3_xboole_1])).
% 35.75/35.92  thf('22', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 35.75/35.92      inference('sup-', [status(thm)], ['20', '21'])).
% 35.75/35.92  thf(t70_enumset1, axiom,
% 35.75/35.92    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 35.75/35.92  thf('23', plain,
% 35.75/35.92      (![X20 : $i, X21 : $i]:
% 35.75/35.92         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 35.75/35.92      inference('cnf', [status(esa)], [t70_enumset1])).
% 35.75/35.92  thf(t69_enumset1, axiom,
% 35.75/35.92    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 35.75/35.92  thf('24', plain,
% 35.75/35.92      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 35.75/35.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 35.75/35.92  thf('25', plain,
% 35.75/35.92      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 35.75/35.92      inference('sup+', [status(thm)], ['23', '24'])).
% 35.75/35.92  thf(t71_enumset1, axiom,
% 35.75/35.92    (![A:$i,B:$i,C:$i]:
% 35.75/35.92     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 35.75/35.92  thf('26', plain,
% 35.75/35.92      (![X22 : $i, X23 : $i, X24 : $i]:
% 35.75/35.92         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 35.75/35.92           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 35.75/35.92      inference('cnf', [status(esa)], [t71_enumset1])).
% 35.75/35.92  thf(t73_enumset1, axiom,
% 35.75/35.92    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 35.75/35.92     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 35.75/35.92       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 35.75/35.92  thf('27', plain,
% 35.75/35.92      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 35.75/35.92         ((k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33)
% 35.75/35.93           = (k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 35.75/35.93      inference('cnf', [status(esa)], [t73_enumset1])).
% 35.75/35.93  thf(t72_enumset1, axiom,
% 35.75/35.93    (![A:$i,B:$i,C:$i,D:$i]:
% 35.75/35.93     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 35.75/35.93  thf('28', plain,
% 35.75/35.93      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 35.75/35.93         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 35.75/35.93           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 35.75/35.93      inference('cnf', [status(esa)], [t72_enumset1])).
% 35.75/35.93  thf('29', plain,
% 35.75/35.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 35.75/35.93         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 35.75/35.93           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 35.75/35.93      inference('sup+', [status(thm)], ['27', '28'])).
% 35.75/35.93  thf('30', plain,
% 35.75/35.93      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 35.75/35.93      inference('cnf', [status(esa)], [t69_enumset1])).
% 35.75/35.93  thf(t57_enumset1, axiom,
% 35.75/35.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 35.75/35.93     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 35.75/35.93       ( k2_xboole_0 @
% 35.75/35.93         ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ))).
% 35.75/35.93  thf('31', plain,
% 35.75/35.93      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 35.75/35.93         ((k5_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18)
% 35.75/35.93           = (k2_xboole_0 @ (k2_tarski @ X12 @ X13) @ 
% 35.75/35.93              (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)))),
% 35.75/35.93      inference('cnf', [status(esa)], [t57_enumset1])).
% 35.75/35.93  thf('32', plain,
% 35.75/35.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 35.75/35.93         ((k5_enumset1 @ X0 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1)
% 35.75/35.93           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 35.75/35.93              (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1)))),
% 35.75/35.93      inference('sup+', [status(thm)], ['30', '31'])).
% 35.75/35.93  thf(t74_enumset1, axiom,
% 35.75/35.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 35.75/35.93     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 35.75/35.93       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 35.75/35.93  thf('33', plain,
% 35.75/35.93      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 35.75/35.93         ((k5_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)
% 35.75/35.93           = (k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39))),
% 35.75/35.93      inference('cnf', [status(esa)], [t74_enumset1])).
% 35.75/35.93  thf('34', plain,
% 35.75/35.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 35.75/35.93         ((k4_enumset1 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1)
% 35.75/35.93           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 35.75/35.93              (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1)))),
% 35.75/35.93      inference('demod', [status(thm)], ['32', '33'])).
% 35.75/35.93  thf(t95_xboole_1, axiom,
% 35.75/35.93    (![A:$i,B:$i]:
% 35.75/35.93     ( ( k3_xboole_0 @ A @ B ) =
% 35.75/35.93       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 35.75/35.93  thf('35', plain,
% 35.75/35.93      (![X10 : $i, X11 : $i]:
% 35.75/35.93         ((k3_xboole_0 @ X10 @ X11)
% 35.75/35.93           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 35.75/35.93              (k2_xboole_0 @ X10 @ X11)))),
% 35.75/35.93      inference('cnf', [status(esa)], [t95_xboole_1])).
% 35.75/35.93  thf(t91_xboole_1, axiom,
% 35.75/35.93    (![A:$i,B:$i,C:$i]:
% 35.75/35.93     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 35.75/35.93       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 35.75/35.93  thf('36', plain,
% 35.75/35.93      (![X6 : $i, X7 : $i, X8 : $i]:
% 35.75/35.93         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 35.75/35.93           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 35.75/35.93      inference('cnf', [status(esa)], [t91_xboole_1])).
% 35.75/35.93  thf('37', plain,
% 35.75/35.93      (![X10 : $i, X11 : $i]:
% 35.75/35.93         ((k3_xboole_0 @ X10 @ X11)
% 35.75/35.93           = (k5_xboole_0 @ X10 @ 
% 35.75/35.93              (k5_xboole_0 @ X11 @ (k2_xboole_0 @ X10 @ X11))))),
% 35.75/35.93      inference('demod', [status(thm)], ['35', '36'])).
% 35.75/35.93  thf(t92_xboole_1, axiom,
% 35.75/35.93    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 35.75/35.93  thf('38', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 35.75/35.93      inference('cnf', [status(esa)], [t92_xboole_1])).
% 35.75/35.93  thf('39', plain,
% 35.75/35.93      (![X6 : $i, X7 : $i, X8 : $i]:
% 35.75/35.93         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 35.75/35.93           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 35.75/35.93      inference('cnf', [status(esa)], [t91_xboole_1])).
% 35.75/35.93  thf('40', plain,
% 35.75/35.93      (![X0 : $i, X1 : $i]:
% 35.75/35.93         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 35.75/35.93           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 35.75/35.93      inference('sup+', [status(thm)], ['38', '39'])).
% 35.75/35.93  thf('41', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 35.75/35.93      inference('cnf', [status(esa)], [t92_xboole_1])).
% 35.75/35.93  thf('42', plain,
% 35.75/35.93      (![X0 : $i, X1 : $i]:
% 35.75/35.93         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 35.75/35.93           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 35.75/35.93      inference('sup+', [status(thm)], ['38', '39'])).
% 35.75/35.93  thf('43', plain,
% 35.75/35.93      (![X0 : $i]:
% 35.75/35.93         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 35.75/35.93      inference('sup+', [status(thm)], ['41', '42'])).
% 35.75/35.93  thf(t5_boole, axiom,
% 35.75/35.93    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 35.75/35.93  thf('44', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 35.75/35.93      inference('cnf', [status(esa)], [t5_boole])).
% 35.75/35.93  thf('45', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 35.75/35.93      inference('demod', [status(thm)], ['43', '44'])).
% 35.75/35.93  thf('46', plain,
% 35.75/35.93      (![X0 : $i, X1 : $i]:
% 35.75/35.93         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 35.75/35.93      inference('demod', [status(thm)], ['40', '45'])).
% 35.75/35.93  thf('47', plain,
% 35.75/35.93      (![X0 : $i, X1 : $i]:
% 35.75/35.93         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 35.75/35.93           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 35.75/35.93      inference('sup+', [status(thm)], ['37', '46'])).
% 35.75/35.93  thf(t100_xboole_1, axiom,
% 35.75/35.93    (![A:$i,B:$i]:
% 35.75/35.93     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 35.75/35.93  thf('48', plain,
% 35.75/35.93      (![X2 : $i, X3 : $i]:
% 35.75/35.93         ((k4_xboole_0 @ X2 @ X3)
% 35.75/35.93           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 35.75/35.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 35.75/35.93  thf('49', plain,
% 35.75/35.93      (![X0 : $i, X1 : $i]:
% 35.75/35.93         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 35.75/35.93           = (k4_xboole_0 @ X1 @ X0))),
% 35.75/35.93      inference('demod', [status(thm)], ['47', '48'])).
% 35.75/35.93  thf('50', plain,
% 35.75/35.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 35.75/35.93         ((k5_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 35.75/35.93           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 35.75/35.93           = (k4_xboole_0 @ (k1_tarski @ X5) @ 
% 35.75/35.93              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 35.75/35.93      inference('sup+', [status(thm)], ['34', '49'])).
% 35.75/35.93  thf('51', plain,
% 35.75/35.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 35.75/35.93         ((k5_xboole_0 @ (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0) @ 
% 35.75/35.93           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 35.75/35.93           = (k4_xboole_0 @ (k1_tarski @ X3) @ 
% 35.75/35.93              (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)))),
% 35.75/35.93      inference('sup+', [status(thm)], ['29', '50'])).
% 35.75/35.93  thf('52', plain,
% 35.75/35.93      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 35.75/35.93         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 35.75/35.93           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 35.75/35.93      inference('cnf', [status(esa)], [t72_enumset1])).
% 35.75/35.93  thf('53', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 35.75/35.93      inference('cnf', [status(esa)], [t92_xboole_1])).
% 35.75/35.93  thf('54', plain,
% 35.75/35.93      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 35.75/35.93         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 35.75/35.93           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 35.75/35.93      inference('cnf', [status(esa)], [t72_enumset1])).
% 35.75/35.93  thf('55', plain,
% 35.75/35.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 35.75/35.93         ((k1_xboole_0)
% 35.75/35.93           = (k4_xboole_0 @ (k1_tarski @ X3) @ 
% 35.75/35.93              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 35.75/35.93      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 35.75/35.93  thf('56', plain,
% 35.75/35.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.75/35.93         ((k1_xboole_0)
% 35.75/35.93           = (k4_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 35.75/35.93      inference('sup+', [status(thm)], ['26', '55'])).
% 35.75/35.93  thf('57', plain,
% 35.75/35.93      (![X0 : $i]:
% 35.75/35.93         ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 35.75/35.93      inference('sup+', [status(thm)], ['25', '56'])).
% 35.75/35.93  thf('58', plain,
% 35.75/35.93      (((k1_xboole_0)
% 35.75/35.93         = (k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1))))),
% 35.75/35.93      inference('sup+', [status(thm)], ['22', '57'])).
% 35.75/35.93  thf('59', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 35.75/35.93      inference('sup-', [status(thm)], ['20', '21'])).
% 35.75/35.93  thf('60', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 35.75/35.93      inference('demod', [status(thm)], ['43', '44'])).
% 35.75/35.93  thf('61', plain,
% 35.75/35.93      (![X2 : $i, X3 : $i]:
% 35.75/35.93         ((k4_xboole_0 @ X2 @ X3)
% 35.75/35.93           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 35.75/35.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 35.75/35.93  thf('62', plain,
% 35.75/35.93      (![X0 : $i]:
% 35.75/35.93         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 35.75/35.93      inference('sup+', [status(thm)], ['60', '61'])).
% 35.75/35.93  thf('63', plain,
% 35.75/35.93      (((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 35.75/35.93      inference('demod', [status(thm)], ['58', '59', '62'])).
% 35.75/35.93  thf('64', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 35.75/35.93      inference('sup-', [status(thm)], ['20', '21'])).
% 35.75/35.93  thf(t20_zfmisc_1, axiom,
% 35.75/35.93    (![A:$i,B:$i]:
% 35.75/35.93     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 35.75/35.93         ( k1_tarski @ A ) ) <=>
% 35.75/35.93       ( ( A ) != ( B ) ) ))).
% 35.75/35.93  thf('65', plain,
% 35.75/35.93      (![X52 : $i, X53 : $i]:
% 35.75/35.93         (((X53) != (X52))
% 35.75/35.93          | ((k4_xboole_0 @ (k1_tarski @ X53) @ (k1_tarski @ X52))
% 35.75/35.93              != (k1_tarski @ X53)))),
% 35.75/35.93      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 35.75/35.93  thf('66', plain,
% 35.75/35.93      (![X52 : $i]:
% 35.75/35.93         ((k4_xboole_0 @ (k1_tarski @ X52) @ (k1_tarski @ X52))
% 35.75/35.93           != (k1_tarski @ X52))),
% 35.75/35.93      inference('simplify', [status(thm)], ['65'])).
% 35.75/35.93  thf('67', plain,
% 35.75/35.93      (((k4_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)) @ k1_xboole_0)
% 35.75/35.93         != (k1_tarski @ (sk_B @ sk_B_1)))),
% 35.75/35.93      inference('sup-', [status(thm)], ['64', '66'])).
% 35.75/35.93  thf('68', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 35.75/35.93      inference('sup-', [status(thm)], ['20', '21'])).
% 35.75/35.93  thf('69', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 35.75/35.93      inference('sup-', [status(thm)], ['20', '21'])).
% 35.75/35.93  thf('70', plain,
% 35.75/35.93      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 35.75/35.93      inference('demod', [status(thm)], ['67', '68', '69'])).
% 35.75/35.93  thf('71', plain,
% 35.75/35.93      (![X0 : $i]:
% 35.75/35.93         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 35.75/35.93      inference('sup+', [status(thm)], ['60', '61'])).
% 35.75/35.93  thf('72', plain,
% 35.75/35.93      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 35.75/35.93      inference('demod', [status(thm)], ['70', '71'])).
% 35.75/35.93  thf('73', plain, ($false),
% 35.75/35.93      inference('simplify_reflect-', [status(thm)], ['63', '72'])).
% 35.75/35.93  
% 35.75/35.93  % SZS output end Refutation
% 35.75/35.93  
% 35.75/35.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
