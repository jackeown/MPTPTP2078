%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x0b4pdav4Q

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:56 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 377 expanded)
%              Number of leaves         :   43 ( 133 expanded)
%              Depth                    :   18
%              Number of atoms          :  976 (4488 expanded)
%              Number of equality atoms :  114 ( 309 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k7_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k9_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X10
        = ( k1_enumset1 @ X7 @ X8 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X7 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X8 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X7 @ X8 ) )
      | ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10
        = ( k1_tarski @ X8 ) )
      | ( X10
        = ( k1_tarski @ X7 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X3
        = ( k1_tarski @ X2 ) )
      | ( X3
        = ( k1_tarski @ X1 ) )
      | ( X3
        = ( k1_tarski @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X1 ) )
      | ( X3
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X0 ) )
      | ( X3
        = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','25'])).

thf('27',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k1_relat_1 @ X24 )
       != ( k1_tarski @ X23 ) )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_tarski @ ( k1_funct_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['31'])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('42',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X14 @ X15 ) @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) @ X0 ) @ ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('49',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('50',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('52',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','55'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('57',plain,(
    ! [X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('58',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('62',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('66',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('67',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('68',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('70',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['66','67'])).

thf('73',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('77',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['66','67'])).

thf('78',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['4','61','78','79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x0b4pdav4Q
% 0.16/0.38  % Computer   : n008.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 14:53:45 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.47/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.69  % Solved by: fo/fo7.sh
% 0.47/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.69  % done 500 iterations in 0.202s
% 0.47/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.69  % SZS output start Refutation
% 0.47/0.69  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.47/0.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.69  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.69  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.69  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.69  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.69  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.69  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.47/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.69  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.69  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.47/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.69  thf(t64_funct_2, conjecture,
% 0.47/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.69     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.47/0.69         ( m1_subset_1 @
% 0.47/0.69           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.47/0.69       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.47/0.69         ( r1_tarski @
% 0.47/0.69           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.47/0.69           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.47/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.69        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.47/0.69            ( m1_subset_1 @
% 0.47/0.69              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.47/0.69          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.47/0.69            ( r1_tarski @
% 0.47/0.69              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.47/0.69              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.47/0.69    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.47/0.69  thf('0', plain,
% 0.47/0.69      (~ (r1_tarski @ 
% 0.47/0.69          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.47/0.69          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('1', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(redefinition_k7_relset_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.69       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.47/0.69  thf('2', plain,
% 0.47/0.69      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.47/0.69         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.47/0.69          | ((k7_relset_1 @ X32 @ X33 @ X31 @ X34) = (k9_relat_1 @ X31 @ X34)))),
% 0.47/0.69      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.47/0.69  thf('3', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.47/0.69           = (k9_relat_1 @ sk_D @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.69  thf('4', plain,
% 0.47/0.69      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.47/0.69          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.47/0.69      inference('demod', [status(thm)], ['0', '3'])).
% 0.47/0.69  thf('5', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(cc2_relset_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.69       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.69  thf('6', plain,
% 0.47/0.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.69         ((v4_relat_1 @ X28 @ X29)
% 0.47/0.69          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.47/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.69  thf('7', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.47/0.69      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.69  thf(d18_relat_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( v1_relat_1 @ B ) =>
% 0.47/0.69       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.69  thf('8', plain,
% 0.47/0.69      (![X12 : $i, X13 : $i]:
% 0.47/0.69         (~ (v4_relat_1 @ X12 @ X13)
% 0.47/0.69          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.47/0.69          | ~ (v1_relat_1 @ X12))),
% 0.47/0.69      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.69  thf('9', plain,
% 0.47/0.69      ((~ (v1_relat_1 @ sk_D)
% 0.47/0.69        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.69  thf('10', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(cc1_relset_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.69       ( v1_relat_1 @ C ) ))).
% 0.47/0.69  thf('11', plain,
% 0.47/0.69      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.69         ((v1_relat_1 @ X25)
% 0.47/0.69          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.47/0.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.69  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.69  thf('13', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.47/0.69      inference('demod', [status(thm)], ['9', '12'])).
% 0.47/0.69  thf(t71_enumset1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.47/0.69  thf('14', plain,
% 0.47/0.69      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.69         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.47/0.69      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.47/0.69  thf(t70_enumset1, axiom,
% 0.47/0.69    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.47/0.69  thf('15', plain,
% 0.47/0.69      (![X2 : $i, X3 : $i]:
% 0.47/0.69         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.47/0.69      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.47/0.69  thf('16', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.47/0.69      inference('sup+', [status(thm)], ['14', '15'])).
% 0.47/0.69  thf(t69_enumset1, axiom,
% 0.47/0.69    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.47/0.69  thf('17', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.47/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.69  thf('18', plain,
% 0.47/0.69      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.47/0.69      inference('sup+', [status(thm)], ['16', '17'])).
% 0.47/0.69  thf('19', plain,
% 0.47/0.69      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.69         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.47/0.69      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.47/0.69  thf(t142_zfmisc_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.69     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.47/0.69       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.47/0.69            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.47/0.69            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.47/0.69            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.47/0.69            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.47/0.69            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.47/0.69  thf('20', plain,
% 0.47/0.69      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.69         (((X10) = (k1_enumset1 @ X7 @ X8 @ X9))
% 0.47/0.69          | ((X10) = (k2_tarski @ X7 @ X9))
% 0.47/0.69          | ((X10) = (k2_tarski @ X8 @ X9))
% 0.47/0.69          | ((X10) = (k2_tarski @ X7 @ X8))
% 0.47/0.69          | ((X10) = (k1_tarski @ X9))
% 0.47/0.69          | ((X10) = (k1_tarski @ X8))
% 0.47/0.69          | ((X10) = (k1_tarski @ X7))
% 0.47/0.69          | ((X10) = (k1_xboole_0))
% 0.47/0.69          | ~ (r1_tarski @ X10 @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.47/0.69  thf('21', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.69         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 0.47/0.69          | ((X3) = (k1_xboole_0))
% 0.47/0.69          | ((X3) = (k1_tarski @ X2))
% 0.47/0.69          | ((X3) = (k1_tarski @ X1))
% 0.47/0.69          | ((X3) = (k1_tarski @ X0))
% 0.47/0.69          | ((X3) = (k2_tarski @ X2 @ X1))
% 0.47/0.69          | ((X3) = (k2_tarski @ X1 @ X0))
% 0.47/0.69          | ((X3) = (k2_tarski @ X2 @ X0))
% 0.47/0.69          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.69  thf('22', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.47/0.69          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 0.47/0.69          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.47/0.69          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.47/0.69          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.47/0.69          | ((X1) = (k1_tarski @ X0))
% 0.47/0.69          | ((X1) = (k1_tarski @ X0))
% 0.47/0.69          | ((X1) = (k1_tarski @ X0))
% 0.47/0.69          | ((X1) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['18', '21'])).
% 0.47/0.69  thf('23', plain,
% 0.47/0.69      (![X2 : $i, X3 : $i]:
% 0.47/0.69         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.47/0.69      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.47/0.69  thf('24', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.47/0.69          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.47/0.69          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.47/0.69          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.47/0.69          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.47/0.69          | ((X1) = (k1_tarski @ X0))
% 0.47/0.69          | ((X1) = (k1_tarski @ X0))
% 0.47/0.69          | ((X1) = (k1_tarski @ X0))
% 0.47/0.69          | ((X1) = (k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.69  thf('25', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (((X1) = (k1_xboole_0))
% 0.47/0.69          | ((X1) = (k1_tarski @ X0))
% 0.47/0.69          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.47/0.69          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['24'])).
% 0.47/0.69  thf('26', plain,
% 0.47/0.69      ((((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A))
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['13', '25'])).
% 0.47/0.69  thf('27', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.47/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.69  thf('28', plain,
% 0.47/0.69      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['26', '27'])).
% 0.47/0.69  thf('29', plain,
% 0.47/0.69      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['28'])).
% 0.47/0.69  thf(t14_funct_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.69       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.47/0.69         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.47/0.69  thf('30', plain,
% 0.47/0.69      (![X23 : $i, X24 : $i]:
% 0.47/0.69         (((k1_relat_1 @ X24) != (k1_tarski @ X23))
% 0.47/0.69          | ((k2_relat_1 @ X24) = (k1_tarski @ (k1_funct_1 @ X24 @ X23)))
% 0.47/0.69          | ~ (v1_funct_1 @ X24)
% 0.47/0.69          | ~ (v1_relat_1 @ X24))),
% 0.47/0.69      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.47/0.69  thf('31', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.47/0.69          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.47/0.69          | ~ (v1_relat_1 @ X0)
% 0.47/0.69          | ~ (v1_funct_1 @ X0)
% 0.47/0.69          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.69  thf('32', plain,
% 0.47/0.69      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.47/0.69        | ~ (v1_funct_1 @ sk_D)
% 0.47/0.69        | ~ (v1_relat_1 @ sk_D)
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.47/0.69      inference('eq_res', [status(thm)], ['31'])).
% 0.47/0.69  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.69  thf('35', plain,
% 0.47/0.69      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.47/0.69  thf('36', plain,
% 0.47/0.69      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.47/0.69          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.47/0.69      inference('demod', [status(thm)], ['0', '3'])).
% 0.47/0.69  thf('37', plain,
% 0.47/0.69      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.69  thf('38', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.47/0.69      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.69  thf(t209_relat_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.47/0.69       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.47/0.69  thf('39', plain,
% 0.47/0.69      (![X18 : $i, X19 : $i]:
% 0.47/0.69         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.47/0.69          | ~ (v4_relat_1 @ X18 @ X19)
% 0.47/0.69          | ~ (v1_relat_1 @ X18))),
% 0.47/0.69      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.47/0.69  thf('40', plain,
% 0.47/0.69      ((~ (v1_relat_1 @ sk_D)
% 0.47/0.69        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['38', '39'])).
% 0.47/0.69  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.69  thf('42', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.47/0.69      inference('demod', [status(thm)], ['40', '41'])).
% 0.47/0.69  thf(t148_relat_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( v1_relat_1 @ B ) =>
% 0.47/0.69       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.47/0.69  thf('43', plain,
% 0.47/0.69      (![X16 : $i, X17 : $i]:
% 0.47/0.69         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.47/0.69          | ~ (v1_relat_1 @ X16))),
% 0.47/0.69      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.47/0.69  thf(t144_relat_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( v1_relat_1 @ B ) =>
% 0.47/0.69       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.47/0.69  thf('44', plain,
% 0.47/0.69      (![X14 : $i, X15 : $i]:
% 0.47/0.69         ((r1_tarski @ (k9_relat_1 @ X14 @ X15) @ (k2_relat_1 @ X14))
% 0.47/0.69          | ~ (v1_relat_1 @ X14))),
% 0.47/0.69      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.47/0.69  thf('45', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.69         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.47/0.69           (k9_relat_1 @ X1 @ X0))
% 0.47/0.69          | ~ (v1_relat_1 @ X1)
% 0.47/0.69          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.47/0.69      inference('sup+', [status(thm)], ['43', '44'])).
% 0.47/0.69  thf('46', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_relat_1 @ sk_D)
% 0.47/0.69          | ~ (v1_relat_1 @ sk_D)
% 0.47/0.69          | (r1_tarski @ 
% 0.47/0.69             (k9_relat_1 @ (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)) @ X0) @ 
% 0.47/0.69             (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['42', '45'])).
% 0.47/0.69  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.69  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.69  thf('49', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.47/0.69      inference('demod', [status(thm)], ['40', '41'])).
% 0.47/0.69  thf('50', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.47/0.69      inference('demod', [status(thm)], ['40', '41'])).
% 0.47/0.69  thf('51', plain,
% 0.47/0.69      (![X16 : $i, X17 : $i]:
% 0.47/0.69         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.47/0.69          | ~ (v1_relat_1 @ X16))),
% 0.47/0.69      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.47/0.69  thf('52', plain,
% 0.47/0.69      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))
% 0.47/0.69        | ~ (v1_relat_1 @ sk_D))),
% 0.47/0.69      inference('sup+', [status(thm)], ['50', '51'])).
% 0.47/0.69  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.69  thf('54', plain,
% 0.47/0.69      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.47/0.69      inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.69  thf('55', plain,
% 0.47/0.69      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 0.47/0.69      inference('demod', [status(thm)], ['46', '47', '48', '49', '54'])).
% 0.47/0.69  thf('56', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['37', '55'])).
% 0.47/0.69  thf(t64_relat_1, axiom,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( v1_relat_1 @ A ) =>
% 0.47/0.69       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.69           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.69         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.69  thf('57', plain,
% 0.47/0.69      (![X20 : $i]:
% 0.47/0.69         (((k1_relat_1 @ X20) != (k1_xboole_0))
% 0.47/0.69          | ((X20) = (k1_xboole_0))
% 0.47/0.69          | ~ (v1_relat_1 @ X20))),
% 0.47/0.69      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.47/0.69  thf('58', plain,
% 0.47/0.69      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.69        | ~ (v1_relat_1 @ sk_D)
% 0.47/0.69        | ((sk_D) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.69  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.69  thf('60', plain,
% 0.47/0.69      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['58', '59'])).
% 0.47/0.69  thf('61', plain, (((sk_D) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['60'])).
% 0.47/0.69  thf(t60_relat_1, axiom,
% 0.47/0.69    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.47/0.69     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.69  thf('62', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.69      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.69  thf('63', plain,
% 0.47/0.69      (![X12 : $i, X13 : $i]:
% 0.47/0.69         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.47/0.69          | (v4_relat_1 @ X12 @ X13)
% 0.47/0.69          | ~ (v1_relat_1 @ X12))),
% 0.47/0.69      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.69  thf('64', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.47/0.69          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.69          | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.69  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.69  thf('65', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.47/0.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.69  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.47/0.69  thf('66', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.69      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.47/0.69  thf(fc3_funct_1, axiom,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.47/0.69       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.47/0.69  thf('67', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.47/0.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.69  thf('68', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.69      inference('sup+', [status(thm)], ['66', '67'])).
% 0.47/0.69  thf('69', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.47/0.69      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.47/0.69  thf('70', plain,
% 0.47/0.69      (![X18 : $i, X19 : $i]:
% 0.47/0.69         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.47/0.69          | ~ (v4_relat_1 @ X18 @ X19)
% 0.47/0.69          | ~ (v1_relat_1 @ X18))),
% 0.47/0.69      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.47/0.69  thf('71', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.69          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['69', '70'])).
% 0.47/0.69  thf('72', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.69      inference('sup+', [status(thm)], ['66', '67'])).
% 0.47/0.69  thf('73', plain,
% 0.47/0.69      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 0.47/0.69      inference('demod', [status(thm)], ['71', '72'])).
% 0.47/0.69  thf('74', plain,
% 0.47/0.69      (![X16 : $i, X17 : $i]:
% 0.47/0.69         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.47/0.69          | ~ (v1_relat_1 @ X16))),
% 0.47/0.69      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.47/0.69  thf('75', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.69          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.47/0.69      inference('sup+', [status(thm)], ['73', '74'])).
% 0.47/0.69  thf('76', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.69      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.69  thf('77', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.69      inference('sup+', [status(thm)], ['66', '67'])).
% 0.47/0.69  thf('78', plain,
% 0.47/0.69      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.47/0.69      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.47/0.69  thf('79', plain, (((sk_D) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['60'])).
% 0.47/0.69  thf('80', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.47/0.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.69  thf('81', plain, ($false),
% 0.47/0.69      inference('demod', [status(thm)], ['4', '61', '78', '79', '80'])).
% 0.47/0.69  
% 0.47/0.69  % SZS output end Refutation
% 0.47/0.69  
% 0.47/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
