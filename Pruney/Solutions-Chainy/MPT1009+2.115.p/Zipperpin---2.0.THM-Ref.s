%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.f8l8pdywSW

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:05 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 447 expanded)
%              Number of leaves         :   39 ( 151 expanded)
%              Depth                    :   18
%              Number of atoms          :  947 (5396 expanded)
%              Number of equality atoms :   98 ( 437 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k7_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k9_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X26 @ X27 ) @ ( k2_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v4_relat_1 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

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

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X13
        = ( k1_enumset1 @ X10 @ X11 @ X12 ) )
      | ( X13
        = ( k2_tarski @ X10 @ X12 ) )
      | ( X13
        = ( k2_tarski @ X11 @ X12 ) )
      | ( X13
        = ( k2_tarski @ X10 @ X11 ) )
      | ( X13
        = ( k1_tarski @ X12 ) )
      | ( X13
        = ( k1_tarski @ X11 ) )
      | ( X13
        = ( k1_tarski @ X10 ) )
      | ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( ( k1_relat_1 @ X29 )
       != ( k1_tarski @ X28 ) )
      | ( ( k2_relat_1 @ X29 )
        = ( k1_tarski @ ( k1_funct_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
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
    inference(demod,[status(thm)],['13','14'])).

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

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X37: $i] :
      ( ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_D ) ) @ sk_D )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('48',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('49',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('51',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('53',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['46','48','49','50','51','52','53'])).

thf('55',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('56',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v5_relat_1 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('60',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v5_relat_1 @ X22 @ X23 )
      | ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('63',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('64',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X26 @ X27 ) @ ( k2_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['62','63'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['46','48','49','50','51','52','53'])).

thf('77',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['4','54','75','76','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.f8l8pdywSW
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.54/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.75  % Solved by: fo/fo7.sh
% 0.54/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.75  % done 506 iterations in 0.298s
% 0.54/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.75  % SZS output start Refutation
% 0.54/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.75  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.54/0.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.75  thf(sk_D_type, type, sk_D: $i).
% 0.54/0.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.75  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.54/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.75  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.54/0.75  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.54/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.75  thf(t64_funct_2, conjecture,
% 0.54/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.75     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.54/0.75         ( m1_subset_1 @
% 0.54/0.75           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.54/0.75       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.54/0.75         ( r1_tarski @
% 0.54/0.75           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.54/0.75           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.54/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.75    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.75        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.54/0.75            ( m1_subset_1 @
% 0.54/0.75              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.54/0.75          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.54/0.75            ( r1_tarski @
% 0.54/0.75              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.54/0.75              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.54/0.75    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.54/0.75  thf('0', plain,
% 0.54/0.75      (~ (r1_tarski @ 
% 0.54/0.75          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.54/0.75          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('1', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_D @ 
% 0.54/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(redefinition_k7_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.54/0.75  thf('2', plain,
% 0.54/0.75      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.54/0.75          | ((k7_relset_1 @ X34 @ X35 @ X33 @ X36) = (k9_relat_1 @ X33 @ X36)))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.54/0.75  thf('3', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.54/0.75           = (k9_relat_1 @ sk_D @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.75  thf('4', plain,
% 0.54/0.75      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.54/0.75          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['0', '3'])).
% 0.54/0.75  thf(t144_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ B ) =>
% 0.54/0.75       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.54/0.75  thf('5', plain,
% 0.54/0.75      (![X26 : $i, X27 : $i]:
% 0.54/0.75         ((r1_tarski @ (k9_relat_1 @ X26 @ X27) @ (k2_relat_1 @ X26))
% 0.54/0.75          | ~ (v1_relat_1 @ X26))),
% 0.54/0.75      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.54/0.75  thf('6', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_D @ 
% 0.54/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(cc2_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.75  thf('7', plain,
% 0.54/0.75      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.54/0.75         ((v4_relat_1 @ X30 @ X31)
% 0.54/0.75          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.75  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['6', '7'])).
% 0.54/0.75  thf(d18_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ B ) =>
% 0.54/0.75       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.75  thf('9', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i]:
% 0.54/0.75         (~ (v4_relat_1 @ X20 @ X21)
% 0.54/0.75          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.54/0.75          | ~ (v1_relat_1 @ X20))),
% 0.54/0.75      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.54/0.75  thf('10', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ sk_D)
% 0.54/0.75        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.75  thf('11', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_D @ 
% 0.54/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(cc2_relat_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ A ) =>
% 0.54/0.75       ( ![B:$i]:
% 0.54/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.54/0.75  thf('12', plain,
% 0.54/0.75      (![X18 : $i, X19 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.54/0.75          | (v1_relat_1 @ X18)
% 0.54/0.75          | ~ (v1_relat_1 @ X19))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.54/0.75  thf('13', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.54/0.75        | (v1_relat_1 @ sk_D))),
% 0.54/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.54/0.75  thf(fc6_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.54/0.75  thf('14', plain,
% 0.54/0.75      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 0.54/0.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.75  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.54/0.75      inference('demod', [status(thm)], ['13', '14'])).
% 0.54/0.75  thf('16', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['10', '15'])).
% 0.54/0.75  thf(t69_enumset1, axiom,
% 0.54/0.75    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.54/0.75  thf('17', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.54/0.75      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.75  thf(t70_enumset1, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.54/0.75  thf('18', plain,
% 0.54/0.75      (![X5 : $i, X6 : $i]:
% 0.54/0.75         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.54/0.75      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.54/0.75  thf(t142_zfmisc_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.75     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.54/0.75       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.54/0.75            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.54/0.75            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.54/0.75            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.54/0.75            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.54/0.75            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.54/0.75  thf('19', plain,
% 0.54/0.75      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.54/0.75         (((X13) = (k1_enumset1 @ X10 @ X11 @ X12))
% 0.54/0.75          | ((X13) = (k2_tarski @ X10 @ X12))
% 0.54/0.75          | ((X13) = (k2_tarski @ X11 @ X12))
% 0.54/0.75          | ((X13) = (k2_tarski @ X10 @ X11))
% 0.54/0.75          | ((X13) = (k1_tarski @ X12))
% 0.54/0.75          | ((X13) = (k1_tarski @ X11))
% 0.54/0.75          | ((X13) = (k1_tarski @ X10))
% 0.54/0.75          | ((X13) = (k1_xboole_0))
% 0.54/0.75          | ~ (r1_tarski @ X13 @ (k1_enumset1 @ X10 @ X11 @ X12)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.54/0.75  thf('20', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.54/0.75          | ((X2) = (k1_xboole_0))
% 0.54/0.75          | ((X2) = (k1_tarski @ X1))
% 0.54/0.75          | ((X2) = (k1_tarski @ X1))
% 0.54/0.75          | ((X2) = (k1_tarski @ X0))
% 0.54/0.75          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.54/0.75          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.54/0.75          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.54/0.75          | ((X2) = (k1_enumset1 @ X1 @ X1 @ X0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.75  thf('21', plain,
% 0.54/0.75      (![X5 : $i, X6 : $i]:
% 0.54/0.75         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.54/0.75      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.54/0.75  thf('22', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.54/0.75          | ((X2) = (k1_xboole_0))
% 0.54/0.75          | ((X2) = (k1_tarski @ X1))
% 0.54/0.75          | ((X2) = (k1_tarski @ X1))
% 0.54/0.75          | ((X2) = (k1_tarski @ X0))
% 0.54/0.75          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.54/0.75          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.54/0.75          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.54/0.75          | ((X2) = (k2_tarski @ X1 @ X0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.54/0.75  thf('23', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         (((X2) = (k2_tarski @ X1 @ X0))
% 0.54/0.75          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.54/0.75          | ((X2) = (k1_tarski @ X0))
% 0.54/0.75          | ((X2) = (k1_tarski @ X1))
% 0.54/0.75          | ((X2) = (k1_xboole_0))
% 0.54/0.75          | ~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['22'])).
% 0.54/0.75  thf('24', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.54/0.75          | ((X1) = (k1_xboole_0))
% 0.54/0.75          | ((X1) = (k1_tarski @ X0))
% 0.54/0.75          | ((X1) = (k1_tarski @ X0))
% 0.54/0.75          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.54/0.75          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['17', '23'])).
% 0.54/0.75  thf('25', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (((X1) = (k2_tarski @ X0 @ X0))
% 0.54/0.75          | ((X1) = (k1_tarski @ X0))
% 0.54/0.75          | ((X1) = (k1_xboole_0))
% 0.54/0.75          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['24'])).
% 0.54/0.75  thf('26', plain,
% 0.54/0.75      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.54/0.75        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.54/0.75        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['16', '25'])).
% 0.54/0.75  thf('27', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.54/0.75      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.75  thf('28', plain,
% 0.54/0.75      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.54/0.75        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.54/0.75        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['26', '27'])).
% 0.54/0.75  thf('29', plain,
% 0.54/0.75      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.54/0.75        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['28'])).
% 0.54/0.75  thf(t14_funct_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.75       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.54/0.75         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.54/0.75  thf('30', plain,
% 0.54/0.75      (![X28 : $i, X29 : $i]:
% 0.54/0.75         (((k1_relat_1 @ X29) != (k1_tarski @ X28))
% 0.54/0.75          | ((k2_relat_1 @ X29) = (k1_tarski @ (k1_funct_1 @ X29 @ X28)))
% 0.54/0.75          | ~ (v1_funct_1 @ X29)
% 0.54/0.75          | ~ (v1_relat_1 @ X29))),
% 0.54/0.75      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.54/0.75  thf('31', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.54/0.75          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_funct_1 @ X0)
% 0.54/0.75          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['29', '30'])).
% 0.54/0.75  thf('32', plain,
% 0.54/0.75      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.54/0.75        | ~ (v1_funct_1 @ sk_D)
% 0.54/0.75        | ~ (v1_relat_1 @ sk_D)
% 0.54/0.75        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.54/0.75      inference('eq_res', [status(thm)], ['31'])).
% 0.54/0.75  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 0.54/0.75      inference('demod', [status(thm)], ['13', '14'])).
% 0.54/0.75  thf('35', plain,
% 0.54/0.75      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.54/0.75        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.54/0.75  thf('36', plain,
% 0.54/0.75      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.54/0.75          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['0', '3'])).
% 0.54/0.75  thf('37', plain,
% 0.54/0.75      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.54/0.75        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['35', '36'])).
% 0.54/0.75  thf('38', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['5', '37'])).
% 0.54/0.75  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 0.54/0.75      inference('demod', [status(thm)], ['13', '14'])).
% 0.54/0.75  thf('40', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['38', '39'])).
% 0.54/0.75  thf(t3_funct_2, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.54/0.75       ( ( v1_funct_1 @ A ) & 
% 0.54/0.75         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.54/0.75         ( m1_subset_1 @
% 0.54/0.75           A @ 
% 0.54/0.75           ( k1_zfmisc_1 @
% 0.54/0.75             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.54/0.75  thf('41', plain,
% 0.54/0.75      (![X37 : $i]:
% 0.54/0.75         ((m1_subset_1 @ X37 @ 
% 0.54/0.75           (k1_zfmisc_1 @ 
% 0.54/0.75            (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37))))
% 0.54/0.75          | ~ (v1_funct_1 @ X37)
% 0.54/0.75          | ~ (v1_relat_1 @ X37))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.54/0.75  thf(t3_subset, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.75  thf('42', plain,
% 0.54/0.75      (![X15 : $i, X16 : $i]:
% 0.54/0.75         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.75  thf('43', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_funct_1 @ X0)
% 0.54/0.75          | (r1_tarski @ X0 @ 
% 0.54/0.75             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['41', '42'])).
% 0.54/0.75  thf(d10_xboole_0, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.75  thf('44', plain,
% 0.54/0.75      (![X0 : $i, X2 : $i]:
% 0.54/0.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.75  thf('45', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_funct_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (r1_tarski @ 
% 0.54/0.75               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 0.54/0.75          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['43', '44'])).
% 0.54/0.75  thf('46', plain,
% 0.54/0.75      ((~ (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_D)) @ sk_D)
% 0.54/0.75        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D)) = (sk_D))
% 0.54/0.75        | ~ (v1_relat_1 @ sk_D)
% 0.54/0.75        | ~ (v1_funct_1 @ sk_D))),
% 0.54/0.75      inference('sup-', [status(thm)], ['40', '45'])).
% 0.54/0.75  thf(t113_zfmisc_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.75       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.75  thf('47', plain,
% 0.54/0.75      (![X8 : $i, X9 : $i]:
% 0.54/0.75         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.54/0.75  thf('48', plain,
% 0.54/0.75      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['47'])).
% 0.54/0.75  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.75  thf('49', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.75  thf('50', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['38', '39'])).
% 0.54/0.75  thf('51', plain,
% 0.54/0.75      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['47'])).
% 0.54/0.75  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 0.54/0.75      inference('demod', [status(thm)], ['13', '14'])).
% 0.54/0.75  thf('53', plain, ((v1_funct_1 @ sk_D)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('54', plain, (((k1_xboole_0) = (sk_D))),
% 0.54/0.75      inference('demod', [status(thm)],
% 0.54/0.75                ['46', '48', '49', '50', '51', '52', '53'])).
% 0.54/0.75  thf('55', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.75  thf('56', plain,
% 0.54/0.75      (![X15 : $i, X17 : $i]:
% 0.54/0.75         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.75  thf('57', plain,
% 0.54/0.75      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['55', '56'])).
% 0.54/0.75  thf('58', plain,
% 0.54/0.75      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.54/0.75         ((v5_relat_1 @ X30 @ X32)
% 0.54/0.75          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.75  thf('59', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.54/0.75      inference('sup-', [status(thm)], ['57', '58'])).
% 0.54/0.75  thf(d19_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ B ) =>
% 0.54/0.75       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.75  thf('60', plain,
% 0.54/0.75      (![X22 : $i, X23 : $i]:
% 0.54/0.75         (~ (v5_relat_1 @ X22 @ X23)
% 0.54/0.75          | (r1_tarski @ (k2_relat_1 @ X22) @ X23)
% 0.54/0.75          | ~ (v1_relat_1 @ X22))),
% 0.54/0.75      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.54/0.75  thf('61', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ k1_xboole_0)
% 0.54/0.75          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['59', '60'])).
% 0.54/0.75  thf('62', plain,
% 0.54/0.75      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['47'])).
% 0.54/0.75  thf('63', plain,
% 0.54/0.75      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 0.54/0.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.75  thf('64', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.54/0.75      inference('sup+', [status(thm)], ['62', '63'])).
% 0.54/0.75  thf('65', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.54/0.75      inference('demod', [status(thm)], ['61', '64'])).
% 0.54/0.75  thf('66', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.75  thf('67', plain,
% 0.54/0.75      (![X0 : $i, X2 : $i]:
% 0.54/0.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.75  thf('68', plain,
% 0.54/0.75      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['66', '67'])).
% 0.54/0.75  thf('69', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['65', '68'])).
% 0.54/0.75  thf('70', plain,
% 0.54/0.75      (![X26 : $i, X27 : $i]:
% 0.54/0.75         ((r1_tarski @ (k9_relat_1 @ X26 @ X27) @ (k2_relat_1 @ X26))
% 0.54/0.75          | ~ (v1_relat_1 @ X26))),
% 0.54/0.75      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.54/0.75  thf('71', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.54/0.75          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['69', '70'])).
% 0.54/0.75  thf('72', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.54/0.75      inference('sup+', [status(thm)], ['62', '63'])).
% 0.54/0.75  thf('73', plain,
% 0.54/0.75      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.54/0.75      inference('demod', [status(thm)], ['71', '72'])).
% 0.54/0.75  thf('74', plain,
% 0.54/0.75      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['66', '67'])).
% 0.54/0.75  thf('75', plain,
% 0.54/0.75      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['73', '74'])).
% 0.54/0.75  thf('76', plain, (((k1_xboole_0) = (sk_D))),
% 0.54/0.75      inference('demod', [status(thm)],
% 0.54/0.75                ['46', '48', '49', '50', '51', '52', '53'])).
% 0.54/0.75  thf('77', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.75  thf('78', plain, ($false),
% 0.54/0.75      inference('demod', [status(thm)], ['4', '54', '75', '76', '77'])).
% 0.54/0.75  
% 0.54/0.75  % SZS output end Refutation
% 0.54/0.75  
% 0.54/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
