%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.odlCbQCNPp

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:51 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 273 expanded)
%              Number of leaves         :   35 (  94 expanded)
%              Depth                    :   15
%              Number of atoms          : 1271 (5405 expanded)
%              Number of equality atoms :   37 ( 138 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t24_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
             => ( ( k2_relset_1 @ A @ B @ C )
                = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_funct_2])).

thf('0',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k6_partfun1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k5_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_B @ sk_B @ ( k5_relat_1 @ sk_D @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ sk_D @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('26',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X35: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X35 ) @ ( k2_relat_1 @ X35 ) ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('31',plain,(
    ! [X35: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X35 ) @ ( k2_relat_1 @ X35 ) ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('32',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X35: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X35 ) @ ( k2_relat_1 @ X35 ) ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('38',plain,(
    ! [X35: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X35 ) @ ( k2_relat_1 @ X35 ) ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','56'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('58',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('69',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('74',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['57','58','67','68','69','70','71','74','75'])).

thf('77',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('79',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('80',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.odlCbQCNPp
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:50:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 233 iterations in 0.136s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.59  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.38/0.59  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.38/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.59  thf(t24_funct_2, conjecture,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.59       ( ![D:$i]:
% 0.38/0.59         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.38/0.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.38/0.59           ( ( r2_relset_1 @
% 0.38/0.59               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.38/0.59               ( k6_partfun1 @ B ) ) =>
% 0.38/0.59             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.59            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.59          ( ![D:$i]:
% 0.38/0.59            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.38/0.59                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.38/0.59              ( ( r2_relset_1 @
% 0.38/0.59                  B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.38/0.59                  ( k6_partfun1 @ B ) ) =>
% 0.38/0.59                ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t24_funct_2])).
% 0.38/0.59  thf('0', plain,
% 0.38/0.59      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.38/0.59        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.38/0.59        (k6_partfun1 @ sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(redefinition_k6_partfun1, axiom,
% 0.38/0.59    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.38/0.59  thf('1', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.38/0.59        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.38/0.59        (k6_relat_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(redefinition_k1_partfun1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.59     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.59         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.59         ( v1_funct_1 @ F ) & 
% 0.38/0.59         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.38/0.59       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.38/0.59  thf('5', plain,
% 0.38/0.59      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.38/0.59          | ~ (v1_funct_1 @ X28)
% 0.38/0.59          | ~ (v1_funct_1 @ X31)
% 0.38/0.59          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.38/0.59          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 0.38/0.59              = (k5_relat_1 @ X28 @ X31)))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.38/0.59  thf('6', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.38/0.59            = (k5_relat_1 @ sk_D @ X0))
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ sk_D))),
% 0.38/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.59  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('8', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.38/0.59            = (k5_relat_1 @ sk_D @ X0))
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.38/0.59          | ~ (v1_funct_1 @ X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['6', '7'])).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.59        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.38/0.59            = (k5_relat_1 @ sk_D @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['3', '8'])).
% 0.38/0.59  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('11', plain,
% 0.38/0.59      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.38/0.59         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.38/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      ((r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 0.38/0.59        (k6_relat_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['2', '11'])).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('14', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(dt_k1_partfun1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.59     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.59         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.59         ( v1_funct_1 @ F ) & 
% 0.38/0.59         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.38/0.59       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.38/0.59         ( m1_subset_1 @
% 0.38/0.59           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.59           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.38/0.59          | ~ (v1_funct_1 @ X20)
% 0.38/0.59          | ~ (v1_funct_1 @ X23)
% 0.38/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.38/0.59          | (m1_subset_1 @ (k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X25))))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.38/0.59  thf('16', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ sk_D))),
% 0.38/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.59  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.38/0.59          | ~ (v1_funct_1 @ X1))),
% 0.38/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.59        | (m1_subset_1 @ 
% 0.38/0.59           (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['13', '18'])).
% 0.38/0.59  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.38/0.59         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.38/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.38/0.59  thf(redefinition_r2_relset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.59     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.59       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.38/0.59  thf('23', plain,
% 0.38/0.59      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.38/0.59          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.38/0.59          | ((X16) = (X19))
% 0.38/0.59          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.38/0.59  thf('24', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ X0)
% 0.38/0.59          | ((k5_relat_1 @ sk_D @ sk_C) = (X0))
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_B) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))
% 0.38/0.59        | ((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['12', '24'])).
% 0.38/0.59  thf(dt_k6_partfun1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( m1_subset_1 @
% 0.38/0.59         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.38/0.59       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (![X27 : $i]:
% 0.38/0.59         (m1_subset_1 @ (k6_partfun1 @ X27) @ 
% 0.38/0.59          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.38/0.59  thf('27', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.38/0.59  thf('28', plain,
% 0.38/0.59      (![X27 : $i]:
% 0.38/0.59         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 0.38/0.59          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.38/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.59  thf('29', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['25', '28'])).
% 0.38/0.59  thf(t3_funct_2, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.59       ( ( v1_funct_1 @ A ) & 
% 0.38/0.59         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.38/0.59         ( m1_subset_1 @
% 0.38/0.59           A @ 
% 0.38/0.59           ( k1_zfmisc_1 @
% 0.38/0.59             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.38/0.59  thf('30', plain,
% 0.38/0.59      (![X35 : $i]:
% 0.38/0.59         ((m1_subset_1 @ X35 @ 
% 0.38/0.59           (k1_zfmisc_1 @ 
% 0.38/0.59            (k2_zfmisc_1 @ (k1_relat_1 @ X35) @ (k2_relat_1 @ X35))))
% 0.38/0.59          | ~ (v1_funct_1 @ X35)
% 0.38/0.59          | ~ (v1_relat_1 @ X35))),
% 0.38/0.59      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.38/0.59  thf('31', plain,
% 0.38/0.59      (![X35 : $i]:
% 0.38/0.59         ((m1_subset_1 @ X35 @ 
% 0.38/0.59           (k1_zfmisc_1 @ 
% 0.38/0.59            (k2_zfmisc_1 @ (k1_relat_1 @ X35) @ (k2_relat_1 @ X35))))
% 0.38/0.59          | ~ (v1_funct_1 @ X35)
% 0.38/0.59          | ~ (v1_relat_1 @ X35))),
% 0.38/0.59      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.38/0.59  thf('32', plain,
% 0.38/0.59      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.38/0.59          | ~ (v1_funct_1 @ X28)
% 0.38/0.59          | ~ (v1_funct_1 @ X31)
% 0.38/0.59          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.38/0.59          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 0.38/0.59              = (k5_relat_1 @ X28 @ X31)))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.38/0.59  thf('33', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 0.38/0.59              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.59  thf('34', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X1)
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 0.38/0.59          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 0.38/0.59              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['33'])).
% 0.38/0.59  thf('35', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | ((k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 0.38/0.59              (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0)
% 0.38/0.59              = (k5_relat_1 @ X1 @ X0))
% 0.38/0.59          | ~ (v1_funct_1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['30', '34'])).
% 0.38/0.59  thf('36', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 0.38/0.59            (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0)
% 0.38/0.59            = (k5_relat_1 @ X1 @ X0))
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['35'])).
% 0.38/0.59  thf('37', plain,
% 0.38/0.59      (![X35 : $i]:
% 0.38/0.59         ((m1_subset_1 @ X35 @ 
% 0.38/0.59           (k1_zfmisc_1 @ 
% 0.38/0.59            (k2_zfmisc_1 @ (k1_relat_1 @ X35) @ (k2_relat_1 @ X35))))
% 0.38/0.59          | ~ (v1_funct_1 @ X35)
% 0.38/0.59          | ~ (v1_relat_1 @ X35))),
% 0.38/0.59      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.38/0.59  thf('38', plain,
% 0.38/0.59      (![X35 : $i]:
% 0.38/0.59         ((m1_subset_1 @ X35 @ 
% 0.38/0.59           (k1_zfmisc_1 @ 
% 0.38/0.59            (k2_zfmisc_1 @ (k1_relat_1 @ X35) @ (k2_relat_1 @ X35))))
% 0.38/0.59          | ~ (v1_funct_1 @ X35)
% 0.38/0.59          | ~ (v1_relat_1 @ X35))),
% 0.38/0.59      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.38/0.59  thf('39', plain,
% 0.38/0.59      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.38/0.59          | ~ (v1_funct_1 @ X20)
% 0.38/0.59          | ~ (v1_funct_1 @ X23)
% 0.38/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.38/0.59          | (m1_subset_1 @ (k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X25))))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.38/0.59  thf('40', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | (m1_subset_1 @ 
% 0.38/0.59             (k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X1 @ 
% 0.38/0.59              X0 @ X2) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.38/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 0.38/0.59          | ~ (v1_funct_1 @ X2)
% 0.38/0.59          | ~ (v1_funct_1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.59  thf('41', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X2)
% 0.38/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 0.38/0.59          | (m1_subset_1 @ 
% 0.38/0.59             (k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X1 @ 
% 0.38/0.59              X0 @ X2) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['40'])).
% 0.38/0.59  thf('42', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | (m1_subset_1 @ 
% 0.38/0.59             (k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 0.38/0.59              (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0) @ 
% 0.38/0.59             (k1_zfmisc_1 @ 
% 0.38/0.59              (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.38/0.59          | ~ (v1_funct_1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['37', '41'])).
% 0.38/0.59  thf('43', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((m1_subset_1 @ 
% 0.38/0.59           (k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 0.38/0.59            (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['42'])).
% 0.38/0.59  thf('44', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((m1_subset_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X1))),
% 0.38/0.59      inference('sup+', [status(thm)], ['36', '43'])).
% 0.38/0.59  thf('45', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | (m1_subset_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.38/0.59             (k1_zfmisc_1 @ 
% 0.38/0.59              (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0)))))),
% 0.38/0.59      inference('simplify', [status(thm)], ['44'])).
% 0.38/0.59  thf(cc1_relset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.59       ( v1_relat_1 @ C ) ))).
% 0.38/0.59  thf('46', plain,
% 0.38/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.59         ((v1_relat_1 @ X7)
% 0.38/0.59          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.59  thf('47', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.59  thf('48', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | (m1_subset_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.38/0.59             (k1_zfmisc_1 @ 
% 0.38/0.59              (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0)))))),
% 0.38/0.59      inference('simplify', [status(thm)], ['44'])).
% 0.38/0.59  thf(cc2_relset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.59  thf('49', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.59         ((v5_relat_1 @ X10 @ X12)
% 0.38/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.59  thf('50', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.59  thf(d19_relat_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ B ) =>
% 0.38/0.59       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.59  thf('51', plain,
% 0.38/0.59      (![X3 : $i, X4 : $i]:
% 0.38/0.59         (~ (v5_relat_1 @ X3 @ X4)
% 0.38/0.59          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.38/0.59          | ~ (v1_relat_1 @ X3))),
% 0.38/0.59      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.38/0.59  thf('52', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.38/0.59          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.38/0.59             (k2_relat_1 @ X0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.59  thf('53', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.38/0.59             (k2_relat_1 @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['47', '52'])).
% 0.38/0.59  thf('54', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.38/0.59           (k2_relat_1 @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X1))),
% 0.38/0.59      inference('simplify', [status(thm)], ['53'])).
% 0.38/0.59  thf(d10_xboole_0, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.59  thf('55', plain,
% 0.38/0.59      (![X0 : $i, X2 : $i]:
% 0.38/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.59  thf('56', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.38/0.59               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.38/0.59          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.59  thf('57', plain,
% 0.38/0.59      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_relat_1 @ (k6_relat_1 @ sk_B)))
% 0.38/0.59        | ((k2_relat_1 @ sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C)))
% 0.38/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.59        | ~ (v1_relat_1 @ sk_D)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_D))),
% 0.38/0.59      inference('sup-', [status(thm)], ['29', '56'])).
% 0.38/0.59  thf(t71_relat_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.38/0.59       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.59  thf('58', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.38/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.59  thf('59', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('60', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.59         ((v5_relat_1 @ X10 @ X12)
% 0.38/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.59  thf('61', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.38/0.59      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.59  thf('62', plain,
% 0.38/0.59      (![X3 : $i, X4 : $i]:
% 0.38/0.59         (~ (v5_relat_1 @ X3 @ X4)
% 0.38/0.59          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.38/0.59          | ~ (v1_relat_1 @ X3))),
% 0.38/0.59      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.38/0.59  thf('63', plain,
% 0.38/0.59      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['61', '62'])).
% 0.38/0.59  thf('64', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('65', plain,
% 0.38/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.59         ((v1_relat_1 @ X7)
% 0.38/0.59          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.59  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.59      inference('sup-', [status(thm)], ['64', '65'])).
% 0.38/0.59  thf('67', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.38/0.59      inference('demod', [status(thm)], ['63', '66'])).
% 0.38/0.59  thf('68', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['25', '28'])).
% 0.38/0.59  thf('69', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.38/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.59  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.59      inference('sup-', [status(thm)], ['64', '65'])).
% 0.38/0.59  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('72', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('73', plain,
% 0.38/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.59         ((v1_relat_1 @ X7)
% 0.38/0.59          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.59  thf('74', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.59      inference('sup-', [status(thm)], ['72', '73'])).
% 0.38/0.59  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('76', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.38/0.59      inference('demod', [status(thm)],
% 0.38/0.59                ['57', '58', '67', '68', '69', '70', '71', '74', '75'])).
% 0.38/0.59  thf('77', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('78', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.59  thf('79', plain,
% 0.38/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.59         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.38/0.59          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.59  thf('80', plain,
% 0.38/0.59      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.38/0.59      inference('sup-', [status(thm)], ['78', '79'])).
% 0.38/0.59  thf('81', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['77', '80'])).
% 0.38/0.59  thf('82', plain, ($false),
% 0.38/0.59      inference('simplify_reflect-', [status(thm)], ['76', '81'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
