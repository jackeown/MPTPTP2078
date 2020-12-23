%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sgazxrPlmB

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:55 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  186 (1202 expanded)
%              Number of leaves         :   47 ( 375 expanded)
%              Depth                    :   24
%              Number of atoms          : 1616 (28555 expanded)
%              Number of equality atoms :  106 (1867 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('2',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('11',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('18',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( X30 = X33 )
      | ~ ( r2_relset_1 @ X31 @ X32 @ X30 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('21',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X18
        = ( k2_funct_1 @ X19 ) )
      | ( ( k5_relat_1 @ X18 @ X19 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X19 ) ) )
      | ( ( k2_relat_1 @ X18 )
       != ( k1_relat_1 @ X19 ) )
      | ~ ( v2_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('27',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X18
        = ( k2_funct_1 @ X19 ) )
      | ( ( k5_relat_1 @ X18 @ X19 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X19 ) ) )
      | ( ( k2_relat_1 @ X18 )
       != ( k1_relat_1 @ X19 ) )
      | ~ ( v2_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','32','33','38','39','42'])).

thf('44',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('46',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('48',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('49',plain,(
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X13 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('51',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['36','37'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['40','41'])).

thf('55',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['46','49','50','51','52','53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('57',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('58',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('59',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('62',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k2_relat_1 @ X15 ) )
      | ( ( k9_relat_1 @ X15 @ ( k10_relat_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['40','41'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('71',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('72',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('73',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('74',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('75',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['40','41'])).

thf('77',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('78',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['72','75','76','77'])).

thf('79',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['69','78'])).

thf('80',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('81',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('82',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('88',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['40','41'])).

thf('92',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

thf('94',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['40','41'])).

thf('97',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['84','85','92','93','94','95','96'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('98',plain,(
    ! [X5: $i] :
      ( ( ( k9_relat_1 @ X5 @ ( k1_relat_1 @ X5 ) )
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('99',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['36','37'])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['40','41'])).

thf('102',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['79','102'])).

thf('104',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['55','103'])).

thf('105',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['79','102'])).

thf('107',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['43','105','106'])).

thf('108',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
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

thf('111',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( r2_relset_1 @ X49 @ X49 @ ( k1_partfun1 @ X49 @ X50 @ X50 @ X49 @ X48 @ X51 ) @ ( k6_partfun1 @ X49 ) )
      | ( ( k2_relset_1 @ X50 @ X49 @ X51 )
        = X49 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X49 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['109','115'])).

thf('117',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('118',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( r2_relset_1 @ X31 @ X32 @ X30 @ X33 )
      | ( X30 != X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('119',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_relset_1 @ X31 @ X32 @ X33 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('123',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['116','120','123','124','125','126'])).

thf('128',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','127'])).

thf('129',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['128'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('130',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X20 ) )
        = X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('131',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('133',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['104'])).

thf('135',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['131','132','133','134'])).

thf('136',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['135','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sgazxrPlmB
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 19:36:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.91/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.12  % Solved by: fo/fo7.sh
% 0.91/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.12  % done 874 iterations in 0.671s
% 0.91/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.12  % SZS output start Refutation
% 0.91/1.12  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.91/1.12  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.91/1.12  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.91/1.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.12  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.91/1.12  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.91/1.12  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.12  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.91/1.12  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.91/1.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.12  thf(sk_D_type, type, sk_D: $i).
% 0.91/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.12  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.12  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.91/1.12  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.91/1.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.12  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.91/1.12  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.91/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.12  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.91/1.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.12  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.91/1.12  thf(t36_funct_2, conjecture,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.12       ( ![D:$i]:
% 0.91/1.12         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.91/1.12             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.91/1.12           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.91/1.12               ( r2_relset_1 @
% 0.91/1.12                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.91/1.12                 ( k6_partfun1 @ A ) ) & 
% 0.91/1.12               ( v2_funct_1 @ C ) ) =>
% 0.91/1.12             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.91/1.12               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.91/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.12    (~( ![A:$i,B:$i,C:$i]:
% 0.91/1.12        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.12            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.12          ( ![D:$i]:
% 0.91/1.12            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.91/1.12                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.91/1.12              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.91/1.12                  ( r2_relset_1 @
% 0.91/1.12                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.91/1.12                    ( k6_partfun1 @ A ) ) & 
% 0.91/1.12                  ( v2_funct_1 @ C ) ) =>
% 0.91/1.12                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.91/1.12                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.91/1.12    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.91/1.12  thf('0', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('1', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(redefinition_k1_partfun1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.91/1.12     ( ( ( v1_funct_1 @ E ) & 
% 0.91/1.12         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.91/1.12         ( v1_funct_1 @ F ) & 
% 0.91/1.12         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.91/1.12       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.91/1.12  thf('2', plain,
% 0.91/1.12      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.91/1.12          | ~ (v1_funct_1 @ X41)
% 0.91/1.12          | ~ (v1_funct_1 @ X44)
% 0.91/1.12          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.91/1.12          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 0.91/1.12              = (k5_relat_1 @ X41 @ X44)))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.91/1.12  thf('3', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.12         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.91/1.12            = (k5_relat_1 @ sk_C @ X0))
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.91/1.12          | ~ (v1_funct_1 @ X0)
% 0.91/1.12          | ~ (v1_funct_1 @ sk_C))),
% 0.91/1.12      inference('sup-', [status(thm)], ['1', '2'])).
% 0.91/1.12  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('5', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.12         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.91/1.12            = (k5_relat_1 @ sk_C @ X0))
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.91/1.12          | ~ (v1_funct_1 @ X0))),
% 0.91/1.12      inference('demod', [status(thm)], ['3', '4'])).
% 0.91/1.12  thf('6', plain,
% 0.91/1.12      ((~ (v1_funct_1 @ sk_D)
% 0.91/1.12        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.91/1.12            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['0', '5'])).
% 0.91/1.12  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('8', plain,
% 0.91/1.12      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.12        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.91/1.12        (k6_partfun1 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('9', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('10', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(dt_k1_partfun1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.91/1.12     ( ( ( v1_funct_1 @ E ) & 
% 0.91/1.12         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.91/1.12         ( v1_funct_1 @ F ) & 
% 0.91/1.12         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.91/1.12       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.91/1.12         ( m1_subset_1 @
% 0.91/1.12           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.91/1.12           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.91/1.12  thf('11', plain,
% 0.91/1.12      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.91/1.12          | ~ (v1_funct_1 @ X35)
% 0.91/1.12          | ~ (v1_funct_1 @ X38)
% 0.91/1.12          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.91/1.12          | (m1_subset_1 @ (k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38) @ 
% 0.91/1.12             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X40))))),
% 0.91/1.12      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.91/1.12  thf('12', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.12         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.91/1.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.91/1.12          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.91/1.12          | ~ (v1_funct_1 @ X1)
% 0.91/1.12          | ~ (v1_funct_1 @ sk_C))),
% 0.91/1.12      inference('sup-', [status(thm)], ['10', '11'])).
% 0.91/1.12  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('14', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.12         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.91/1.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.91/1.12          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.91/1.12          | ~ (v1_funct_1 @ X1))),
% 0.91/1.12      inference('demod', [status(thm)], ['12', '13'])).
% 0.91/1.12  thf('15', plain,
% 0.91/1.12      ((~ (v1_funct_1 @ sk_D)
% 0.91/1.12        | (m1_subset_1 @ 
% 0.91/1.12           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.91/1.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['9', '14'])).
% 0.91/1.12  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('17', plain,
% 0.91/1.12      ((m1_subset_1 @ 
% 0.91/1.12        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.91/1.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.12      inference('demod', [status(thm)], ['15', '16'])).
% 0.91/1.12  thf(redefinition_r2_relset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.12     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.91/1.12         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.12       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.91/1.12  thf('18', plain,
% 0.91/1.12      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.91/1.12          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.91/1.12          | ((X30) = (X33))
% 0.91/1.12          | ~ (r2_relset_1 @ X31 @ X32 @ X30 @ X33))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.91/1.12  thf('19', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.12             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.91/1.12          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['17', '18'])).
% 0.91/1.12  thf('20', plain,
% 0.91/1.12      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.91/1.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.91/1.12        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.91/1.12            = (k6_partfun1 @ sk_A)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['8', '19'])).
% 0.91/1.12  thf(t29_relset_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( m1_subset_1 @
% 0.91/1.12       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.91/1.12  thf('21', plain,
% 0.91/1.12      (![X34 : $i]:
% 0.91/1.12         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 0.91/1.12          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.91/1.12      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.91/1.12  thf(redefinition_k6_partfun1, axiom,
% 0.91/1.12    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.91/1.12  thf('22', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.91/1.12  thf('23', plain,
% 0.91/1.12      (![X34 : $i]:
% 0.91/1.12         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 0.91/1.12          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.91/1.12      inference('demod', [status(thm)], ['21', '22'])).
% 0.91/1.12  thf('24', plain,
% 0.91/1.12      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.91/1.12         = (k6_partfun1 @ sk_A))),
% 0.91/1.12      inference('demod', [status(thm)], ['20', '23'])).
% 0.91/1.12  thf('25', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.91/1.12      inference('demod', [status(thm)], ['6', '7', '24'])).
% 0.91/1.12  thf(t64_funct_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.12       ( ![B:$i]:
% 0.91/1.12         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.12           ( ( ( v2_funct_1 @ A ) & 
% 0.91/1.12               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.91/1.12               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.91/1.12             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.91/1.12  thf('26', plain,
% 0.91/1.12      (![X18 : $i, X19 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X18)
% 0.91/1.12          | ~ (v1_funct_1 @ X18)
% 0.91/1.12          | ((X18) = (k2_funct_1 @ X19))
% 0.91/1.12          | ((k5_relat_1 @ X18 @ X19) != (k6_relat_1 @ (k2_relat_1 @ X19)))
% 0.91/1.12          | ((k2_relat_1 @ X18) != (k1_relat_1 @ X19))
% 0.91/1.12          | ~ (v2_funct_1 @ X19)
% 0.91/1.12          | ~ (v1_funct_1 @ X19)
% 0.91/1.12          | ~ (v1_relat_1 @ X19))),
% 0.91/1.12      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.91/1.12  thf('27', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.91/1.12  thf('28', plain,
% 0.91/1.12      (![X18 : $i, X19 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X18)
% 0.91/1.12          | ~ (v1_funct_1 @ X18)
% 0.91/1.12          | ((X18) = (k2_funct_1 @ X19))
% 0.91/1.12          | ((k5_relat_1 @ X18 @ X19) != (k6_partfun1 @ (k2_relat_1 @ X19)))
% 0.91/1.12          | ((k2_relat_1 @ X18) != (k1_relat_1 @ X19))
% 0.91/1.12          | ~ (v2_funct_1 @ X19)
% 0.91/1.12          | ~ (v1_funct_1 @ X19)
% 0.91/1.12          | ~ (v1_relat_1 @ X19))),
% 0.91/1.12      inference('demod', [status(thm)], ['26', '27'])).
% 0.91/1.12  thf('29', plain,
% 0.91/1.12      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.91/1.12        | ~ (v1_relat_1 @ sk_D)
% 0.91/1.12        | ~ (v1_funct_1 @ sk_D)
% 0.91/1.12        | ~ (v2_funct_1 @ sk_D)
% 0.91/1.12        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.91/1.12        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.91/1.12        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.12        | ~ (v1_relat_1 @ sk_C))),
% 0.91/1.12      inference('sup-', [status(thm)], ['25', '28'])).
% 0.91/1.12  thf('30', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(cc1_relset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.12       ( v1_relat_1 @ C ) ))).
% 0.91/1.12  thf('31', plain,
% 0.91/1.12      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.91/1.12         ((v1_relat_1 @ X21)
% 0.91/1.12          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.91/1.12      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.91/1.12  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.12      inference('sup-', [status(thm)], ['30', '31'])).
% 0.91/1.12  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('34', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(redefinition_k2_relset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.12       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.91/1.12  thf('35', plain,
% 0.91/1.12      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.91/1.12         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.91/1.12          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.91/1.12  thf('36', plain,
% 0.91/1.12      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.91/1.12      inference('sup-', [status(thm)], ['34', '35'])).
% 0.91/1.12  thf('37', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('38', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.91/1.12      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.12  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('40', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('41', plain,
% 0.91/1.12      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.91/1.12         ((v1_relat_1 @ X21)
% 0.91/1.12          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.91/1.12      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.91/1.12  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.12      inference('sup-', [status(thm)], ['40', '41'])).
% 0.91/1.12  thf('43', plain,
% 0.91/1.12      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.91/1.12        | ~ (v2_funct_1 @ sk_D)
% 0.91/1.12        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.91/1.12        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.91/1.12      inference('demod', [status(thm)], ['29', '32', '33', '38', '39', '42'])).
% 0.91/1.12  thf('44', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.91/1.12      inference('demod', [status(thm)], ['6', '7', '24'])).
% 0.91/1.12  thf(t48_funct_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.12       ( ![B:$i]:
% 0.91/1.12         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.12           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.91/1.12               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.91/1.12             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.91/1.12  thf('45', plain,
% 0.91/1.12      (![X16 : $i, X17 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X16)
% 0.91/1.12          | ~ (v1_funct_1 @ X16)
% 0.91/1.12          | (v2_funct_1 @ X17)
% 0.91/1.12          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X17))
% 0.91/1.12          | ~ (v2_funct_1 @ (k5_relat_1 @ X16 @ X17))
% 0.91/1.12          | ~ (v1_funct_1 @ X17)
% 0.91/1.12          | ~ (v1_relat_1 @ X17))),
% 0.91/1.12      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.91/1.12  thf('46', plain,
% 0.91/1.12      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.91/1.12        | ~ (v1_relat_1 @ sk_D)
% 0.91/1.12        | ~ (v1_funct_1 @ sk_D)
% 0.91/1.12        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.91/1.12        | (v2_funct_1 @ sk_D)
% 0.91/1.12        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.12        | ~ (v1_relat_1 @ sk_C))),
% 0.91/1.12      inference('sup-', [status(thm)], ['44', '45'])).
% 0.91/1.12  thf(fc4_funct_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.91/1.12       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.91/1.12  thf('47', plain, (![X13 : $i]: (v2_funct_1 @ (k6_relat_1 @ X13))),
% 0.91/1.12      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.91/1.12  thf('48', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.91/1.12  thf('49', plain, (![X13 : $i]: (v2_funct_1 @ (k6_partfun1 @ X13))),
% 0.91/1.12      inference('demod', [status(thm)], ['47', '48'])).
% 0.91/1.12  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.12      inference('sup-', [status(thm)], ['30', '31'])).
% 0.91/1.12  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('52', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.91/1.12      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.12  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.12      inference('sup-', [status(thm)], ['40', '41'])).
% 0.91/1.12  thf('55', plain, ((((sk_B) != (k1_relat_1 @ sk_D)) | (v2_funct_1 @ sk_D))),
% 0.91/1.12      inference('demod', [status(thm)],
% 0.91/1.12                ['46', '49', '50', '51', '52', '53', '54'])).
% 0.91/1.12  thf('56', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(cc2_relset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.12       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.91/1.12  thf('57', plain,
% 0.91/1.12      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.91/1.12         ((v4_relat_1 @ X24 @ X25)
% 0.91/1.12          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.91/1.12      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.91/1.12  thf('58', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.91/1.12      inference('sup-', [status(thm)], ['56', '57'])).
% 0.91/1.12  thf(d18_relat_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ B ) =>
% 0.91/1.12       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.91/1.12  thf('59', plain,
% 0.91/1.12      (![X3 : $i, X4 : $i]:
% 0.91/1.12         (~ (v4_relat_1 @ X3 @ X4)
% 0.91/1.12          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.91/1.12          | ~ (v1_relat_1 @ X3))),
% 0.91/1.12      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.91/1.12  thf('60', plain,
% 0.91/1.12      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.91/1.12      inference('sup-', [status(thm)], ['58', '59'])).
% 0.91/1.12  thf('61', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.12      inference('sup-', [status(thm)], ['30', '31'])).
% 0.91/1.12  thf('62', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.91/1.12      inference('demod', [status(thm)], ['60', '61'])).
% 0.91/1.12  thf('63', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.91/1.12      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.12  thf(t147_funct_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.12       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.91/1.12         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.91/1.12  thf('64', plain,
% 0.91/1.12      (![X14 : $i, X15 : $i]:
% 0.91/1.12         (~ (r1_tarski @ X14 @ (k2_relat_1 @ X15))
% 0.91/1.12          | ((k9_relat_1 @ X15 @ (k10_relat_1 @ X15 @ X14)) = (X14))
% 0.91/1.12          | ~ (v1_funct_1 @ X15)
% 0.91/1.12          | ~ (v1_relat_1 @ X15))),
% 0.91/1.12      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.91/1.12  thf('65', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (r1_tarski @ X0 @ sk_B)
% 0.91/1.12          | ~ (v1_relat_1 @ sk_C)
% 0.91/1.12          | ~ (v1_funct_1 @ sk_C)
% 0.91/1.12          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['63', '64'])).
% 0.91/1.12  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.12      inference('sup-', [status(thm)], ['40', '41'])).
% 0.91/1.12  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('68', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (r1_tarski @ X0 @ sk_B)
% 0.91/1.12          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.91/1.12      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.91/1.12  thf('69', plain,
% 0.91/1.12      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.91/1.12         = (k1_relat_1 @ sk_D))),
% 0.91/1.12      inference('sup-', [status(thm)], ['62', '68'])).
% 0.91/1.12  thf('70', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.91/1.12      inference('demod', [status(thm)], ['6', '7', '24'])).
% 0.91/1.12  thf(t182_relat_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ A ) =>
% 0.91/1.12       ( ![B:$i]:
% 0.91/1.12         ( ( v1_relat_1 @ B ) =>
% 0.91/1.12           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.91/1.12             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.91/1.12  thf('71', plain,
% 0.91/1.12      (![X6 : $i, X7 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X6)
% 0.91/1.12          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.91/1.12              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 0.91/1.12          | ~ (v1_relat_1 @ X7))),
% 0.91/1.12      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.91/1.12  thf('72', plain,
% 0.91/1.12      ((((k1_relat_1 @ (k6_partfun1 @ sk_A))
% 0.91/1.12          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.91/1.12        | ~ (v1_relat_1 @ sk_C)
% 0.91/1.12        | ~ (v1_relat_1 @ sk_D))),
% 0.91/1.12      inference('sup+', [status(thm)], ['70', '71'])).
% 0.91/1.12  thf(t71_relat_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.91/1.12       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.91/1.12  thf('73', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.91/1.12      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.12  thf('74', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.91/1.12  thf('75', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 0.91/1.12      inference('demod', [status(thm)], ['73', '74'])).
% 0.91/1.12  thf('76', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.12      inference('sup-', [status(thm)], ['40', '41'])).
% 0.91/1.12  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.12      inference('sup-', [status(thm)], ['30', '31'])).
% 0.91/1.12  thf('78', plain, (((sk_A) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 0.91/1.12      inference('demod', [status(thm)], ['72', '75', '76', '77'])).
% 0.91/1.12  thf('79', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.91/1.12      inference('demod', [status(thm)], ['69', '78'])).
% 0.91/1.12  thf('80', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.91/1.12      inference('demod', [status(thm)], ['6', '7', '24'])).
% 0.91/1.12  thf(t44_relat_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ A ) =>
% 0.91/1.12       ( ![B:$i]:
% 0.91/1.12         ( ( v1_relat_1 @ B ) =>
% 0.91/1.12           ( r1_tarski @
% 0.91/1.12             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.91/1.12  thf('81', plain,
% 0.91/1.12      (![X8 : $i, X9 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X8)
% 0.91/1.12          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X9 @ X8)) @ 
% 0.91/1.12             (k1_relat_1 @ X9))
% 0.91/1.12          | ~ (v1_relat_1 @ X9))),
% 0.91/1.12      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.91/1.12  thf(d10_xboole_0, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.12  thf('82', plain,
% 0.91/1.12      (![X0 : $i, X2 : $i]:
% 0.91/1.12         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.91/1.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.12  thf('83', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X0)
% 0.91/1.12          | ~ (v1_relat_1 @ X1)
% 0.91/1.12          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.91/1.12               (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 0.91/1.12          | ((k1_relat_1 @ X0) = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['81', '82'])).
% 0.91/1.12  thf('84', plain,
% 0.91/1.12      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 0.91/1.12           (k1_relat_1 @ (k6_partfun1 @ sk_A)))
% 0.91/1.12        | ((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 0.91/1.12        | ~ (v1_relat_1 @ sk_D)
% 0.91/1.12        | ~ (v1_relat_1 @ sk_C))),
% 0.91/1.12      inference('sup-', [status(thm)], ['80', '83'])).
% 0.91/1.12  thf('85', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 0.91/1.12      inference('demod', [status(thm)], ['73', '74'])).
% 0.91/1.12  thf('86', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('87', plain,
% 0.91/1.12      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.91/1.12         ((v4_relat_1 @ X24 @ X25)
% 0.91/1.12          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.91/1.12      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.91/1.12  thf('88', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.91/1.12      inference('sup-', [status(thm)], ['86', '87'])).
% 0.91/1.12  thf('89', plain,
% 0.91/1.12      (![X3 : $i, X4 : $i]:
% 0.91/1.12         (~ (v4_relat_1 @ X3 @ X4)
% 0.91/1.12          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.91/1.12          | ~ (v1_relat_1 @ X3))),
% 0.91/1.12      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.91/1.12  thf('90', plain,
% 0.91/1.12      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['88', '89'])).
% 0.91/1.12  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.12      inference('sup-', [status(thm)], ['40', '41'])).
% 0.91/1.12  thf('92', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.91/1.12      inference('demod', [status(thm)], ['90', '91'])).
% 0.91/1.12  thf('93', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.91/1.12      inference('demod', [status(thm)], ['6', '7', '24'])).
% 0.91/1.12  thf('94', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 0.91/1.12      inference('demod', [status(thm)], ['73', '74'])).
% 0.91/1.12  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.12      inference('sup-', [status(thm)], ['30', '31'])).
% 0.91/1.12  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.12      inference('sup-', [status(thm)], ['40', '41'])).
% 0.91/1.12  thf('97', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.91/1.12      inference('demod', [status(thm)],
% 0.91/1.12                ['84', '85', '92', '93', '94', '95', '96'])).
% 0.91/1.12  thf(t146_relat_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ A ) =>
% 0.91/1.12       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.91/1.12  thf('98', plain,
% 0.91/1.12      (![X5 : $i]:
% 0.91/1.12         (((k9_relat_1 @ X5 @ (k1_relat_1 @ X5)) = (k2_relat_1 @ X5))
% 0.91/1.12          | ~ (v1_relat_1 @ X5))),
% 0.91/1.12      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.91/1.12  thf('99', plain,
% 0.91/1.12      ((((k9_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))
% 0.91/1.12        | ~ (v1_relat_1 @ sk_C))),
% 0.91/1.12      inference('sup+', [status(thm)], ['97', '98'])).
% 0.91/1.12  thf('100', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.91/1.12      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.12  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.12      inference('sup-', [status(thm)], ['40', '41'])).
% 0.91/1.12  thf('102', plain, (((k9_relat_1 @ sk_C @ sk_A) = (sk_B))),
% 0.91/1.12      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.91/1.12  thf('103', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 0.91/1.12      inference('sup+', [status(thm)], ['79', '102'])).
% 0.91/1.12  thf('104', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 0.91/1.12      inference('demod', [status(thm)], ['55', '103'])).
% 0.91/1.12  thf('105', plain, ((v2_funct_1 @ sk_D)),
% 0.91/1.12      inference('simplify', [status(thm)], ['104'])).
% 0.91/1.12  thf('106', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 0.91/1.12      inference('sup+', [status(thm)], ['79', '102'])).
% 0.91/1.12  thf('107', plain,
% 0.91/1.12      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.91/1.12        | ((sk_B) != (sk_B))
% 0.91/1.12        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.91/1.12      inference('demod', [status(thm)], ['43', '105', '106'])).
% 0.91/1.12  thf('108', plain,
% 0.91/1.12      ((((sk_C) = (k2_funct_1 @ sk_D))
% 0.91/1.12        | ((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 0.91/1.12      inference('simplify', [status(thm)], ['107'])).
% 0.91/1.12  thf('109', plain,
% 0.91/1.12      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.91/1.12         = (k6_partfun1 @ sk_A))),
% 0.91/1.12      inference('demod', [status(thm)], ['20', '23'])).
% 0.91/1.12  thf('110', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(t24_funct_2, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.12       ( ![D:$i]:
% 0.91/1.12         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.91/1.12             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.91/1.12           ( ( r2_relset_1 @
% 0.91/1.12               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.91/1.12               ( k6_partfun1 @ B ) ) =>
% 0.91/1.12             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.91/1.12  thf('111', plain,
% 0.91/1.12      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.91/1.12         (~ (v1_funct_1 @ X48)
% 0.91/1.12          | ~ (v1_funct_2 @ X48 @ X49 @ X50)
% 0.91/1.12          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 0.91/1.12          | ~ (r2_relset_1 @ X49 @ X49 @ 
% 0.91/1.12               (k1_partfun1 @ X49 @ X50 @ X50 @ X49 @ X48 @ X51) @ 
% 0.91/1.12               (k6_partfun1 @ X49))
% 0.91/1.12          | ((k2_relset_1 @ X50 @ X49 @ X51) = (X49))
% 0.91/1.12          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.91/1.12          | ~ (v1_funct_2 @ X51 @ X50 @ X49)
% 0.91/1.12          | ~ (v1_funct_1 @ X51))),
% 0.91/1.12      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.91/1.12  thf('112', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (v1_funct_1 @ X0)
% 0.91/1.12          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.91/1.12          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.91/1.12          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.12               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.91/1.12               (k6_partfun1 @ sk_A))
% 0.91/1.12          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.91/1.12          | ~ (v1_funct_1 @ sk_C))),
% 0.91/1.12      inference('sup-', [status(thm)], ['110', '111'])).
% 0.91/1.12  thf('113', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('115', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (v1_funct_1 @ X0)
% 0.91/1.12          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.91/1.12          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.91/1.12          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.12               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.91/1.12               (k6_partfun1 @ sk_A)))),
% 0.91/1.12      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.91/1.12  thf('116', plain,
% 0.91/1.12      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.91/1.12           (k6_partfun1 @ sk_A))
% 0.91/1.12        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.91/1.12        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.91/1.12        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.91/1.12        | ~ (v1_funct_1 @ sk_D))),
% 0.91/1.12      inference('sup-', [status(thm)], ['109', '115'])).
% 0.91/1.12  thf('117', plain,
% 0.91/1.12      (![X34 : $i]:
% 0.91/1.12         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 0.91/1.12          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.91/1.12      inference('demod', [status(thm)], ['21', '22'])).
% 0.91/1.12  thf('118', plain,
% 0.91/1.12      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.91/1.12          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.91/1.12          | (r2_relset_1 @ X31 @ X32 @ X30 @ X33)
% 0.91/1.12          | ((X30) != (X33)))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.91/1.12  thf('119', plain,
% 0.91/1.12      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.91/1.12         ((r2_relset_1 @ X31 @ X32 @ X33 @ X33)
% 0.91/1.12          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.91/1.12      inference('simplify', [status(thm)], ['118'])).
% 0.91/1.12  thf('120', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['117', '119'])).
% 0.91/1.12  thf('121', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('122', plain,
% 0.91/1.12      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.91/1.12         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.91/1.12          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.91/1.12  thf('123', plain,
% 0.91/1.12      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.91/1.12      inference('sup-', [status(thm)], ['121', '122'])).
% 0.91/1.12  thf('124', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('125', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('126', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('127', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.91/1.12      inference('demod', [status(thm)],
% 0.91/1.12                ['116', '120', '123', '124', '125', '126'])).
% 0.91/1.12  thf('128', plain,
% 0.91/1.12      ((((sk_C) = (k2_funct_1 @ sk_D))
% 0.91/1.12        | ((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A)))),
% 0.91/1.12      inference('demod', [status(thm)], ['108', '127'])).
% 0.91/1.12  thf('129', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.91/1.12      inference('simplify', [status(thm)], ['128'])).
% 0.91/1.12  thf(t65_funct_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.12       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.91/1.12  thf('130', plain,
% 0.91/1.12      (![X20 : $i]:
% 0.91/1.12         (~ (v2_funct_1 @ X20)
% 0.91/1.12          | ((k2_funct_1 @ (k2_funct_1 @ X20)) = (X20))
% 0.91/1.12          | ~ (v1_funct_1 @ X20)
% 0.91/1.12          | ~ (v1_relat_1 @ X20))),
% 0.91/1.12      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.91/1.12  thf('131', plain,
% 0.91/1.12      ((((k2_funct_1 @ sk_C) = (sk_D))
% 0.91/1.12        | ~ (v1_relat_1 @ sk_D)
% 0.91/1.12        | ~ (v1_funct_1 @ sk_D)
% 0.91/1.12        | ~ (v2_funct_1 @ sk_D))),
% 0.91/1.12      inference('sup+', [status(thm)], ['129', '130'])).
% 0.91/1.12  thf('132', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.12      inference('sup-', [status(thm)], ['30', '31'])).
% 0.91/1.12  thf('133', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('134', plain, ((v2_funct_1 @ sk_D)),
% 0.91/1.12      inference('simplify', [status(thm)], ['104'])).
% 0.91/1.12  thf('135', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 0.91/1.12      inference('demod', [status(thm)], ['131', '132', '133', '134'])).
% 0.91/1.12  thf('136', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('137', plain, ($false),
% 0.91/1.12      inference('simplify_reflect-', [status(thm)], ['135', '136'])).
% 0.91/1.12  
% 0.91/1.12  % SZS output end Refutation
% 0.91/1.12  
% 0.91/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
