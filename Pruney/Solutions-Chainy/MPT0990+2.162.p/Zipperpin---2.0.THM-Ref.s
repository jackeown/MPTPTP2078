%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jC1FLSmGTv

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:23 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 473 expanded)
%              Number of leaves         :   45 ( 161 expanded)
%              Depth                    :   17
%              Number of atoms          : 1406 (10942 expanded)
%              Number of equality atoms :   88 ( 737 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
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
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X8 @ X9 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('27',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X8 @ X9 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf('30',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( r2_relset_1 @ X44 @ X44 @ ( k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46 ) @ ( k6_partfun1 @ X44 ) )
      | ( ( k2_relset_1 @ X45 @ X44 @ X46 )
        = X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','41','44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('61',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('63',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('71',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('72',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['62','69','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','48','53','54','59','73','74','79'])).

thf('81',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
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

thf('83',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('84',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('85',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('86',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('87',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('91',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['62','69','72'])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('94',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['84','87','88','89','90','91','92','93'])).

thf('95',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','95'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('97',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('98',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('100',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['94'])).

thf('102',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jC1FLSmGTv
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:48:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.98/2.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.98/2.19  % Solved by: fo/fo7.sh
% 1.98/2.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.98/2.19  % done 460 iterations in 1.733s
% 1.98/2.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.98/2.19  % SZS output start Refutation
% 1.98/2.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.98/2.19  thf(sk_A_type, type, sk_A: $i).
% 1.98/2.19  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.98/2.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.98/2.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.98/2.19  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.98/2.19  thf(sk_D_type, type, sk_D: $i).
% 1.98/2.19  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.98/2.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.98/2.19  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.98/2.19  thf(sk_C_type, type, sk_C: $i).
% 1.98/2.19  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.98/2.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.98/2.19  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.98/2.19  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.98/2.19  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.98/2.19  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.98/2.19  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.98/2.19  thf(sk_B_type, type, sk_B: $i).
% 1.98/2.19  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.98/2.19  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.98/2.19  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.98/2.19  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.98/2.19  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.98/2.19  thf(t36_funct_2, conjecture,
% 1.98/2.19    (![A:$i,B:$i,C:$i]:
% 1.98/2.19     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.98/2.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.98/2.19       ( ![D:$i]:
% 1.98/2.19         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.98/2.19             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.98/2.19           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.98/2.19               ( r2_relset_1 @
% 1.98/2.19                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.98/2.19                 ( k6_partfun1 @ A ) ) & 
% 1.98/2.19               ( v2_funct_1 @ C ) ) =>
% 1.98/2.19             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.98/2.19               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.98/2.19  thf(zf_stmt_0, negated_conjecture,
% 1.98/2.19    (~( ![A:$i,B:$i,C:$i]:
% 1.98/2.19        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.98/2.19            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.98/2.19          ( ![D:$i]:
% 1.98/2.19            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.98/2.19                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.98/2.19              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.98/2.19                  ( r2_relset_1 @
% 1.98/2.19                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.98/2.19                    ( k6_partfun1 @ A ) ) & 
% 1.98/2.19                  ( v2_funct_1 @ C ) ) =>
% 1.98/2.19                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.98/2.19                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.98/2.19    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.98/2.19  thf('0', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('1', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf(redefinition_k1_partfun1, axiom,
% 1.98/2.19    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.98/2.19     ( ( ( v1_funct_1 @ E ) & 
% 1.98/2.19         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.98/2.19         ( v1_funct_1 @ F ) & 
% 1.98/2.19         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.98/2.19       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.98/2.19  thf('2', plain,
% 1.98/2.19      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.98/2.19         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.98/2.19          | ~ (v1_funct_1 @ X36)
% 1.98/2.19          | ~ (v1_funct_1 @ X39)
% 1.98/2.19          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.98/2.19          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 1.98/2.19              = (k5_relat_1 @ X36 @ X39)))),
% 1.98/2.19      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.98/2.19  thf('3', plain,
% 1.98/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.98/2.19         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.98/2.19            = (k5_relat_1 @ sk_C @ X0))
% 1.98/2.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.98/2.19          | ~ (v1_funct_1 @ X0)
% 1.98/2.19          | ~ (v1_funct_1 @ sk_C))),
% 1.98/2.19      inference('sup-', [status(thm)], ['1', '2'])).
% 1.98/2.19  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('5', plain,
% 1.98/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.98/2.19         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.98/2.19            = (k5_relat_1 @ sk_C @ X0))
% 1.98/2.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.98/2.19          | ~ (v1_funct_1 @ X0))),
% 1.98/2.19      inference('demod', [status(thm)], ['3', '4'])).
% 1.98/2.19  thf('6', plain,
% 1.98/2.19      ((~ (v1_funct_1 @ sk_D)
% 1.98/2.19        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.98/2.19            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.98/2.19      inference('sup-', [status(thm)], ['0', '5'])).
% 1.98/2.19  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('8', plain,
% 1.98/2.19      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.98/2.19        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.98/2.19        (k6_partfun1 @ sk_A))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('9', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('10', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf(dt_k1_partfun1, axiom,
% 1.98/2.19    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.98/2.19     ( ( ( v1_funct_1 @ E ) & 
% 1.98/2.19         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.98/2.19         ( v1_funct_1 @ F ) & 
% 1.98/2.19         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.98/2.19       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.98/2.19         ( m1_subset_1 @
% 1.98/2.19           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.98/2.19           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.98/2.19  thf('11', plain,
% 1.98/2.19      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.98/2.19         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.98/2.19          | ~ (v1_funct_1 @ X30)
% 1.98/2.19          | ~ (v1_funct_1 @ X33)
% 1.98/2.19          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.98/2.19          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 1.98/2.19             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 1.98/2.19      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.98/2.19  thf('12', plain,
% 1.98/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.98/2.19         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.98/2.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.98/2.19          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.98/2.19          | ~ (v1_funct_1 @ X1)
% 1.98/2.19          | ~ (v1_funct_1 @ sk_C))),
% 1.98/2.19      inference('sup-', [status(thm)], ['10', '11'])).
% 1.98/2.19  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('14', plain,
% 1.98/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.98/2.19         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.98/2.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.98/2.19          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.98/2.19          | ~ (v1_funct_1 @ X1))),
% 1.98/2.19      inference('demod', [status(thm)], ['12', '13'])).
% 1.98/2.19  thf('15', plain,
% 1.98/2.19      ((~ (v1_funct_1 @ sk_D)
% 1.98/2.19        | (m1_subset_1 @ 
% 1.98/2.19           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.98/2.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.98/2.19      inference('sup-', [status(thm)], ['9', '14'])).
% 1.98/2.19  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('17', plain,
% 1.98/2.19      ((m1_subset_1 @ 
% 1.98/2.19        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.98/2.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.98/2.19      inference('demod', [status(thm)], ['15', '16'])).
% 1.98/2.19  thf(redefinition_r2_relset_1, axiom,
% 1.98/2.19    (![A:$i,B:$i,C:$i,D:$i]:
% 1.98/2.19     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.98/2.19         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.98/2.19       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.98/2.19  thf('18', plain,
% 1.98/2.19      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.98/2.19         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.98/2.19          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.98/2.19          | ((X17) = (X20))
% 1.98/2.19          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 1.98/2.19      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.98/2.19  thf('19', plain,
% 1.98/2.19      (![X0 : $i]:
% 1.98/2.19         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.98/2.19             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.98/2.19          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.98/2.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.98/2.19      inference('sup-', [status(thm)], ['17', '18'])).
% 1.98/2.19  thf('20', plain,
% 1.98/2.19      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.98/2.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.98/2.19        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.98/2.19            = (k6_partfun1 @ sk_A)))),
% 1.98/2.19      inference('sup-', [status(thm)], ['8', '19'])).
% 1.98/2.19  thf(t29_relset_1, axiom,
% 1.98/2.19    (![A:$i]:
% 1.98/2.19     ( m1_subset_1 @
% 1.98/2.19       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.98/2.19  thf('21', plain,
% 1.98/2.19      (![X21 : $i]:
% 1.98/2.19         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 1.98/2.19          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.98/2.19      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.98/2.19  thf(redefinition_k6_partfun1, axiom,
% 1.98/2.19    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.98/2.19  thf('22', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.98/2.19      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.98/2.19  thf('23', plain,
% 1.98/2.19      (![X21 : $i]:
% 1.98/2.19         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 1.98/2.19          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.98/2.19      inference('demod', [status(thm)], ['21', '22'])).
% 1.98/2.19  thf('24', plain,
% 1.98/2.19      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.98/2.19         = (k6_partfun1 @ sk_A))),
% 1.98/2.19      inference('demod', [status(thm)], ['20', '23'])).
% 1.98/2.19  thf('25', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.98/2.19      inference('demod', [status(thm)], ['6', '7', '24'])).
% 1.98/2.19  thf(t64_funct_1, axiom,
% 1.98/2.19    (![A:$i]:
% 1.98/2.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.98/2.19       ( ![B:$i]:
% 1.98/2.19         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.98/2.19           ( ( ( v2_funct_1 @ A ) & 
% 1.98/2.19               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.98/2.19               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.98/2.19             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.98/2.19  thf('26', plain,
% 1.98/2.19      (![X8 : $i, X9 : $i]:
% 1.98/2.19         (~ (v1_relat_1 @ X8)
% 1.98/2.19          | ~ (v1_funct_1 @ X8)
% 1.98/2.19          | ((X8) = (k2_funct_1 @ X9))
% 1.98/2.19          | ((k5_relat_1 @ X8 @ X9) != (k6_relat_1 @ (k2_relat_1 @ X9)))
% 1.98/2.19          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 1.98/2.19          | ~ (v2_funct_1 @ X9)
% 1.98/2.19          | ~ (v1_funct_1 @ X9)
% 1.98/2.19          | ~ (v1_relat_1 @ X9))),
% 1.98/2.19      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.98/2.19  thf('27', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.98/2.19      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.98/2.19  thf('28', plain,
% 1.98/2.19      (![X8 : $i, X9 : $i]:
% 1.98/2.19         (~ (v1_relat_1 @ X8)
% 1.98/2.19          | ~ (v1_funct_1 @ X8)
% 1.98/2.19          | ((X8) = (k2_funct_1 @ X9))
% 1.98/2.19          | ((k5_relat_1 @ X8 @ X9) != (k6_partfun1 @ (k2_relat_1 @ X9)))
% 1.98/2.19          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 1.98/2.19          | ~ (v2_funct_1 @ X9)
% 1.98/2.19          | ~ (v1_funct_1 @ X9)
% 1.98/2.19          | ~ (v1_relat_1 @ X9))),
% 1.98/2.19      inference('demod', [status(thm)], ['26', '27'])).
% 1.98/2.19  thf('29', plain,
% 1.98/2.19      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.98/2.19        | ~ (v1_relat_1 @ sk_D)
% 1.98/2.19        | ~ (v1_funct_1 @ sk_D)
% 1.98/2.19        | ~ (v2_funct_1 @ sk_D)
% 1.98/2.19        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.98/2.19        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.98/2.19        | ~ (v1_funct_1 @ sk_C)
% 1.98/2.19        | ~ (v1_relat_1 @ sk_C))),
% 1.98/2.19      inference('sup-', [status(thm)], ['25', '28'])).
% 1.98/2.19  thf('30', plain,
% 1.98/2.19      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.98/2.19         = (k6_partfun1 @ sk_A))),
% 1.98/2.19      inference('demod', [status(thm)], ['20', '23'])).
% 1.98/2.19  thf('31', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf(t24_funct_2, axiom,
% 1.98/2.19    (![A:$i,B:$i,C:$i]:
% 1.98/2.19     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.98/2.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.98/2.19       ( ![D:$i]:
% 1.98/2.19         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.98/2.19             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.98/2.19           ( ( r2_relset_1 @
% 1.98/2.19               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.98/2.19               ( k6_partfun1 @ B ) ) =>
% 1.98/2.19             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.98/2.19  thf('32', plain,
% 1.98/2.19      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.98/2.19         (~ (v1_funct_1 @ X43)
% 1.98/2.19          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 1.98/2.19          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 1.98/2.19          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 1.98/2.19               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 1.98/2.19               (k6_partfun1 @ X44))
% 1.98/2.19          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 1.98/2.19          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 1.98/2.19          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 1.98/2.19          | ~ (v1_funct_1 @ X46))),
% 1.98/2.19      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.98/2.19  thf('33', plain,
% 1.98/2.19      (![X0 : $i]:
% 1.98/2.19         (~ (v1_funct_1 @ X0)
% 1.98/2.19          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.98/2.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.98/2.19          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.98/2.19          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.98/2.19               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.98/2.19               (k6_partfun1 @ sk_A))
% 1.98/2.19          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.98/2.19          | ~ (v1_funct_1 @ sk_C))),
% 1.98/2.19      inference('sup-', [status(thm)], ['31', '32'])).
% 1.98/2.19  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('36', plain,
% 1.98/2.19      (![X0 : $i]:
% 1.98/2.19         (~ (v1_funct_1 @ X0)
% 1.98/2.19          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.98/2.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.98/2.19          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.98/2.19          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.98/2.19               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.98/2.19               (k6_partfun1 @ sk_A)))),
% 1.98/2.19      inference('demod', [status(thm)], ['33', '34', '35'])).
% 1.98/2.19  thf('37', plain,
% 1.98/2.19      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.98/2.19           (k6_partfun1 @ sk_A))
% 1.98/2.19        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.98/2.19        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.98/2.19        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.98/2.19        | ~ (v1_funct_1 @ sk_D))),
% 1.98/2.19      inference('sup-', [status(thm)], ['30', '36'])).
% 1.98/2.19  thf('38', plain,
% 1.98/2.19      (![X21 : $i]:
% 1.98/2.19         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 1.98/2.19          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.98/2.19      inference('demod', [status(thm)], ['21', '22'])).
% 1.98/2.19  thf('39', plain,
% 1.98/2.19      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.98/2.19         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.98/2.19          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.98/2.19          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 1.98/2.19          | ((X17) != (X20)))),
% 1.98/2.19      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.98/2.19  thf('40', plain,
% 1.98/2.19      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.98/2.19         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 1.98/2.19          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.98/2.19      inference('simplify', [status(thm)], ['39'])).
% 1.98/2.19  thf('41', plain,
% 1.98/2.19      (![X0 : $i]:
% 1.98/2.19         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.98/2.19      inference('sup-', [status(thm)], ['38', '40'])).
% 1.98/2.19  thf('42', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf(redefinition_k2_relset_1, axiom,
% 1.98/2.19    (![A:$i,B:$i,C:$i]:
% 1.98/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.98/2.19       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.98/2.19  thf('43', plain,
% 1.98/2.19      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.98/2.19         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.98/2.19          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.98/2.19      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.98/2.19  thf('44', plain,
% 1.98/2.19      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.98/2.19      inference('sup-', [status(thm)], ['42', '43'])).
% 1.98/2.19  thf('45', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.98/2.19      inference('demod', [status(thm)], ['37', '41', '44', '45', '46', '47'])).
% 1.98/2.19  thf('49', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf(cc2_relat_1, axiom,
% 1.98/2.19    (![A:$i]:
% 1.98/2.19     ( ( v1_relat_1 @ A ) =>
% 1.98/2.19       ( ![B:$i]:
% 1.98/2.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.98/2.20  thf('50', plain,
% 1.98/2.20      (![X0 : $i, X1 : $i]:
% 1.98/2.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.98/2.20          | (v1_relat_1 @ X0)
% 1.98/2.20          | ~ (v1_relat_1 @ X1))),
% 1.98/2.20      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.98/2.20  thf('51', plain,
% 1.98/2.20      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.98/2.20      inference('sup-', [status(thm)], ['49', '50'])).
% 1.98/2.20  thf(fc6_relat_1, axiom,
% 1.98/2.20    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.98/2.20  thf('52', plain,
% 1.98/2.20      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.98/2.20      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.98/2.20  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 1.98/2.20      inference('demod', [status(thm)], ['51', '52'])).
% 1.98/2.20  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.20  thf('55', plain,
% 1.98/2.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.20  thf('56', plain,
% 1.98/2.20      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.98/2.20         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.98/2.20          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.98/2.20      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.98/2.20  thf('57', plain,
% 1.98/2.20      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.98/2.20      inference('sup-', [status(thm)], ['55', '56'])).
% 1.98/2.20  thf('58', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.20  thf('59', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.98/2.20      inference('sup+', [status(thm)], ['57', '58'])).
% 1.98/2.20  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.20  thf(d1_funct_2, axiom,
% 1.98/2.20    (![A:$i,B:$i,C:$i]:
% 1.98/2.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.98/2.20       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.98/2.20           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.98/2.20             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.98/2.20         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.98/2.20           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.98/2.20             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.98/2.20  thf(zf_stmt_1, axiom,
% 1.98/2.20    (![C:$i,B:$i,A:$i]:
% 1.98/2.20     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.98/2.20       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.98/2.20  thf('61', plain,
% 1.98/2.20      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.98/2.20         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 1.98/2.20          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 1.98/2.20          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.98/2.20  thf('62', plain,
% 1.98/2.20      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 1.98/2.20        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 1.98/2.20      inference('sup-', [status(thm)], ['60', '61'])).
% 1.98/2.20  thf(zf_stmt_2, axiom,
% 1.98/2.20    (![B:$i,A:$i]:
% 1.98/2.20     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.98/2.20       ( zip_tseitin_0 @ B @ A ) ))).
% 1.98/2.20  thf('63', plain,
% 1.98/2.20      (![X22 : $i, X23 : $i]:
% 1.98/2.20         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.98/2.20  thf('64', plain,
% 1.98/2.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.20  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.98/2.20  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.98/2.20  thf(zf_stmt_5, axiom,
% 1.98/2.20    (![A:$i,B:$i,C:$i]:
% 1.98/2.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.98/2.20       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.98/2.20         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.98/2.20           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.98/2.20             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.98/2.20  thf('65', plain,
% 1.98/2.20      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.98/2.20         (~ (zip_tseitin_0 @ X27 @ X28)
% 1.98/2.20          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 1.98/2.20          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.98/2.20  thf('66', plain,
% 1.98/2.20      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 1.98/2.20      inference('sup-', [status(thm)], ['64', '65'])).
% 1.98/2.20  thf('67', plain,
% 1.98/2.20      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 1.98/2.20      inference('sup-', [status(thm)], ['63', '66'])).
% 1.98/2.20  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.20  thf('69', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 1.98/2.20      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 1.98/2.20  thf('70', plain,
% 1.98/2.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.20  thf(redefinition_k1_relset_1, axiom,
% 1.98/2.20    (![A:$i,B:$i,C:$i]:
% 1.98/2.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.98/2.20       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.98/2.20  thf('71', plain,
% 1.98/2.20      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.98/2.20         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 1.98/2.20          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.98/2.20      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.98/2.20  thf('72', plain,
% 1.98/2.20      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.98/2.20      inference('sup-', [status(thm)], ['70', '71'])).
% 1.98/2.20  thf('73', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.98/2.20      inference('demod', [status(thm)], ['62', '69', '72'])).
% 1.98/2.20  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.20  thf('75', plain,
% 1.98/2.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.20  thf('76', plain,
% 1.98/2.20      (![X0 : $i, X1 : $i]:
% 1.98/2.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.98/2.20          | (v1_relat_1 @ X0)
% 1.98/2.20          | ~ (v1_relat_1 @ X1))),
% 1.98/2.20      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.98/2.20  thf('77', plain,
% 1.98/2.20      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.98/2.20      inference('sup-', [status(thm)], ['75', '76'])).
% 1.98/2.20  thf('78', plain,
% 1.98/2.20      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.98/2.20      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.98/2.20  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 1.98/2.20      inference('demod', [status(thm)], ['77', '78'])).
% 1.98/2.20  thf('80', plain,
% 1.98/2.20      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 1.98/2.20        | ~ (v2_funct_1 @ sk_D)
% 1.98/2.20        | ((sk_B) != (sk_B))
% 1.98/2.20        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.98/2.20      inference('demod', [status(thm)],
% 1.98/2.20                ['29', '48', '53', '54', '59', '73', '74', '79'])).
% 1.98/2.20  thf('81', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.98/2.20      inference('simplify', [status(thm)], ['80'])).
% 1.98/2.20  thf('82', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.98/2.20      inference('demod', [status(thm)], ['6', '7', '24'])).
% 1.98/2.20  thf(t48_funct_1, axiom,
% 1.98/2.20    (![A:$i]:
% 1.98/2.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.98/2.20       ( ![B:$i]:
% 1.98/2.20         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.98/2.20           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.98/2.20               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.98/2.20             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.98/2.20  thf('83', plain,
% 1.98/2.20      (![X6 : $i, X7 : $i]:
% 1.98/2.20         (~ (v1_relat_1 @ X6)
% 1.98/2.20          | ~ (v1_funct_1 @ X6)
% 1.98/2.20          | (v2_funct_1 @ X7)
% 1.98/2.20          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 1.98/2.20          | ~ (v2_funct_1 @ (k5_relat_1 @ X6 @ X7))
% 1.98/2.20          | ~ (v1_funct_1 @ X7)
% 1.98/2.20          | ~ (v1_relat_1 @ X7))),
% 1.98/2.20      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.98/2.20  thf('84', plain,
% 1.98/2.20      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.98/2.20        | ~ (v1_relat_1 @ sk_D)
% 1.98/2.20        | ~ (v1_funct_1 @ sk_D)
% 1.98/2.20        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.98/2.20        | (v2_funct_1 @ sk_D)
% 1.98/2.20        | ~ (v1_funct_1 @ sk_C)
% 1.98/2.20        | ~ (v1_relat_1 @ sk_C))),
% 1.98/2.20      inference('sup-', [status(thm)], ['82', '83'])).
% 1.98/2.20  thf(fc4_funct_1, axiom,
% 1.98/2.20    (![A:$i]:
% 1.98/2.20     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.98/2.20       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.98/2.20  thf('85', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 1.98/2.20      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.98/2.20  thf('86', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.98/2.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.98/2.20  thf('87', plain, (![X5 : $i]: (v2_funct_1 @ (k6_partfun1 @ X5))),
% 1.98/2.20      inference('demod', [status(thm)], ['85', '86'])).
% 1.98/2.20  thf('88', plain, ((v1_relat_1 @ sk_D)),
% 1.98/2.20      inference('demod', [status(thm)], ['51', '52'])).
% 1.98/2.20  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.20  thf('90', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.98/2.20      inference('sup+', [status(thm)], ['57', '58'])).
% 1.98/2.20  thf('91', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.98/2.20      inference('demod', [status(thm)], ['62', '69', '72'])).
% 1.98/2.20  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.20  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 1.98/2.20      inference('demod', [status(thm)], ['77', '78'])).
% 1.98/2.20  thf('94', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 1.98/2.20      inference('demod', [status(thm)],
% 1.98/2.20                ['84', '87', '88', '89', '90', '91', '92', '93'])).
% 1.98/2.20  thf('95', plain, ((v2_funct_1 @ sk_D)),
% 1.98/2.20      inference('simplify', [status(thm)], ['94'])).
% 1.98/2.20  thf('96', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.98/2.20      inference('demod', [status(thm)], ['81', '95'])).
% 1.98/2.20  thf(t65_funct_1, axiom,
% 1.98/2.20    (![A:$i]:
% 1.98/2.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.98/2.20       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 1.98/2.20  thf('97', plain,
% 1.98/2.20      (![X10 : $i]:
% 1.98/2.20         (~ (v2_funct_1 @ X10)
% 1.98/2.20          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 1.98/2.20          | ~ (v1_funct_1 @ X10)
% 1.98/2.20          | ~ (v1_relat_1 @ X10))),
% 1.98/2.20      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.98/2.20  thf('98', plain,
% 1.98/2.20      ((((k2_funct_1 @ sk_C) = (sk_D))
% 1.98/2.20        | ~ (v1_relat_1 @ sk_D)
% 1.98/2.20        | ~ (v1_funct_1 @ sk_D)
% 1.98/2.20        | ~ (v2_funct_1 @ sk_D))),
% 1.98/2.20      inference('sup+', [status(thm)], ['96', '97'])).
% 1.98/2.20  thf('99', plain, ((v1_relat_1 @ sk_D)),
% 1.98/2.20      inference('demod', [status(thm)], ['51', '52'])).
% 1.98/2.20  thf('100', plain, ((v1_funct_1 @ sk_D)),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.20  thf('101', plain, ((v2_funct_1 @ sk_D)),
% 1.98/2.20      inference('simplify', [status(thm)], ['94'])).
% 1.98/2.20  thf('102', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 1.98/2.20      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 1.98/2.20  thf('103', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.98/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.20  thf('104', plain, ($false),
% 1.98/2.20      inference('simplify_reflect-', [status(thm)], ['102', '103'])).
% 1.98/2.20  
% 1.98/2.20  % SZS output end Refutation
% 1.98/2.20  
% 1.98/2.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
