%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4XYYQ62EDm

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:04 EST 2020

% Result     : Theorem 10.25s
% Output     : Refutation 10.25s
% Verified   : 
% Statistics : Number of formulae       :  332 ( 962 expanded)
%              Number of leaves         :   58 ( 313 expanded)
%              Depth                    :   28
%              Number of atoms          : 3337 (20092 expanded)
%              Number of equality atoms :  223 (1390 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( X63 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_funct_2 @ X64 @ X65 @ X63 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X63 ) ) )
      | ( ( k5_relat_1 @ X64 @ ( k2_funct_1 @ X64 ) )
        = ( k6_partfun1 @ X65 ) )
      | ~ ( v2_funct_1 @ X64 )
      | ( ( k2_relset_1 @ X65 @ X63 @ X64 )
       != X63 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('2',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','5','6','7'])).

thf('9',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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

thf('13',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( r2_relset_1 @ X51 @ X51 @ ( k1_partfun1 @ X51 @ X52 @ X52 @ X51 @ X50 @ X53 ) @ ( k6_partfun1 @ X51 ) )
      | ( ( k2_relset_1 @ X52 @ X51 @ X53 )
        = X51 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A_1 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
      = sk_A_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,
    ( ( sk_A_1 != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','23'])).

thf('25',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('28',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('37',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('40',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('47',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('48',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( X31 = X34 )
      | ~ ( r2_relset_1 @ X32 @ X33 @ X31 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['37','49'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('51',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('52',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['34','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ! [E: $i] :
          ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
            & ( v1_funct_2 @ E @ B @ C )
            & ( v1_funct_1 @ E ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) )
           => ( ( ( v2_funct_1 @ E )
                & ( v2_funct_1 @ D ) )
              | ( ( B != k1_xboole_0 )
                & ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_1 @ C @ B )
     => ( ( C = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i] :
      ( ( zip_tseitin_0 @ E @ D )
     => ( ( v2_funct_1 @ D )
        & ( v2_funct_1 @ E ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
              & ( ( k2_relset_1 @ A @ B @ D )
                = B ) )
           => ( ( zip_tseitin_1 @ C @ B )
              | ( zip_tseitin_0 @ E @ D ) ) ) ) ) )).

thf('55',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X60 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ( zip_tseitin_0 @ X58 @ X61 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X62 @ X59 @ X59 @ X60 @ X61 @ X58 ) )
      | ( zip_tseitin_1 @ X60 @ X59 )
      | ( ( k2_relset_1 @ X62 @ X59 @ X61 )
       != X59 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X59 ) ) )
      | ~ ( v1_funct_2 @ X61 @ X62 @ X59 )
      | ~ ( v1_funct_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A_1 ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('61',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('62',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('63',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['60','63','64','65','66','67'])).

thf('69',plain,
    ( ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X56: $i,X57: $i] :
      ( ( X56 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('71',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X54: $i,X55: $i] :
      ( ( v2_funct_1 @ X55 )
      | ~ ( zip_tseitin_0 @ X55 @ X54 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('75',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','75'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('77',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k1_relat_1 @ X23 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('78',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k10_relat_1 @ X20 @ X21 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X20 ) @ X21 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('79',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('80',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('81',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('82',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('83',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X16 ) ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('84',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k9_relat_1 @ X8 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('86',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('87',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('88',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('90',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','88','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('101',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('102',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('103',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('104',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('105',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('106',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( ( k5_relat_1 @ X17 @ ( k6_relat_1 @ X18 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('107',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('108',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( ( k5_relat_1 @ X17 @ ( k6_partfun1 @ X18 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['99','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('116',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k5_relat_1 @ X24 @ ( k2_funct_1 @ X24 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('117',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('118',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k5_relat_1 @ X24 @ ( k2_funct_1 @ X24 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('119',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['115','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['114','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k9_relat_1 @ X8 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('131',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('132',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','133'])).

thf('135',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('136',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('137',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X16 ) ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k9_relat_1 @ X8 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_partfun1 @ X0 ) )
        = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('145',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('146',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('147',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('148',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['143','144','145','146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['134','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['76','150'])).

thf('152',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('153',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('155',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('158',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['151','152','155','156','157'])).

thf('159',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X16 ) ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('160',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('162',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('163',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X24 ) @ X24 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('164',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('165',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X24 ) @ X24 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['162','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['161','170'])).

thf('172',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('174',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('178',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k10_relat_1 @ X20 @ X21 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X20 ) @ X21 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('179',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('180',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['174','175'])).

thf('181',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('182',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('183',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X16 ) ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['181','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['180','186'])).

thf('188',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('190',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['187','190','191','192'])).

thf('194',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k9_relat_1 @ X8 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('195',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('197',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('198',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['179','198'])).

thf('200',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['188','189'])).

thf('201',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['199','200','201'])).

thf('203',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k10_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['178','202'])).

thf('204',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['174','175'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('205',plain,(
    ! [X10: $i] :
      ( ( ( k10_relat_1 @ X10 @ ( k2_relat_1 @ X10 ) )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('206',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['204','205'])).

thf('207',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['188','189'])).

thf('208',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['188','189'])).

thf('210',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['203','208','209','210','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('214',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['212','213'])).

thf('215',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['177','214'])).

thf('216',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['188','189'])).

thf('217',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( X63 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_funct_2 @ X64 @ X65 @ X63 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X63 ) ) )
      | ( ( k5_relat_1 @ X64 @ ( k2_funct_1 @ X64 ) )
        = ( k6_partfun1 @ X65 ) )
      | ~ ( v2_funct_1 @ X64 )
      | ( ( k2_relset_1 @ X65 @ X63 @ X64 )
       != X63 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('221',plain,
    ( ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('225',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k5_relat_1 @ X24 @ ( k2_funct_1 @ X24 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('226',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['174','175'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('228',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['226','227'])).

thf('229',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['188','189'])).

thf('230',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X16 ) ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('232',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['230','236'])).

thf('238',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['228','229'])).

thf('239',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['188','189'])).

thf('240',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('241',plain,
    ( sk_C
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['237','238','239','240'])).

thf('242',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('245',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['188','189'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['243','244','245'])).

thf('247',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['225','246'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('249',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['188','189'])).

thf('250',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['247','248','249','250','251'])).

thf('253',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['224','252'])).

thf('254',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['188','189'])).

thf('255',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('257',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ( sk_B != sk_B )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['221','222','223','256','257','258'])).

thf('260',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['259'])).

thf('261',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference('simplify_reflect-',[status(thm)],['260','261'])).

thf('263',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A_1 ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['218','262'])).

thf('264',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['188','189'])).

thf('265',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['153','154'])).

thf('268',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['171','176','263','264','265','266','267'])).

thf('269',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['153','154'])).

thf('270',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['160','268','269'])).

thf('271',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['270','271'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4XYYQ62EDm
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 10.25/10.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.25/10.46  % Solved by: fo/fo7.sh
% 10.25/10.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.25/10.46  % done 6065 iterations in 10.001s
% 10.25/10.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.25/10.46  % SZS output start Refutation
% 10.25/10.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.25/10.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 10.25/10.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 10.25/10.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 10.25/10.46  thf(sk_A_1_type, type, sk_A_1: $i).
% 10.25/10.46  thf(sk_D_type, type, sk_D: $i).
% 10.25/10.46  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 10.25/10.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.25/10.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 10.25/10.46  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 10.25/10.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 10.25/10.46  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 10.25/10.46  thf(sk_B_type, type, sk_B: $i).
% 10.25/10.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.25/10.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 10.25/10.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.25/10.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 10.25/10.46  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 10.25/10.46  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 10.25/10.46  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 10.25/10.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.25/10.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 10.25/10.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.25/10.46  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 10.25/10.46  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 10.25/10.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 10.25/10.46  thf(sk_C_type, type, sk_C: $i).
% 10.25/10.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.25/10.46  thf(t36_funct_2, conjecture,
% 10.25/10.46    (![A:$i,B:$i,C:$i]:
% 10.25/10.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.25/10.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.25/10.46       ( ![D:$i]:
% 10.25/10.46         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 10.25/10.46             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 10.25/10.46           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 10.25/10.46               ( r2_relset_1 @
% 10.25/10.46                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 10.25/10.46                 ( k6_partfun1 @ A ) ) & 
% 10.25/10.46               ( v2_funct_1 @ C ) ) =>
% 10.25/10.46             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 10.25/10.46               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 10.25/10.46  thf(zf_stmt_0, negated_conjecture,
% 10.25/10.46    (~( ![A:$i,B:$i,C:$i]:
% 10.25/10.46        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.25/10.46            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.25/10.46          ( ![D:$i]:
% 10.25/10.46            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 10.25/10.46                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 10.25/10.46              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 10.25/10.46                  ( r2_relset_1 @
% 10.25/10.46                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 10.25/10.46                    ( k6_partfun1 @ A ) ) & 
% 10.25/10.46                  ( v2_funct_1 @ C ) ) =>
% 10.25/10.46                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 10.25/10.46                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 10.25/10.46    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 10.25/10.46  thf('0', plain,
% 10.25/10.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf(t35_funct_2, axiom,
% 10.25/10.46    (![A:$i,B:$i,C:$i]:
% 10.25/10.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.25/10.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.25/10.46       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 10.25/10.46         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 10.25/10.46           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 10.25/10.46             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 10.25/10.46  thf('1', plain,
% 10.25/10.46      (![X63 : $i, X64 : $i, X65 : $i]:
% 10.25/10.46         (((X63) = (k1_xboole_0))
% 10.25/10.46          | ~ (v1_funct_1 @ X64)
% 10.25/10.46          | ~ (v1_funct_2 @ X64 @ X65 @ X63)
% 10.25/10.46          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X63)))
% 10.25/10.46          | ((k5_relat_1 @ X64 @ (k2_funct_1 @ X64)) = (k6_partfun1 @ X65))
% 10.25/10.46          | ~ (v2_funct_1 @ X64)
% 10.25/10.46          | ((k2_relset_1 @ X65 @ X63 @ X64) != (X63)))),
% 10.25/10.46      inference('cnf', [status(esa)], [t35_funct_2])).
% 10.25/10.46  thf('2', plain,
% 10.25/10.46      ((((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) != (sk_A_1))
% 10.25/10.46        | ~ (v2_funct_1 @ sk_D)
% 10.25/10.46        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 10.25/10.46        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 10.25/10.46        | ~ (v1_funct_1 @ sk_D)
% 10.25/10.46        | ((sk_A_1) = (k1_xboole_0)))),
% 10.25/10.46      inference('sup-', [status(thm)], ['0', '1'])).
% 10.25/10.46  thf('3', plain,
% 10.25/10.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf(redefinition_k2_relset_1, axiom,
% 10.25/10.46    (![A:$i,B:$i,C:$i]:
% 10.25/10.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.25/10.46       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 10.25/10.46  thf('4', plain,
% 10.25/10.46      (![X28 : $i, X29 : $i, X30 : $i]:
% 10.25/10.46         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 10.25/10.46          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 10.25/10.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 10.25/10.46  thf('5', plain,
% 10.25/10.46      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 10.25/10.46      inference('sup-', [status(thm)], ['3', '4'])).
% 10.25/10.46  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('8', plain,
% 10.25/10.46      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 10.25/10.46        | ~ (v2_funct_1 @ sk_D)
% 10.25/10.46        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 10.25/10.46        | ((sk_A_1) = (k1_xboole_0)))),
% 10.25/10.46      inference('demod', [status(thm)], ['2', '5', '6', '7'])).
% 10.25/10.46  thf('9', plain, (((sk_A_1) != (k1_xboole_0))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('10', plain,
% 10.25/10.46      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 10.25/10.46        | ~ (v2_funct_1 @ sk_D)
% 10.25/10.46        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 10.25/10.46      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 10.25/10.46  thf('11', plain,
% 10.25/10.46      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 10.25/10.46        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 10.25/10.46        (k6_partfun1 @ sk_A_1))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('12', plain,
% 10.25/10.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf(t24_funct_2, axiom,
% 10.25/10.46    (![A:$i,B:$i,C:$i]:
% 10.25/10.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.25/10.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.25/10.46       ( ![D:$i]:
% 10.25/10.46         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 10.25/10.46             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 10.25/10.46           ( ( r2_relset_1 @
% 10.25/10.46               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 10.25/10.46               ( k6_partfun1 @ B ) ) =>
% 10.25/10.46             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 10.25/10.46  thf('13', plain,
% 10.25/10.46      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 10.25/10.46         (~ (v1_funct_1 @ X50)
% 10.25/10.46          | ~ (v1_funct_2 @ X50 @ X51 @ X52)
% 10.25/10.46          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 10.25/10.46          | ~ (r2_relset_1 @ X51 @ X51 @ 
% 10.25/10.46               (k1_partfun1 @ X51 @ X52 @ X52 @ X51 @ X50 @ X53) @ 
% 10.25/10.46               (k6_partfun1 @ X51))
% 10.25/10.46          | ((k2_relset_1 @ X52 @ X51 @ X53) = (X51))
% 10.25/10.46          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 10.25/10.46          | ~ (v1_funct_2 @ X53 @ X52 @ X51)
% 10.25/10.46          | ~ (v1_funct_1 @ X53))),
% 10.25/10.46      inference('cnf', [status(esa)], [t24_funct_2])).
% 10.25/10.46  thf('14', plain,
% 10.25/10.46      (![X0 : $i]:
% 10.25/10.46         (~ (v1_funct_1 @ X0)
% 10.25/10.46          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 10.25/10.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 10.25/10.46          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 10.25/10.46          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 10.25/10.46               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 10.25/10.46               (k6_partfun1 @ sk_A_1))
% 10.25/10.46          | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 10.25/10.46          | ~ (v1_funct_1 @ sk_C))),
% 10.25/10.46      inference('sup-', [status(thm)], ['12', '13'])).
% 10.25/10.46  thf('15', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('17', plain,
% 10.25/10.46      (![X0 : $i]:
% 10.25/10.46         (~ (v1_funct_1 @ X0)
% 10.25/10.46          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 10.25/10.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 10.25/10.46          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 10.25/10.46          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 10.25/10.46               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 10.25/10.46               (k6_partfun1 @ sk_A_1)))),
% 10.25/10.46      inference('demod', [status(thm)], ['14', '15', '16'])).
% 10.25/10.46  thf('18', plain,
% 10.25/10.46      ((((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (sk_A_1))
% 10.25/10.46        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 10.25/10.46        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 10.25/10.46        | ~ (v1_funct_1 @ sk_D))),
% 10.25/10.46      inference('sup-', [status(thm)], ['11', '17'])).
% 10.25/10.46  thf('19', plain,
% 10.25/10.46      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 10.25/10.46      inference('sup-', [status(thm)], ['3', '4'])).
% 10.25/10.46  thf('20', plain,
% 10.25/10.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('23', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 10.25/10.46      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 10.25/10.46  thf('24', plain,
% 10.25/10.46      ((((sk_A_1) != (sk_A_1))
% 10.25/10.46        | ~ (v2_funct_1 @ sk_D)
% 10.25/10.46        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 10.25/10.46      inference('demod', [status(thm)], ['10', '23'])).
% 10.25/10.46  thf('25', plain,
% 10.25/10.46      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 10.25/10.46        | ~ (v2_funct_1 @ sk_D))),
% 10.25/10.46      inference('simplify', [status(thm)], ['24'])).
% 10.25/10.46  thf('26', plain,
% 10.25/10.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('27', plain,
% 10.25/10.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf(redefinition_k1_partfun1, axiom,
% 10.25/10.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.25/10.46     ( ( ( v1_funct_1 @ E ) & 
% 10.25/10.46         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.25/10.46         ( v1_funct_1 @ F ) & 
% 10.25/10.46         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 10.25/10.46       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 10.25/10.46  thf('28', plain,
% 10.25/10.46      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 10.25/10.46         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 10.25/10.46          | ~ (v1_funct_1 @ X43)
% 10.25/10.46          | ~ (v1_funct_1 @ X46)
% 10.25/10.46          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 10.25/10.46          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 10.25/10.46              = (k5_relat_1 @ X43 @ X46)))),
% 10.25/10.46      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 10.25/10.46  thf('29', plain,
% 10.25/10.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.25/10.46         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 10.25/10.46            = (k5_relat_1 @ sk_C @ X0))
% 10.25/10.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.25/10.46          | ~ (v1_funct_1 @ X0)
% 10.25/10.46          | ~ (v1_funct_1 @ sk_C))),
% 10.25/10.46      inference('sup-', [status(thm)], ['27', '28'])).
% 10.25/10.46  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('31', plain,
% 10.25/10.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.25/10.46         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 10.25/10.46            = (k5_relat_1 @ sk_C @ X0))
% 10.25/10.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.25/10.46          | ~ (v1_funct_1 @ X0))),
% 10.25/10.46      inference('demod', [status(thm)], ['29', '30'])).
% 10.25/10.46  thf('32', plain,
% 10.25/10.46      ((~ (v1_funct_1 @ sk_D)
% 10.25/10.46        | ((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 10.25/10.46            = (k5_relat_1 @ sk_C @ sk_D)))),
% 10.25/10.46      inference('sup-', [status(thm)], ['26', '31'])).
% 10.25/10.46  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('34', plain,
% 10.25/10.46      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 10.25/10.46         = (k5_relat_1 @ sk_C @ sk_D))),
% 10.25/10.46      inference('demod', [status(thm)], ['32', '33'])).
% 10.25/10.46  thf('35', plain,
% 10.25/10.46      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 10.25/10.46        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 10.25/10.46        (k6_partfun1 @ sk_A_1))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('36', plain,
% 10.25/10.46      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 10.25/10.46         = (k5_relat_1 @ sk_C @ sk_D))),
% 10.25/10.46      inference('demod', [status(thm)], ['32', '33'])).
% 10.25/10.46  thf('37', plain,
% 10.25/10.46      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 10.25/10.46        (k6_partfun1 @ sk_A_1))),
% 10.25/10.46      inference('demod', [status(thm)], ['35', '36'])).
% 10.25/10.46  thf('38', plain,
% 10.25/10.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('39', plain,
% 10.25/10.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf(dt_k1_partfun1, axiom,
% 10.25/10.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.25/10.46     ( ( ( v1_funct_1 @ E ) & 
% 10.25/10.46         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.25/10.46         ( v1_funct_1 @ F ) & 
% 10.25/10.46         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 10.25/10.46       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 10.25/10.46         ( m1_subset_1 @
% 10.25/10.46           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 10.25/10.46           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 10.25/10.46  thf('40', plain,
% 10.25/10.46      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 10.25/10.46         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 10.25/10.46          | ~ (v1_funct_1 @ X35)
% 10.25/10.46          | ~ (v1_funct_1 @ X38)
% 10.25/10.46          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 10.25/10.46          | (m1_subset_1 @ (k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38) @ 
% 10.25/10.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X40))))),
% 10.25/10.46      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 10.25/10.46  thf('41', plain,
% 10.25/10.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.25/10.46         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 10.25/10.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 10.25/10.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 10.25/10.46          | ~ (v1_funct_1 @ X1)
% 10.25/10.46          | ~ (v1_funct_1 @ sk_C))),
% 10.25/10.46      inference('sup-', [status(thm)], ['39', '40'])).
% 10.25/10.46  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('43', plain,
% 10.25/10.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.25/10.46         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 10.25/10.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 10.25/10.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 10.25/10.46          | ~ (v1_funct_1 @ X1))),
% 10.25/10.46      inference('demod', [status(thm)], ['41', '42'])).
% 10.25/10.46  thf('44', plain,
% 10.25/10.46      ((~ (v1_funct_1 @ sk_D)
% 10.25/10.46        | (m1_subset_1 @ 
% 10.25/10.46           (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 10.25/10.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 10.25/10.46      inference('sup-', [status(thm)], ['38', '43'])).
% 10.25/10.46  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('46', plain,
% 10.25/10.46      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 10.25/10.46         = (k5_relat_1 @ sk_C @ sk_D))),
% 10.25/10.46      inference('demod', [status(thm)], ['32', '33'])).
% 10.25/10.46  thf('47', plain,
% 10.25/10.46      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 10.25/10.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))),
% 10.25/10.46      inference('demod', [status(thm)], ['44', '45', '46'])).
% 10.25/10.46  thf(redefinition_r2_relset_1, axiom,
% 10.25/10.46    (![A:$i,B:$i,C:$i,D:$i]:
% 10.25/10.46     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.25/10.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.25/10.46       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 10.25/10.46  thf('48', plain,
% 10.25/10.46      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 10.25/10.46         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 10.25/10.46          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 10.25/10.46          | ((X31) = (X34))
% 10.25/10.46          | ~ (r2_relset_1 @ X32 @ X33 @ X31 @ X34))),
% 10.25/10.46      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 10.25/10.46  thf('49', plain,
% 10.25/10.46      (![X0 : $i]:
% 10.25/10.46         (~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 10.25/10.46          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 10.25/10.46          | ~ (m1_subset_1 @ X0 @ 
% 10.25/10.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 10.25/10.46      inference('sup-', [status(thm)], ['47', '48'])).
% 10.25/10.46  thf('50', plain,
% 10.25/10.46      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A_1) @ 
% 10.25/10.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))
% 10.25/10.46        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1)))),
% 10.25/10.46      inference('sup-', [status(thm)], ['37', '49'])).
% 10.25/10.46  thf(dt_k6_partfun1, axiom,
% 10.25/10.46    (![A:$i]:
% 10.25/10.46     ( ( m1_subset_1 @
% 10.25/10.46         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 10.25/10.46       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 10.25/10.46  thf('51', plain,
% 10.25/10.46      (![X42 : $i]:
% 10.25/10.46         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 10.25/10.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 10.25/10.46      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 10.25/10.46  thf('52', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1))),
% 10.25/10.46      inference('demod', [status(thm)], ['50', '51'])).
% 10.25/10.46  thf('53', plain,
% 10.25/10.46      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 10.25/10.46         = (k6_partfun1 @ sk_A_1))),
% 10.25/10.46      inference('demod', [status(thm)], ['34', '52'])).
% 10.25/10.46  thf('54', plain,
% 10.25/10.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf(t30_funct_2, axiom,
% 10.25/10.46    (![A:$i,B:$i,C:$i,D:$i]:
% 10.25/10.46     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.25/10.46         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 10.25/10.46       ( ![E:$i]:
% 10.25/10.46         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 10.25/10.46             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 10.25/10.46           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 10.25/10.46               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 10.25/10.46             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 10.25/10.46               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 10.25/10.46  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 10.25/10.46  thf(zf_stmt_2, axiom,
% 10.25/10.46    (![C:$i,B:$i]:
% 10.25/10.46     ( ( zip_tseitin_1 @ C @ B ) =>
% 10.25/10.46       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 10.25/10.46  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 10.25/10.46  thf(zf_stmt_4, axiom,
% 10.25/10.46    (![E:$i,D:$i]:
% 10.25/10.46     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 10.25/10.46  thf(zf_stmt_5, axiom,
% 10.25/10.46    (![A:$i,B:$i,C:$i,D:$i]:
% 10.25/10.46     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.25/10.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.25/10.46       ( ![E:$i]:
% 10.25/10.46         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 10.25/10.46             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 10.25/10.46           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 10.25/10.46               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 10.25/10.46             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 10.25/10.46  thf('55', plain,
% 10.25/10.46      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 10.25/10.46         (~ (v1_funct_1 @ X58)
% 10.25/10.46          | ~ (v1_funct_2 @ X58 @ X59 @ X60)
% 10.25/10.46          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 10.25/10.46          | (zip_tseitin_0 @ X58 @ X61)
% 10.25/10.46          | ~ (v2_funct_1 @ (k1_partfun1 @ X62 @ X59 @ X59 @ X60 @ X61 @ X58))
% 10.25/10.46          | (zip_tseitin_1 @ X60 @ X59)
% 10.25/10.46          | ((k2_relset_1 @ X62 @ X59 @ X61) != (X59))
% 10.25/10.46          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X59)))
% 10.25/10.46          | ~ (v1_funct_2 @ X61 @ X62 @ X59)
% 10.25/10.46          | ~ (v1_funct_1 @ X61))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.25/10.46  thf('56', plain,
% 10.25/10.46      (![X0 : $i, X1 : $i]:
% 10.25/10.46         (~ (v1_funct_1 @ X0)
% 10.25/10.46          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 10.25/10.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 10.25/10.46          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 10.25/10.46          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 10.25/10.46          | ~ (v2_funct_1 @ 
% 10.25/10.46               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 10.25/10.46          | (zip_tseitin_0 @ sk_D @ X0)
% 10.25/10.46          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 10.25/10.46          | ~ (v1_funct_1 @ sk_D))),
% 10.25/10.46      inference('sup-', [status(thm)], ['54', '55'])).
% 10.25/10.46  thf('57', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('58', plain, ((v1_funct_1 @ sk_D)),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('59', plain,
% 10.25/10.46      (![X0 : $i, X1 : $i]:
% 10.25/10.46         (~ (v1_funct_1 @ X0)
% 10.25/10.46          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 10.25/10.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 10.25/10.46          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 10.25/10.46          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 10.25/10.46          | ~ (v2_funct_1 @ 
% 10.25/10.46               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 10.25/10.46          | (zip_tseitin_0 @ sk_D @ X0))),
% 10.25/10.46      inference('demod', [status(thm)], ['56', '57', '58'])).
% 10.25/10.46  thf('60', plain,
% 10.25/10.46      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A_1))
% 10.25/10.46        | (zip_tseitin_0 @ sk_D @ sk_C)
% 10.25/10.46        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 10.25/10.46        | ((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 10.25/10.46        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 10.25/10.46        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 10.25/10.46        | ~ (v1_funct_1 @ sk_C))),
% 10.25/10.46      inference('sup-', [status(thm)], ['53', '59'])).
% 10.25/10.46  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 10.25/10.46  thf('61', plain, (![X22 : $i]: (v2_funct_1 @ (k6_relat_1 @ X22))),
% 10.25/10.46      inference('cnf', [status(esa)], [t52_funct_1])).
% 10.25/10.46  thf(redefinition_k6_partfun1, axiom,
% 10.25/10.46    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 10.25/10.46  thf('62', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 10.25/10.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.25/10.46  thf('63', plain, (![X22 : $i]: (v2_funct_1 @ (k6_partfun1 @ X22))),
% 10.25/10.46      inference('demod', [status(thm)], ['61', '62'])).
% 10.25/10.46  thf('64', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('65', plain,
% 10.25/10.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('66', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('68', plain,
% 10.25/10.46      (((zip_tseitin_0 @ sk_D @ sk_C)
% 10.25/10.46        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 10.25/10.46        | ((sk_B) != (sk_B)))),
% 10.25/10.46      inference('demod', [status(thm)], ['60', '63', '64', '65', '66', '67'])).
% 10.25/10.46  thf('69', plain,
% 10.25/10.46      (((zip_tseitin_1 @ sk_A_1 @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 10.25/10.46      inference('simplify', [status(thm)], ['68'])).
% 10.25/10.46  thf('70', plain,
% 10.25/10.46      (![X56 : $i, X57 : $i]:
% 10.25/10.46         (((X56) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X56 @ X57))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 10.25/10.46  thf('71', plain,
% 10.25/10.46      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A_1) = (k1_xboole_0)))),
% 10.25/10.46      inference('sup-', [status(thm)], ['69', '70'])).
% 10.25/10.46  thf('72', plain, (((sk_A_1) != (k1_xboole_0))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.46  thf('73', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 10.25/10.46      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 10.25/10.46  thf('74', plain,
% 10.25/10.46      (![X54 : $i, X55 : $i]:
% 10.25/10.46         ((v2_funct_1 @ X55) | ~ (zip_tseitin_0 @ X55 @ X54))),
% 10.25/10.46      inference('cnf', [status(esa)], [zf_stmt_4])).
% 10.25/10.46  thf('75', plain, ((v2_funct_1 @ sk_D)),
% 10.25/10.46      inference('sup-', [status(thm)], ['73', '74'])).
% 10.25/10.46  thf('76', plain,
% 10.25/10.46      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 10.25/10.46      inference('demod', [status(thm)], ['25', '75'])).
% 10.25/10.46  thf(t55_funct_1, axiom,
% 10.25/10.46    (![A:$i]:
% 10.25/10.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 10.25/10.46       ( ( v2_funct_1 @ A ) =>
% 10.25/10.46         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 10.25/10.46           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 10.25/10.46  thf('77', plain,
% 10.25/10.46      (![X23 : $i]:
% 10.25/10.46         (~ (v2_funct_1 @ X23)
% 10.25/10.46          | ((k1_relat_1 @ X23) = (k2_relat_1 @ (k2_funct_1 @ X23)))
% 10.25/10.46          | ~ (v1_funct_1 @ X23)
% 10.25/10.46          | ~ (v1_relat_1 @ X23))),
% 10.25/10.46      inference('cnf', [status(esa)], [t55_funct_1])).
% 10.25/10.46  thf(t155_funct_1, axiom,
% 10.25/10.46    (![A:$i,B:$i]:
% 10.25/10.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 10.25/10.46       ( ( v2_funct_1 @ B ) =>
% 10.25/10.46         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 10.25/10.46  thf('78', plain,
% 10.25/10.46      (![X20 : $i, X21 : $i]:
% 10.25/10.46         (~ (v2_funct_1 @ X20)
% 10.25/10.46          | ((k10_relat_1 @ X20 @ X21)
% 10.25/10.46              = (k9_relat_1 @ (k2_funct_1 @ X20) @ X21))
% 10.25/10.46          | ~ (v1_funct_1 @ X20)
% 10.25/10.46          | ~ (v1_relat_1 @ X20))),
% 10.25/10.46      inference('cnf', [status(esa)], [t155_funct_1])).
% 10.25/10.46  thf(dt_k2_funct_1, axiom,
% 10.25/10.46    (![A:$i]:
% 10.25/10.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 10.25/10.46       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 10.25/10.46         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 10.25/10.46  thf('79', plain,
% 10.25/10.46      (![X19 : $i]:
% 10.25/10.46         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 10.25/10.46          | ~ (v1_funct_1 @ X19)
% 10.25/10.46          | ~ (v1_relat_1 @ X19))),
% 10.25/10.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 10.25/10.46  thf('80', plain,
% 10.25/10.46      (![X23 : $i]:
% 10.25/10.46         (~ (v2_funct_1 @ X23)
% 10.25/10.46          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 10.25/10.46          | ~ (v1_funct_1 @ X23)
% 10.25/10.46          | ~ (v1_relat_1 @ X23))),
% 10.25/10.46      inference('cnf', [status(esa)], [t55_funct_1])).
% 10.25/10.46  thf(t78_relat_1, axiom,
% 10.25/10.46    (![A:$i]:
% 10.25/10.46     ( ( v1_relat_1 @ A ) =>
% 10.25/10.46       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 10.25/10.46  thf('81', plain,
% 10.25/10.46      (![X16 : $i]:
% 10.25/10.46         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 10.25/10.46          | ~ (v1_relat_1 @ X16))),
% 10.25/10.46      inference('cnf', [status(esa)], [t78_relat_1])).
% 10.25/10.46  thf('82', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 10.25/10.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.25/10.46  thf('83', plain,
% 10.25/10.46      (![X16 : $i]:
% 10.25/10.46         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 10.25/10.46          | ~ (v1_relat_1 @ X16))),
% 10.25/10.46      inference('demod', [status(thm)], ['81', '82'])).
% 10.25/10.46  thf(t160_relat_1, axiom,
% 10.25/10.46    (![A:$i]:
% 10.25/10.46     ( ( v1_relat_1 @ A ) =>
% 10.25/10.46       ( ![B:$i]:
% 10.25/10.46         ( ( v1_relat_1 @ B ) =>
% 10.25/10.46           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 10.25/10.46             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 10.25/10.46  thf('84', plain,
% 10.25/10.46      (![X8 : $i, X9 : $i]:
% 10.25/10.46         (~ (v1_relat_1 @ X8)
% 10.25/10.46          | ((k2_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 10.25/10.46              = (k9_relat_1 @ X8 @ (k2_relat_1 @ X9)))
% 10.25/10.46          | ~ (v1_relat_1 @ X9))),
% 10.25/10.46      inference('cnf', [status(esa)], [t160_relat_1])).
% 10.25/10.46  thf('85', plain,
% 10.25/10.46      (![X0 : $i]:
% 10.25/10.46         (((k2_relat_1 @ X0)
% 10.25/10.46            = (k9_relat_1 @ X0 @ 
% 10.25/10.46               (k2_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))))
% 10.25/10.46          | ~ (v1_relat_1 @ X0)
% 10.25/10.46          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 10.25/10.46          | ~ (v1_relat_1 @ X0))),
% 10.25/10.46      inference('sup+', [status(thm)], ['83', '84'])).
% 10.25/10.46  thf(t71_relat_1, axiom,
% 10.25/10.46    (![A:$i]:
% 10.25/10.46     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 10.25/10.46       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 10.25/10.46  thf('86', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 10.25/10.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.25/10.46  thf('87', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 10.25/10.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.25/10.46  thf('88', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 10.25/10.46      inference('demod', [status(thm)], ['86', '87'])).
% 10.25/10.46  thf('89', plain,
% 10.25/10.46      (![X42 : $i]:
% 10.25/10.46         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 10.25/10.47          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 10.25/10.47      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 10.25/10.47  thf(cc1_relset_1, axiom,
% 10.25/10.47    (![A:$i,B:$i,C:$i]:
% 10.25/10.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.25/10.47       ( v1_relat_1 @ C ) ))).
% 10.25/10.47  thf('90', plain,
% 10.25/10.47      (![X25 : $i, X26 : $i, X27 : $i]:
% 10.25/10.47         ((v1_relat_1 @ X25)
% 10.25/10.47          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 10.25/10.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.25/10.47  thf('91', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 10.25/10.47      inference('sup-', [status(thm)], ['89', '90'])).
% 10.25/10.47  thf('92', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0))),
% 10.25/10.47      inference('demod', [status(thm)], ['85', '88', '91'])).
% 10.25/10.47  thf('93', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X0)
% 10.25/10.47          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 10.25/10.47      inference('simplify', [status(thm)], ['92'])).
% 10.25/10.47  thf('94', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k2_relat_1 @ (k2_funct_1 @ X0))
% 10.25/10.47            = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 10.25/10.47      inference('sup+', [status(thm)], ['80', '93'])).
% 10.25/10.47  thf('95', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 10.25/10.47              = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))))),
% 10.25/10.47      inference('sup-', [status(thm)], ['79', '94'])).
% 10.25/10.47  thf('96', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k2_relat_1 @ (k2_funct_1 @ X0))
% 10.25/10.47            = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0))),
% 10.25/10.47      inference('simplify', [status(thm)], ['95'])).
% 10.25/10.47  thf('97', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k2_relat_1 @ (k2_funct_1 @ X0))
% 10.25/10.47            = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0))),
% 10.25/10.47      inference('sup+', [status(thm)], ['78', '96'])).
% 10.25/10.47  thf('98', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 10.25/10.47              = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 10.25/10.47      inference('simplify', [status(thm)], ['97'])).
% 10.25/10.47  thf('99', plain,
% 10.25/10.47      (![X19 : $i]:
% 10.25/10.47         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 10.25/10.47          | ~ (v1_funct_1 @ X19)
% 10.25/10.47          | ~ (v1_relat_1 @ X19))),
% 10.25/10.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 10.25/10.47  thf('100', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 10.25/10.47              = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 10.25/10.47      inference('simplify', [status(thm)], ['97'])).
% 10.25/10.47  thf(dt_k2_subset_1, axiom,
% 10.25/10.47    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 10.25/10.47  thf('101', plain,
% 10.25/10.47      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 10.25/10.47      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 10.25/10.47  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 10.25/10.47  thf('102', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 10.25/10.47      inference('cnf', [status(esa)], [d4_subset_1])).
% 10.25/10.47  thf('103', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 10.25/10.47      inference('demod', [status(thm)], ['101', '102'])).
% 10.25/10.47  thf(t3_subset, axiom,
% 10.25/10.47    (![A:$i,B:$i]:
% 10.25/10.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 10.25/10.47  thf('104', plain,
% 10.25/10.47      (![X5 : $i, X6 : $i]:
% 10.25/10.47         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 10.25/10.47      inference('cnf', [status(esa)], [t3_subset])).
% 10.25/10.47  thf('105', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 10.25/10.47      inference('sup-', [status(thm)], ['103', '104'])).
% 10.25/10.47  thf(t79_relat_1, axiom,
% 10.25/10.47    (![A:$i,B:$i]:
% 10.25/10.47     ( ( v1_relat_1 @ B ) =>
% 10.25/10.47       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 10.25/10.47         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 10.25/10.47  thf('106', plain,
% 10.25/10.47      (![X17 : $i, X18 : $i]:
% 10.25/10.47         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 10.25/10.47          | ((k5_relat_1 @ X17 @ (k6_relat_1 @ X18)) = (X17))
% 10.25/10.47          | ~ (v1_relat_1 @ X17))),
% 10.25/10.47      inference('cnf', [status(esa)], [t79_relat_1])).
% 10.25/10.47  thf('107', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 10.25/10.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.25/10.47  thf('108', plain,
% 10.25/10.47      (![X17 : $i, X18 : $i]:
% 10.25/10.47         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 10.25/10.47          | ((k5_relat_1 @ X17 @ (k6_partfun1 @ X18)) = (X17))
% 10.25/10.47          | ~ (v1_relat_1 @ X17))),
% 10.25/10.47      inference('demod', [status(thm)], ['106', '107'])).
% 10.25/10.47  thf('109', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X0)
% 10.25/10.47          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 10.25/10.47      inference('sup-', [status(thm)], ['105', '108'])).
% 10.25/10.47  thf('110', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 10.25/10.47            (k6_partfun1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))
% 10.25/10.47            = (k2_funct_1 @ X0))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 10.25/10.47      inference('sup+', [status(thm)], ['100', '109'])).
% 10.25/10.47  thf('111', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 10.25/10.47              (k6_partfun1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))
% 10.25/10.47              = (k2_funct_1 @ X0)))),
% 10.25/10.47      inference('sup-', [status(thm)], ['99', '110'])).
% 10.25/10.47  thf('112', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 10.25/10.47            (k6_partfun1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))
% 10.25/10.47            = (k2_funct_1 @ X0))
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0))),
% 10.25/10.47      inference('simplify', [status(thm)], ['111'])).
% 10.25/10.47  thf('113', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 10.25/10.47            (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 10.25/10.47            = (k2_funct_1 @ X0))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0))),
% 10.25/10.47      inference('sup+', [status(thm)], ['98', '112'])).
% 10.25/10.47  thf('114', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 10.25/10.47              (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 10.25/10.47              = (k2_funct_1 @ X0)))),
% 10.25/10.47      inference('simplify', [status(thm)], ['113'])).
% 10.25/10.47  thf('115', plain,
% 10.25/10.47      (![X19 : $i]:
% 10.25/10.47         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 10.25/10.47          | ~ (v1_funct_1 @ X19)
% 10.25/10.47          | ~ (v1_relat_1 @ X19))),
% 10.25/10.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 10.25/10.47  thf(t61_funct_1, axiom,
% 10.25/10.47    (![A:$i]:
% 10.25/10.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 10.25/10.47       ( ( v2_funct_1 @ A ) =>
% 10.25/10.47         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 10.25/10.47             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 10.25/10.47           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 10.25/10.47             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 10.25/10.47  thf('116', plain,
% 10.25/10.47      (![X24 : $i]:
% 10.25/10.47         (~ (v2_funct_1 @ X24)
% 10.25/10.47          | ((k5_relat_1 @ X24 @ (k2_funct_1 @ X24))
% 10.25/10.47              = (k6_relat_1 @ (k1_relat_1 @ X24)))
% 10.25/10.47          | ~ (v1_funct_1 @ X24)
% 10.25/10.47          | ~ (v1_relat_1 @ X24))),
% 10.25/10.47      inference('cnf', [status(esa)], [t61_funct_1])).
% 10.25/10.47  thf('117', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 10.25/10.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.25/10.47  thf('118', plain,
% 10.25/10.47      (![X24 : $i]:
% 10.25/10.47         (~ (v2_funct_1 @ X24)
% 10.25/10.47          | ((k5_relat_1 @ X24 @ (k2_funct_1 @ X24))
% 10.25/10.47              = (k6_partfun1 @ (k1_relat_1 @ X24)))
% 10.25/10.47          | ~ (v1_funct_1 @ X24)
% 10.25/10.47          | ~ (v1_relat_1 @ X24))),
% 10.25/10.47      inference('demod', [status(thm)], ['116', '117'])).
% 10.25/10.47  thf(t55_relat_1, axiom,
% 10.25/10.47    (![A:$i]:
% 10.25/10.47     ( ( v1_relat_1 @ A ) =>
% 10.25/10.47       ( ![B:$i]:
% 10.25/10.47         ( ( v1_relat_1 @ B ) =>
% 10.25/10.47           ( ![C:$i]:
% 10.25/10.47             ( ( v1_relat_1 @ C ) =>
% 10.25/10.47               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 10.25/10.47                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 10.25/10.47  thf('119', plain,
% 10.25/10.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X11)
% 10.25/10.47          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 10.25/10.47              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 10.25/10.47          | ~ (v1_relat_1 @ X13)
% 10.25/10.47          | ~ (v1_relat_1 @ X12))),
% 10.25/10.47      inference('cnf', [status(esa)], [t55_relat_1])).
% 10.25/10.47  thf('120', plain,
% 10.25/10.47      (![X0 : $i, X1 : $i]:
% 10.25/10.47         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 10.25/10.47            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X1)
% 10.25/10.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 10.25/10.47      inference('sup+', [status(thm)], ['118', '119'])).
% 10.25/10.47  thf('121', plain,
% 10.25/10.47      (![X0 : $i, X1 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 10.25/10.47          | ~ (v1_relat_1 @ X1)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 10.25/10.47              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1))))),
% 10.25/10.47      inference('simplify', [status(thm)], ['120'])).
% 10.25/10.47  thf('122', plain,
% 10.25/10.47      (![X0 : $i, X1 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 10.25/10.47              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X1))),
% 10.25/10.47      inference('sup-', [status(thm)], ['115', '121'])).
% 10.25/10.47  thf('123', plain,
% 10.25/10.47      (![X0 : $i, X1 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X1)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 10.25/10.47              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0))),
% 10.25/10.47      inference('simplify', [status(thm)], ['122'])).
% 10.25/10.47  thf('124', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 10.25/10.47            (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 10.25/10.47            = (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 10.25/10.47      inference('sup+', [status(thm)], ['114', '123'])).
% 10.25/10.47  thf('125', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 10.25/10.47      inference('sup-', [status(thm)], ['89', '90'])).
% 10.25/10.47  thf('126', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 10.25/10.47            (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 10.25/10.47            = (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0))),
% 10.25/10.47      inference('demod', [status(thm)], ['124', '125'])).
% 10.25/10.47  thf('127', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 10.25/10.47              (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 10.25/10.47              = (k5_relat_1 @ X0 @ (k2_funct_1 @ X0))))),
% 10.25/10.47      inference('simplify', [status(thm)], ['126'])).
% 10.25/10.47  thf('128', plain,
% 10.25/10.47      (![X8 : $i, X9 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X8)
% 10.25/10.47          | ((k2_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 10.25/10.47              = (k9_relat_1 @ X8 @ (k2_relat_1 @ X9)))
% 10.25/10.47          | ~ (v1_relat_1 @ X9))),
% 10.25/10.47      inference('cnf', [status(esa)], [t160_relat_1])).
% 10.25/10.47  thf('129', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 10.25/10.47            = (k9_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))) @ 
% 10.25/10.47               (k2_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 10.25/10.47          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 10.25/10.47      inference('sup+', [status(thm)], ['127', '128'])).
% 10.25/10.47  thf('130', plain,
% 10.25/10.47      (![X15 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 10.25/10.47      inference('demod', [status(thm)], ['86', '87'])).
% 10.25/10.47  thf('131', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 10.25/10.47      inference('sup-', [status(thm)], ['89', '90'])).
% 10.25/10.47  thf('132', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 10.25/10.47      inference('sup-', [status(thm)], ['89', '90'])).
% 10.25/10.47  thf('133', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 10.25/10.47            = (k9_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))) @ 
% 10.25/10.47               (k1_relat_1 @ X0)))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0))),
% 10.25/10.47      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 10.25/10.47  thf('134', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 10.25/10.47            = (k9_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 10.25/10.47               (k1_relat_1 @ X0)))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0))),
% 10.25/10.47      inference('sup+', [status(thm)], ['77', '133'])).
% 10.25/10.47  thf('135', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 10.25/10.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.25/10.47  thf('136', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 10.25/10.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.25/10.47  thf('137', plain,
% 10.25/10.47      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 10.25/10.47      inference('demod', [status(thm)], ['135', '136'])).
% 10.25/10.47  thf('138', plain,
% 10.25/10.47      (![X16 : $i]:
% 10.25/10.47         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 10.25/10.47          | ~ (v1_relat_1 @ X16))),
% 10.25/10.47      inference('demod', [status(thm)], ['81', '82'])).
% 10.25/10.47  thf('139', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 10.25/10.47            = (k6_partfun1 @ X0))
% 10.25/10.47          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 10.25/10.47      inference('sup+', [status(thm)], ['137', '138'])).
% 10.25/10.47  thf('140', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 10.25/10.47      inference('sup-', [status(thm)], ['89', '90'])).
% 10.25/10.47  thf('141', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 10.25/10.47           = (k6_partfun1 @ X0))),
% 10.25/10.47      inference('demod', [status(thm)], ['139', '140'])).
% 10.25/10.47  thf('142', plain,
% 10.25/10.47      (![X8 : $i, X9 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X8)
% 10.25/10.47          | ((k2_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 10.25/10.47              = (k9_relat_1 @ X8 @ (k2_relat_1 @ X9)))
% 10.25/10.47          | ~ (v1_relat_1 @ X9))),
% 10.25/10.47      inference('cnf', [status(esa)], [t160_relat_1])).
% 10.25/10.47  thf('143', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k2_relat_1 @ (k6_partfun1 @ X0))
% 10.25/10.47            = (k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 10.25/10.47               (k2_relat_1 @ (k6_partfun1 @ X0))))
% 10.25/10.47          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 10.25/10.47          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 10.25/10.47      inference('sup+', [status(thm)], ['141', '142'])).
% 10.25/10.47  thf('144', plain,
% 10.25/10.47      (![X15 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 10.25/10.47      inference('demod', [status(thm)], ['86', '87'])).
% 10.25/10.47  thf('145', plain,
% 10.25/10.47      (![X15 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 10.25/10.47      inference('demod', [status(thm)], ['86', '87'])).
% 10.25/10.47  thf('146', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 10.25/10.47      inference('sup-', [status(thm)], ['89', '90'])).
% 10.25/10.47  thf('147', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 10.25/10.47      inference('sup-', [status(thm)], ['89', '90'])).
% 10.25/10.47  thf('148', plain,
% 10.25/10.47      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_partfun1 @ X0) @ X0))),
% 10.25/10.47      inference('demod', [status(thm)], ['143', '144', '145', '146', '147'])).
% 10.25/10.47  thf('149', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 10.25/10.47            = (k1_relat_1 @ X0))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0))),
% 10.25/10.47      inference('demod', [status(thm)], ['134', '148'])).
% 10.25/10.47  thf('150', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 10.25/10.47              = (k1_relat_1 @ X0)))),
% 10.25/10.47      inference('simplify', [status(thm)], ['149'])).
% 10.25/10.47  thf('151', plain,
% 10.25/10.47      ((((k2_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 10.25/10.47        | ~ (v1_relat_1 @ sk_D)
% 10.25/10.47        | ~ (v1_funct_1 @ sk_D)
% 10.25/10.47        | ~ (v2_funct_1 @ sk_D))),
% 10.25/10.47      inference('sup+', [status(thm)], ['76', '150'])).
% 10.25/10.47  thf('152', plain,
% 10.25/10.47      (![X15 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 10.25/10.47      inference('demod', [status(thm)], ['86', '87'])).
% 10.25/10.47  thf('153', plain,
% 10.25/10.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('154', plain,
% 10.25/10.47      (![X25 : $i, X26 : $i, X27 : $i]:
% 10.25/10.47         ((v1_relat_1 @ X25)
% 10.25/10.47          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 10.25/10.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.25/10.47  thf('155', plain, ((v1_relat_1 @ sk_D)),
% 10.25/10.47      inference('sup-', [status(thm)], ['153', '154'])).
% 10.25/10.47  thf('156', plain, ((v1_funct_1 @ sk_D)),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('157', plain, ((v2_funct_1 @ sk_D)),
% 10.25/10.47      inference('sup-', [status(thm)], ['73', '74'])).
% 10.25/10.47  thf('158', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 10.25/10.47      inference('demod', [status(thm)], ['151', '152', '155', '156', '157'])).
% 10.25/10.47  thf('159', plain,
% 10.25/10.47      (![X16 : $i]:
% 10.25/10.47         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 10.25/10.47          | ~ (v1_relat_1 @ X16))),
% 10.25/10.47      inference('demod', [status(thm)], ['81', '82'])).
% 10.25/10.47  thf('160', plain,
% 10.25/10.47      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 10.25/10.47        | ~ (v1_relat_1 @ sk_D))),
% 10.25/10.47      inference('sup+', [status(thm)], ['158', '159'])).
% 10.25/10.47  thf('161', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1))),
% 10.25/10.47      inference('demod', [status(thm)], ['50', '51'])).
% 10.25/10.47  thf('162', plain,
% 10.25/10.47      (![X19 : $i]:
% 10.25/10.47         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 10.25/10.47          | ~ (v1_funct_1 @ X19)
% 10.25/10.47          | ~ (v1_relat_1 @ X19))),
% 10.25/10.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 10.25/10.47  thf('163', plain,
% 10.25/10.47      (![X24 : $i]:
% 10.25/10.47         (~ (v2_funct_1 @ X24)
% 10.25/10.47          | ((k5_relat_1 @ (k2_funct_1 @ X24) @ X24)
% 10.25/10.47              = (k6_relat_1 @ (k2_relat_1 @ X24)))
% 10.25/10.47          | ~ (v1_funct_1 @ X24)
% 10.25/10.47          | ~ (v1_relat_1 @ X24))),
% 10.25/10.47      inference('cnf', [status(esa)], [t61_funct_1])).
% 10.25/10.47  thf('164', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 10.25/10.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.25/10.47  thf('165', plain,
% 10.25/10.47      (![X24 : $i]:
% 10.25/10.47         (~ (v2_funct_1 @ X24)
% 10.25/10.47          | ((k5_relat_1 @ (k2_funct_1 @ X24) @ X24)
% 10.25/10.47              = (k6_partfun1 @ (k2_relat_1 @ X24)))
% 10.25/10.47          | ~ (v1_funct_1 @ X24)
% 10.25/10.47          | ~ (v1_relat_1 @ X24))),
% 10.25/10.47      inference('demod', [status(thm)], ['163', '164'])).
% 10.25/10.47  thf('166', plain,
% 10.25/10.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X11)
% 10.25/10.47          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 10.25/10.47              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 10.25/10.47          | ~ (v1_relat_1 @ X13)
% 10.25/10.47          | ~ (v1_relat_1 @ X12))),
% 10.25/10.47      inference('cnf', [status(esa)], [t55_relat_1])).
% 10.25/10.47  thf('167', plain,
% 10.25/10.47      (![X0 : $i, X1 : $i]:
% 10.25/10.47         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 10.25/10.47            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 10.25/10.47          | ~ (v1_relat_1 @ X1)
% 10.25/10.47          | ~ (v1_relat_1 @ X0))),
% 10.25/10.47      inference('sup+', [status(thm)], ['165', '166'])).
% 10.25/10.47  thf('168', plain,
% 10.25/10.47      (![X0 : $i, X1 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X1)
% 10.25/10.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 10.25/10.47              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 10.25/10.47      inference('simplify', [status(thm)], ['167'])).
% 10.25/10.47  thf('169', plain,
% 10.25/10.47      (![X0 : $i, X1 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 10.25/10.47              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X1))),
% 10.25/10.47      inference('sup-', [status(thm)], ['162', '168'])).
% 10.25/10.47  thf('170', plain,
% 10.25/10.47      (![X0 : $i, X1 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X1)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 10.25/10.47              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0))),
% 10.25/10.47      inference('simplify', [status(thm)], ['169'])).
% 10.25/10.47  thf('171', plain,
% 10.25/10.47      ((((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_D)
% 10.25/10.47          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A_1)))
% 10.25/10.47        | ~ (v1_relat_1 @ sk_C)
% 10.25/10.47        | ~ (v1_funct_1 @ sk_C)
% 10.25/10.47        | ~ (v2_funct_1 @ sk_C)
% 10.25/10.47        | ~ (v1_relat_1 @ sk_D))),
% 10.25/10.47      inference('sup+', [status(thm)], ['161', '170'])).
% 10.25/10.47  thf('172', plain,
% 10.25/10.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('173', plain,
% 10.25/10.47      (![X28 : $i, X29 : $i, X30 : $i]:
% 10.25/10.47         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 10.25/10.47          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 10.25/10.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 10.25/10.47  thf('174', plain,
% 10.25/10.47      (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 10.25/10.47      inference('sup-', [status(thm)], ['172', '173'])).
% 10.25/10.47  thf('175', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('176', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 10.25/10.47      inference('sup+', [status(thm)], ['174', '175'])).
% 10.25/10.47  thf('177', plain,
% 10.25/10.47      (![X19 : $i]:
% 10.25/10.47         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 10.25/10.47          | ~ (v1_funct_1 @ X19)
% 10.25/10.47          | ~ (v1_relat_1 @ X19))),
% 10.25/10.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 10.25/10.47  thf('178', plain,
% 10.25/10.47      (![X20 : $i, X21 : $i]:
% 10.25/10.47         (~ (v2_funct_1 @ X20)
% 10.25/10.47          | ((k10_relat_1 @ X20 @ X21)
% 10.25/10.47              = (k9_relat_1 @ (k2_funct_1 @ X20) @ X21))
% 10.25/10.47          | ~ (v1_funct_1 @ X20)
% 10.25/10.47          | ~ (v1_relat_1 @ X20))),
% 10.25/10.47      inference('cnf', [status(esa)], [t155_funct_1])).
% 10.25/10.47  thf('179', plain,
% 10.25/10.47      (![X19 : $i]:
% 10.25/10.47         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 10.25/10.47          | ~ (v1_funct_1 @ X19)
% 10.25/10.47          | ~ (v1_relat_1 @ X19))),
% 10.25/10.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 10.25/10.47  thf('180', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 10.25/10.47      inference('sup+', [status(thm)], ['174', '175'])).
% 10.25/10.47  thf('181', plain,
% 10.25/10.47      (![X19 : $i]:
% 10.25/10.47         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 10.25/10.47          | ~ (v1_funct_1 @ X19)
% 10.25/10.47          | ~ (v1_relat_1 @ X19))),
% 10.25/10.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 10.25/10.47  thf('182', plain,
% 10.25/10.47      (![X23 : $i]:
% 10.25/10.47         (~ (v2_funct_1 @ X23)
% 10.25/10.47          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 10.25/10.47          | ~ (v1_funct_1 @ X23)
% 10.25/10.47          | ~ (v1_relat_1 @ X23))),
% 10.25/10.47      inference('cnf', [status(esa)], [t55_funct_1])).
% 10.25/10.47  thf('183', plain,
% 10.25/10.47      (![X16 : $i]:
% 10.25/10.47         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 10.25/10.47          | ~ (v1_relat_1 @ X16))),
% 10.25/10.47      inference('demod', [status(thm)], ['81', '82'])).
% 10.25/10.47  thf('184', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 10.25/10.47            = (k2_funct_1 @ X0))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 10.25/10.47      inference('sup+', [status(thm)], ['182', '183'])).
% 10.25/10.47  thf('185', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 10.25/10.47              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 10.25/10.47      inference('sup-', [status(thm)], ['181', '184'])).
% 10.25/10.47  thf('186', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 10.25/10.47            = (k2_funct_1 @ X0))
% 10.25/10.47          | ~ (v2_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_funct_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X0))),
% 10.25/10.47      inference('simplify', [status(thm)], ['185'])).
% 10.25/10.47  thf('187', plain,
% 10.25/10.47      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 10.25/10.47          = (k2_funct_1 @ sk_C))
% 10.25/10.47        | ~ (v1_relat_1 @ sk_C)
% 10.25/10.47        | ~ (v1_funct_1 @ sk_C)
% 10.25/10.47        | ~ (v2_funct_1 @ sk_C))),
% 10.25/10.47      inference('sup+', [status(thm)], ['180', '186'])).
% 10.25/10.47  thf('188', plain,
% 10.25/10.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('189', plain,
% 10.25/10.47      (![X25 : $i, X26 : $i, X27 : $i]:
% 10.25/10.47         ((v1_relat_1 @ X25)
% 10.25/10.47          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 10.25/10.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.25/10.47  thf('190', plain, ((v1_relat_1 @ sk_C)),
% 10.25/10.47      inference('sup-', [status(thm)], ['188', '189'])).
% 10.25/10.47  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('192', plain, ((v2_funct_1 @ sk_C)),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('193', plain,
% 10.25/10.47      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 10.25/10.47         = (k2_funct_1 @ sk_C))),
% 10.25/10.47      inference('demod', [status(thm)], ['187', '190', '191', '192'])).
% 10.25/10.47  thf('194', plain,
% 10.25/10.47      (![X8 : $i, X9 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X8)
% 10.25/10.47          | ((k2_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 10.25/10.47              = (k9_relat_1 @ X8 @ (k2_relat_1 @ X9)))
% 10.25/10.47          | ~ (v1_relat_1 @ X9))),
% 10.25/10.47      inference('cnf', [status(esa)], [t160_relat_1])).
% 10.25/10.47  thf('195', plain,
% 10.25/10.47      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 10.25/10.47          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 10.25/10.47             (k2_relat_1 @ (k6_partfun1 @ sk_B))))
% 10.25/10.47        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 10.25/10.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 10.25/10.47      inference('sup+', [status(thm)], ['193', '194'])).
% 10.25/10.47  thf('196', plain,
% 10.25/10.47      (![X15 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 10.25/10.47      inference('demod', [status(thm)], ['86', '87'])).
% 10.25/10.47  thf('197', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 10.25/10.47      inference('sup-', [status(thm)], ['89', '90'])).
% 10.25/10.47  thf('198', plain,
% 10.25/10.47      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 10.25/10.47          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))
% 10.25/10.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 10.25/10.47      inference('demod', [status(thm)], ['195', '196', '197'])).
% 10.25/10.47  thf('199', plain,
% 10.25/10.47      ((~ (v1_relat_1 @ sk_C)
% 10.25/10.47        | ~ (v1_funct_1 @ sk_C)
% 10.25/10.47        | ((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 10.25/10.47            = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)))),
% 10.25/10.47      inference('sup-', [status(thm)], ['179', '198'])).
% 10.25/10.47  thf('200', plain, ((v1_relat_1 @ sk_C)),
% 10.25/10.47      inference('sup-', [status(thm)], ['188', '189'])).
% 10.25/10.47  thf('201', plain, ((v1_funct_1 @ sk_C)),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('202', plain,
% 10.25/10.47      (((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 10.25/10.47         = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 10.25/10.47      inference('demod', [status(thm)], ['199', '200', '201'])).
% 10.25/10.47  thf('203', plain,
% 10.25/10.47      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k10_relat_1 @ sk_C @ sk_B))
% 10.25/10.47        | ~ (v1_relat_1 @ sk_C)
% 10.25/10.47        | ~ (v1_funct_1 @ sk_C)
% 10.25/10.47        | ~ (v2_funct_1 @ sk_C))),
% 10.25/10.47      inference('sup+', [status(thm)], ['178', '202'])).
% 10.25/10.47  thf('204', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 10.25/10.47      inference('sup+', [status(thm)], ['174', '175'])).
% 10.25/10.47  thf(t169_relat_1, axiom,
% 10.25/10.47    (![A:$i]:
% 10.25/10.47     ( ( v1_relat_1 @ A ) =>
% 10.25/10.47       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 10.25/10.47  thf('205', plain,
% 10.25/10.47      (![X10 : $i]:
% 10.25/10.47         (((k10_relat_1 @ X10 @ (k2_relat_1 @ X10)) = (k1_relat_1 @ X10))
% 10.25/10.47          | ~ (v1_relat_1 @ X10))),
% 10.25/10.47      inference('cnf', [status(esa)], [t169_relat_1])).
% 10.25/10.47  thf('206', plain,
% 10.25/10.47      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 10.25/10.47        | ~ (v1_relat_1 @ sk_C))),
% 10.25/10.47      inference('sup+', [status(thm)], ['204', '205'])).
% 10.25/10.47  thf('207', plain, ((v1_relat_1 @ sk_C)),
% 10.25/10.47      inference('sup-', [status(thm)], ['188', '189'])).
% 10.25/10.47  thf('208', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 10.25/10.47      inference('demod', [status(thm)], ['206', '207'])).
% 10.25/10.47  thf('209', plain, ((v1_relat_1 @ sk_C)),
% 10.25/10.47      inference('sup-', [status(thm)], ['188', '189'])).
% 10.25/10.47  thf('210', plain, ((v1_funct_1 @ sk_C)),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('211', plain, ((v2_funct_1 @ sk_C)),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('212', plain,
% 10.25/10.47      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 10.25/10.47      inference('demod', [status(thm)], ['203', '208', '209', '210', '211'])).
% 10.25/10.47  thf('213', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X0)
% 10.25/10.47          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 10.25/10.47      inference('sup-', [status(thm)], ['105', '108'])).
% 10.25/10.47  thf('214', plain,
% 10.25/10.47      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 10.25/10.47          (k6_partfun1 @ (k1_relat_1 @ sk_C))) = (k2_funct_1 @ sk_C))
% 10.25/10.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 10.25/10.47      inference('sup+', [status(thm)], ['212', '213'])).
% 10.25/10.47  thf('215', plain,
% 10.25/10.47      ((~ (v1_relat_1 @ sk_C)
% 10.25/10.47        | ~ (v1_funct_1 @ sk_C)
% 10.25/10.47        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 10.25/10.47            (k6_partfun1 @ (k1_relat_1 @ sk_C))) = (k2_funct_1 @ sk_C)))),
% 10.25/10.47      inference('sup-', [status(thm)], ['177', '214'])).
% 10.25/10.47  thf('216', plain, ((v1_relat_1 @ sk_C)),
% 10.25/10.47      inference('sup-', [status(thm)], ['188', '189'])).
% 10.25/10.47  thf('217', plain, ((v1_funct_1 @ sk_C)),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('218', plain,
% 10.25/10.47      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 10.25/10.47         = (k2_funct_1 @ sk_C))),
% 10.25/10.47      inference('demod', [status(thm)], ['215', '216', '217'])).
% 10.25/10.47  thf('219', plain,
% 10.25/10.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('220', plain,
% 10.25/10.47      (![X63 : $i, X64 : $i, X65 : $i]:
% 10.25/10.47         (((X63) = (k1_xboole_0))
% 10.25/10.47          | ~ (v1_funct_1 @ X64)
% 10.25/10.47          | ~ (v1_funct_2 @ X64 @ X65 @ X63)
% 10.25/10.47          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X63)))
% 10.25/10.47          | ((k5_relat_1 @ X64 @ (k2_funct_1 @ X64)) = (k6_partfun1 @ X65))
% 10.25/10.47          | ~ (v2_funct_1 @ X64)
% 10.25/10.47          | ((k2_relset_1 @ X65 @ X63 @ X64) != (X63)))),
% 10.25/10.47      inference('cnf', [status(esa)], [t35_funct_2])).
% 10.25/10.47  thf('221', plain,
% 10.25/10.47      ((((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 10.25/10.47        | ~ (v2_funct_1 @ sk_C)
% 10.25/10.47        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))
% 10.25/10.47        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 10.25/10.47        | ~ (v1_funct_1 @ sk_C)
% 10.25/10.47        | ((sk_B) = (k1_xboole_0)))),
% 10.25/10.47      inference('sup-', [status(thm)], ['219', '220'])).
% 10.25/10.47  thf('222', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('223', plain, ((v2_funct_1 @ sk_C)),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('224', plain,
% 10.25/10.47      (![X19 : $i]:
% 10.25/10.47         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 10.25/10.47          | ~ (v1_funct_1 @ X19)
% 10.25/10.47          | ~ (v1_relat_1 @ X19))),
% 10.25/10.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 10.25/10.47  thf('225', plain,
% 10.25/10.47      (![X24 : $i]:
% 10.25/10.47         (~ (v2_funct_1 @ X24)
% 10.25/10.47          | ((k5_relat_1 @ X24 @ (k2_funct_1 @ X24))
% 10.25/10.47              = (k6_partfun1 @ (k1_relat_1 @ X24)))
% 10.25/10.47          | ~ (v1_funct_1 @ X24)
% 10.25/10.47          | ~ (v1_relat_1 @ X24))),
% 10.25/10.47      inference('demod', [status(thm)], ['116', '117'])).
% 10.25/10.47  thf('226', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 10.25/10.47      inference('sup+', [status(thm)], ['174', '175'])).
% 10.25/10.47  thf('227', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X0)
% 10.25/10.47          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 10.25/10.47      inference('sup-', [status(thm)], ['105', '108'])).
% 10.25/10.47  thf('228', plain,
% 10.25/10.47      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 10.25/10.47        | ~ (v1_relat_1 @ sk_C))),
% 10.25/10.47      inference('sup+', [status(thm)], ['226', '227'])).
% 10.25/10.47  thf('229', plain, ((v1_relat_1 @ sk_C)),
% 10.25/10.47      inference('sup-', [status(thm)], ['188', '189'])).
% 10.25/10.47  thf('230', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 10.25/10.47      inference('demod', [status(thm)], ['228', '229'])).
% 10.25/10.47  thf('231', plain,
% 10.25/10.47      (![X16 : $i]:
% 10.25/10.47         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 10.25/10.47          | ~ (v1_relat_1 @ X16))),
% 10.25/10.47      inference('demod', [status(thm)], ['81', '82'])).
% 10.25/10.47  thf('232', plain,
% 10.25/10.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X11)
% 10.25/10.47          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 10.25/10.47              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 10.25/10.47          | ~ (v1_relat_1 @ X13)
% 10.25/10.47          | ~ (v1_relat_1 @ X12))),
% 10.25/10.47      inference('cnf', [status(esa)], [t55_relat_1])).
% 10.25/10.47  thf('233', plain,
% 10.25/10.47      (![X0 : $i, X1 : $i]:
% 10.25/10.47         (((k5_relat_1 @ X0 @ X1)
% 10.25/10.47            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 10.25/10.47               (k5_relat_1 @ X0 @ X1)))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 10.25/10.47          | ~ (v1_relat_1 @ X1)
% 10.25/10.47          | ~ (v1_relat_1 @ X0))),
% 10.25/10.47      inference('sup+', [status(thm)], ['231', '232'])).
% 10.25/10.47  thf('234', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 10.25/10.47      inference('sup-', [status(thm)], ['89', '90'])).
% 10.25/10.47  thf('235', plain,
% 10.25/10.47      (![X0 : $i, X1 : $i]:
% 10.25/10.47         (((k5_relat_1 @ X0 @ X1)
% 10.25/10.47            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 10.25/10.47               (k5_relat_1 @ X0 @ X1)))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ X1)
% 10.25/10.47          | ~ (v1_relat_1 @ X0))),
% 10.25/10.47      inference('demod', [status(thm)], ['233', '234'])).
% 10.25/10.47  thf('236', plain,
% 10.25/10.47      (![X0 : $i, X1 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X1)
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ((k5_relat_1 @ X0 @ X1)
% 10.25/10.47              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 10.25/10.47                 (k5_relat_1 @ X0 @ X1))))),
% 10.25/10.47      inference('simplify', [status(thm)], ['235'])).
% 10.25/10.47  thf('237', plain,
% 10.25/10.47      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B))
% 10.25/10.47          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))
% 10.25/10.47        | ~ (v1_relat_1 @ sk_C)
% 10.25/10.47        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 10.25/10.47      inference('sup+', [status(thm)], ['230', '236'])).
% 10.25/10.47  thf('238', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 10.25/10.47      inference('demod', [status(thm)], ['228', '229'])).
% 10.25/10.47  thf('239', plain, ((v1_relat_1 @ sk_C)),
% 10.25/10.47      inference('sup-', [status(thm)], ['188', '189'])).
% 10.25/10.47  thf('240', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 10.25/10.47      inference('sup-', [status(thm)], ['89', '90'])).
% 10.25/10.47  thf('241', plain,
% 10.25/10.47      (((sk_C) = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))),
% 10.25/10.47      inference('demod', [status(thm)], ['237', '238', '239', '240'])).
% 10.25/10.47  thf('242', plain,
% 10.25/10.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 10.25/10.47         (~ (v1_relat_1 @ X11)
% 10.25/10.47          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 10.25/10.47              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 10.25/10.47          | ~ (v1_relat_1 @ X13)
% 10.25/10.47          | ~ (v1_relat_1 @ X12))),
% 10.25/10.47      inference('cnf', [status(esa)], [t55_relat_1])).
% 10.25/10.47  thf('243', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k5_relat_1 @ sk_C @ X0)
% 10.25/10.47            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 10.25/10.47               (k5_relat_1 @ sk_C @ X0)))
% 10.25/10.47          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 10.25/10.47          | ~ (v1_relat_1 @ X0)
% 10.25/10.47          | ~ (v1_relat_1 @ sk_C))),
% 10.25/10.47      inference('sup+', [status(thm)], ['241', '242'])).
% 10.25/10.47  thf('244', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 10.25/10.47      inference('sup-', [status(thm)], ['89', '90'])).
% 10.25/10.47  thf('245', plain, ((v1_relat_1 @ sk_C)),
% 10.25/10.47      inference('sup-', [status(thm)], ['188', '189'])).
% 10.25/10.47  thf('246', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         (((k5_relat_1 @ sk_C @ X0)
% 10.25/10.47            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 10.25/10.47               (k5_relat_1 @ sk_C @ X0)))
% 10.25/10.47          | ~ (v1_relat_1 @ X0))),
% 10.25/10.47      inference('demod', [status(thm)], ['243', '244', '245'])).
% 10.25/10.47  thf('247', plain,
% 10.25/10.47      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 10.25/10.47          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 10.25/10.47             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 10.25/10.47        | ~ (v1_relat_1 @ sk_C)
% 10.25/10.47        | ~ (v1_funct_1 @ sk_C)
% 10.25/10.47        | ~ (v2_funct_1 @ sk_C)
% 10.25/10.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 10.25/10.47      inference('sup+', [status(thm)], ['225', '246'])).
% 10.25/10.47  thf('248', plain,
% 10.25/10.47      (![X0 : $i]:
% 10.25/10.47         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 10.25/10.47           = (k6_partfun1 @ X0))),
% 10.25/10.47      inference('demod', [status(thm)], ['139', '140'])).
% 10.25/10.47  thf('249', plain, ((v1_relat_1 @ sk_C)),
% 10.25/10.47      inference('sup-', [status(thm)], ['188', '189'])).
% 10.25/10.47  thf('250', plain, ((v1_funct_1 @ sk_C)),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('251', plain, ((v2_funct_1 @ sk_C)),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('252', plain,
% 10.25/10.47      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 10.25/10.47          = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 10.25/10.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 10.25/10.47      inference('demod', [status(thm)], ['247', '248', '249', '250', '251'])).
% 10.25/10.47  thf('253', plain,
% 10.25/10.47      ((~ (v1_relat_1 @ sk_C)
% 10.25/10.47        | ~ (v1_funct_1 @ sk_C)
% 10.25/10.47        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 10.25/10.47            = (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 10.25/10.47      inference('sup-', [status(thm)], ['224', '252'])).
% 10.25/10.47  thf('254', plain, ((v1_relat_1 @ sk_C)),
% 10.25/10.47      inference('sup-', [status(thm)], ['188', '189'])).
% 10.25/10.47  thf('255', plain, ((v1_funct_1 @ sk_C)),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('256', plain,
% 10.25/10.47      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 10.25/10.47         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 10.25/10.47      inference('demod', [status(thm)], ['253', '254', '255'])).
% 10.25/10.47  thf('257', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('258', plain, ((v1_funct_1 @ sk_C)),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('259', plain,
% 10.25/10.47      ((((sk_B) != (sk_B))
% 10.25/10.47        | ((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))
% 10.25/10.47        | ((sk_B) = (k1_xboole_0)))),
% 10.25/10.47      inference('demod', [status(thm)],
% 10.25/10.47                ['221', '222', '223', '256', '257', '258'])).
% 10.25/10.47  thf('260', plain,
% 10.25/10.47      ((((sk_B) = (k1_xboole_0))
% 10.25/10.47        | ((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A_1)))),
% 10.25/10.47      inference('simplify', [status(thm)], ['259'])).
% 10.25/10.47  thf('261', plain, (((sk_B) != (k1_xboole_0))),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('262', plain,
% 10.25/10.47      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))),
% 10.25/10.47      inference('simplify_reflect-', [status(thm)], ['260', '261'])).
% 10.25/10.47  thf('263', plain,
% 10.25/10.47      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A_1))
% 10.25/10.47         = (k2_funct_1 @ sk_C))),
% 10.25/10.47      inference('demod', [status(thm)], ['218', '262'])).
% 10.25/10.47  thf('264', plain, ((v1_relat_1 @ sk_C)),
% 10.25/10.47      inference('sup-', [status(thm)], ['188', '189'])).
% 10.25/10.47  thf('265', plain, ((v1_funct_1 @ sk_C)),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('266', plain, ((v2_funct_1 @ sk_C)),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('267', plain, ((v1_relat_1 @ sk_D)),
% 10.25/10.47      inference('sup-', [status(thm)], ['153', '154'])).
% 10.25/10.47  thf('268', plain,
% 10.25/10.47      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 10.25/10.47      inference('demod', [status(thm)],
% 10.25/10.47                ['171', '176', '263', '264', '265', '266', '267'])).
% 10.25/10.47  thf('269', plain, ((v1_relat_1 @ sk_D)),
% 10.25/10.47      inference('sup-', [status(thm)], ['153', '154'])).
% 10.25/10.47  thf('270', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 10.25/10.47      inference('demod', [status(thm)], ['160', '268', '269'])).
% 10.25/10.47  thf('271', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 10.25/10.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.25/10.47  thf('272', plain, ($false),
% 10.25/10.47      inference('simplify_reflect-', [status(thm)], ['270', '271'])).
% 10.25/10.47  
% 10.25/10.47  % SZS output end Refutation
% 10.25/10.47  
% 10.25/10.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
