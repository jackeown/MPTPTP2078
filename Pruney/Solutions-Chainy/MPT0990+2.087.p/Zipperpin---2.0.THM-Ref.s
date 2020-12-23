%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nryRYOqL3K

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:09 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  261 (1872 expanded)
%              Number of leaves         :   45 ( 564 expanded)
%              Depth                    :   19
%              Number of atoms          : 2687 (55932 expanded)
%              Number of equality atoms :  162 (3922 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
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
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( X54 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X56 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X54 ) ) )
      | ( ( k5_relat_1 @ X55 @ ( k2_funct_1 @ X55 ) )
        = ( k6_partfun1 @ X56 ) )
      | ~ ( v2_funct_1 @ X55 )
      | ( ( k2_relset_1 @ X56 @ X54 @ X55 )
       != X54 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( X54 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X56 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X54 ) ) )
      | ( ( k5_relat_1 @ X55 @ ( k2_funct_1 @ X55 ) )
        = ( k6_relat_1 @ X56 ) )
      | ~ ( v2_funct_1 @ X55 )
      | ( ( k2_relset_1 @ X56 @ X54 @ X55 )
       != X54 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7','8','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('17',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( r2_relset_1 @ X39 @ X39 @ ( k1_partfun1 @ X39 @ X40 @ X40 @ X39 @ X38 @ X41 ) @ ( k6_partfun1 @ X39 ) )
      | ( ( k2_relset_1 @ X40 @ X39 @ X41 )
        = X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('18',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( r2_relset_1 @ X39 @ X39 @ ( k1_partfun1 @ X39 @ X40 @ X40 @ X39 @ X38 @ X41 ) @ ( k6_relat_1 @ X39 ) )
      | ( ( k2_relset_1 @ X40 @ X39 @ X41 )
        = X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['12','29'])).

thf('31',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('35',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('42',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X21 = X24 )
      | ~ ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X53 @ X52 @ X51 )
       != X52 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X51 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X53 @ X52 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
     != sk_B_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ( sk_B_1 != sk_B_1 ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X53 @ X52 @ X51 )
       != X52 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X53 @ X52 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('58',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
     != sk_B_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( sk_B_1 != sk_B_1 ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','64'])).

thf('66',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('68',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 )
        = ( k5_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('74',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( X54 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X56 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X54 ) ) )
      | ( ( k5_relat_1 @ X55 @ ( k2_funct_1 @ X55 ) )
        = ( k6_relat_1 @ X56 ) )
      | ~ ( v2_funct_1 @ X55 )
      | ( ( k2_relset_1 @ X56 @ X54 @ X55 )
       != X54 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('76',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
     != sk_B_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','84'])).

thf('86',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','85'])).

thf('87',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
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

thf('89',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( zip_tseitin_0 @ X46 @ X49 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X50 @ X47 @ X47 @ X48 @ X49 @ X46 ) )
      | ( zip_tseitin_1 @ X48 @ X47 )
      | ( ( k2_relset_1 @ X50 @ X47 @ X49 )
       != X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X47 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B_1 @ X0 )
       != sk_B_1 )
      | ( zip_tseitin_1 @ sk_A @ sk_B_1 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B_1 @ X0 )
       != sk_B_1 )
      | ( zip_tseitin_1 @ sk_A @ sk_B_1 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C_1 )
    | ( zip_tseitin_1 @ sk_A @ sk_B_1 )
    | ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
     != sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['87','93'])).

thf(t62_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('95',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t62_funct_1])).

thf('96',plain,
    ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf(fc7_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B )
        & ( v2_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('97',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_funct_1])).

thf('98',plain,
    ( ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('100',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('101',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('102',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('105',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['98','99','102','105','106','107'])).

thf('109',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['103','104'])).

thf('111',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C_1 )
    | ( zip_tseitin_1 @ sk_A @ sk_B_1 )
    | ( sk_B_1 != sk_B_1 ) ),
    inference(demod,[status(thm)],['94','113','114','115','116','117'])).

thf('119',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B_1 )
    | ( zip_tseitin_0 @ sk_D @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('121',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    zip_tseitin_0 @ sk_D @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v2_funct_1 @ X43 )
      | ~ ( zip_tseitin_0 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('125',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['31','125'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('127',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) ) )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('128',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B_1 ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('131',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['131','132'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('134',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t59_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('135',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 ) )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B_1 ) )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['133','137'])).

thf('139',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['131','132'])).

thf('140',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['103','104'])).

thf('141',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['138','139','140','141','142'])).

thf('144',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('146',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['123','124'])).

thf('149',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['128','143','146','147','148'])).

thf('150',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('152',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','86'])).

thf('156',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('157',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X13
        = ( k2_funct_1 @ X14 ) )
      | ( ( k5_relat_1 @ X14 @ X13 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X14 ) ) )
      | ( ( k2_relat_1 @ X14 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('158',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t62_funct_1])).

thf('160',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','84'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('162',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ ( k2_funct_1 @ sk_C_1 ) )
      = sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('164',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('165',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('167',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X53 @ X52 @ X51 )
       != X52 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X51 ) @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X53 @ X52 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('169',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
     != sk_B_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ( sk_B_1 != sk_B_1 ) ),
    inference(demod,[status(thm)],['169','170','171','172','173'])).

thf('175',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('177',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['162','165','166','175','176'])).

thf('178',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','64'])).

thf('179',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 )
      | ( X21 != X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('180',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['178','180'])).

thf('182',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','84'])).

thf('183',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','84'])).

thf('184',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['177','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('187',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('189',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) ) )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('190',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['103','104'])).

thf('192',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['190','191','192','193'])).

thf('195',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['177','184'])).

thf('196',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('197',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('198',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = sk_A )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['187','194','195','196','197'])).

thf('199',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['159','198'])).

thf('200',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['103','104'])).

thf('201',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['199','200','201','202'])).

thf('204',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['103','104'])).

thf('205',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['131','132'])).

thf('208',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['144','145'])).

thf('210',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ( sk_B_1
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['158','203','204','205','206','207','208','209'])).

thf('211',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( sk_B_1
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    sk_B_1
 != ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['211','212'])).

thf('214',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['149','213'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nryRYOqL3K
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 14:11:41 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 1.65/1.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.81  % Solved by: fo/fo7.sh
% 1.65/1.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.81  % done 978 iterations in 1.327s
% 1.65/1.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.81  % SZS output start Refutation
% 1.65/1.81  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.65/1.81  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.65/1.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.65/1.81  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.81  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.65/1.81  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.65/1.81  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.65/1.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.65/1.81  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.65/1.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.81  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.65/1.81  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.65/1.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.65/1.81  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.65/1.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.65/1.81  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.65/1.81  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.65/1.81  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.65/1.81  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.65/1.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.65/1.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.65/1.81  thf(sk_D_type, type, sk_D: $i).
% 1.65/1.81  thf(t36_funct_2, conjecture,
% 1.65/1.81    (![A:$i,B:$i,C:$i]:
% 1.65/1.81     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.81       ( ![D:$i]:
% 1.65/1.81         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.65/1.81             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.65/1.81           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.65/1.81               ( r2_relset_1 @
% 1.65/1.81                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.65/1.81                 ( k6_partfun1 @ A ) ) & 
% 1.65/1.81               ( v2_funct_1 @ C ) ) =>
% 1.65/1.81             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.65/1.81               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.65/1.81  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.81    (~( ![A:$i,B:$i,C:$i]:
% 1.65/1.81        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.81            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.81          ( ![D:$i]:
% 1.65/1.81            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.65/1.81                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.65/1.81              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.65/1.81                  ( r2_relset_1 @
% 1.65/1.81                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.65/1.81                    ( k6_partfun1 @ A ) ) & 
% 1.65/1.81                  ( v2_funct_1 @ C ) ) =>
% 1.65/1.81                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.65/1.81                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.65/1.81    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.65/1.81  thf('0', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf(t35_funct_2, axiom,
% 1.65/1.81    (![A:$i,B:$i,C:$i]:
% 1.65/1.81     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.81       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.65/1.81         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.65/1.81           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.65/1.81             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.65/1.81  thf('1', plain,
% 1.65/1.81      (![X54 : $i, X55 : $i, X56 : $i]:
% 1.65/1.81         (((X54) = (k1_xboole_0))
% 1.65/1.81          | ~ (v1_funct_1 @ X55)
% 1.65/1.81          | ~ (v1_funct_2 @ X55 @ X56 @ X54)
% 1.65/1.81          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X54)))
% 1.65/1.81          | ((k5_relat_1 @ X55 @ (k2_funct_1 @ X55)) = (k6_partfun1 @ X56))
% 1.65/1.81          | ~ (v2_funct_1 @ X55)
% 1.65/1.81          | ((k2_relset_1 @ X56 @ X54 @ X55) != (X54)))),
% 1.65/1.81      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.65/1.81  thf(redefinition_k6_partfun1, axiom,
% 1.65/1.81    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.65/1.81  thf('2', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 1.65/1.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.81  thf('3', plain,
% 1.65/1.81      (![X54 : $i, X55 : $i, X56 : $i]:
% 1.65/1.81         (((X54) = (k1_xboole_0))
% 1.65/1.81          | ~ (v1_funct_1 @ X55)
% 1.65/1.81          | ~ (v1_funct_2 @ X55 @ X56 @ X54)
% 1.65/1.81          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X54)))
% 1.65/1.81          | ((k5_relat_1 @ X55 @ (k2_funct_1 @ X55)) = (k6_relat_1 @ X56))
% 1.65/1.81          | ~ (v2_funct_1 @ X55)
% 1.65/1.81          | ((k2_relset_1 @ X56 @ X54 @ X55) != (X54)))),
% 1.65/1.81      inference('demod', [status(thm)], ['1', '2'])).
% 1.65/1.81  thf('4', plain,
% 1.65/1.81      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) != (sk_A))
% 1.65/1.81        | ~ (v2_funct_1 @ sk_D)
% 1.65/1.81        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B_1))
% 1.65/1.81        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 1.65/1.81        | ~ (v1_funct_1 @ sk_D)
% 1.65/1.81        | ((sk_A) = (k1_xboole_0)))),
% 1.65/1.81      inference('sup-', [status(thm)], ['0', '3'])).
% 1.65/1.81  thf('5', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf(redefinition_k2_relset_1, axiom,
% 1.65/1.81    (![A:$i,B:$i,C:$i]:
% 1.65/1.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.81       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.65/1.81  thf('6', plain,
% 1.65/1.81      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.65/1.81         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 1.65/1.81          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.65/1.81      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.65/1.81  thf('7', plain,
% 1.65/1.81      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.65/1.81      inference('sup-', [status(thm)], ['5', '6'])).
% 1.65/1.81  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('10', plain,
% 1.65/1.81      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.65/1.81        | ~ (v2_funct_1 @ sk_D)
% 1.65/1.81        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B_1))
% 1.65/1.81        | ((sk_A) = (k1_xboole_0)))),
% 1.65/1.81      inference('demod', [status(thm)], ['4', '7', '8', '9'])).
% 1.65/1.81  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('12', plain,
% 1.65/1.81      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.65/1.81        | ~ (v2_funct_1 @ sk_D)
% 1.65/1.81        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B_1)))),
% 1.65/1.81      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 1.65/1.81  thf('13', plain,
% 1.65/1.81      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.81        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 1.65/1.81        (k6_partfun1 @ sk_A))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('14', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 1.65/1.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.81  thf('15', plain,
% 1.65/1.81      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.81        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 1.65/1.81        (k6_relat_1 @ sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['13', '14'])).
% 1.65/1.81  thf('16', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf(t24_funct_2, axiom,
% 1.65/1.81    (![A:$i,B:$i,C:$i]:
% 1.65/1.81     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.81       ( ![D:$i]:
% 1.65/1.81         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.65/1.81             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.65/1.81           ( ( r2_relset_1 @
% 1.65/1.81               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.65/1.81               ( k6_partfun1 @ B ) ) =>
% 1.65/1.81             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.65/1.81  thf('17', plain,
% 1.65/1.81      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.65/1.81         (~ (v1_funct_1 @ X38)
% 1.65/1.81          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 1.65/1.81          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.65/1.81          | ~ (r2_relset_1 @ X39 @ X39 @ 
% 1.65/1.81               (k1_partfun1 @ X39 @ X40 @ X40 @ X39 @ X38 @ X41) @ 
% 1.65/1.81               (k6_partfun1 @ X39))
% 1.65/1.81          | ((k2_relset_1 @ X40 @ X39 @ X41) = (X39))
% 1.65/1.81          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 1.65/1.81          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 1.65/1.81          | ~ (v1_funct_1 @ X41))),
% 1.65/1.81      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.65/1.81  thf('18', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 1.65/1.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.81  thf('19', plain,
% 1.65/1.81      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.65/1.81         (~ (v1_funct_1 @ X38)
% 1.65/1.81          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 1.65/1.81          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.65/1.81          | ~ (r2_relset_1 @ X39 @ X39 @ 
% 1.65/1.81               (k1_partfun1 @ X39 @ X40 @ X40 @ X39 @ X38 @ X41) @ 
% 1.65/1.81               (k6_relat_1 @ X39))
% 1.65/1.81          | ((k2_relset_1 @ X40 @ X39 @ X41) = (X39))
% 1.65/1.81          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 1.65/1.81          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 1.65/1.81          | ~ (v1_funct_1 @ X41))),
% 1.65/1.81      inference('demod', [status(thm)], ['17', '18'])).
% 1.65/1.81  thf('20', plain,
% 1.65/1.81      (![X0 : $i]:
% 1.65/1.81         (~ (v1_funct_1 @ X0)
% 1.65/1.81          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 1.65/1.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 1.65/1.81          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 1.65/1.81          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.81               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ X0) @ 
% 1.65/1.81               (k6_relat_1 @ sk_A))
% 1.65/1.81          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 1.65/1.81          | ~ (v1_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('sup-', [status(thm)], ['16', '19'])).
% 1.65/1.81  thf('21', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('22', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('23', plain,
% 1.65/1.81      (![X0 : $i]:
% 1.65/1.81         (~ (v1_funct_1 @ X0)
% 1.65/1.81          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 1.65/1.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 1.65/1.81          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 1.65/1.81          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.81               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ X0) @ 
% 1.65/1.81               (k6_relat_1 @ sk_A)))),
% 1.65/1.81      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.65/1.81  thf('24', plain,
% 1.65/1.81      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 1.65/1.81        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 1.65/1.81        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 1.65/1.81        | ~ (v1_funct_1 @ sk_D))),
% 1.65/1.81      inference('sup-', [status(thm)], ['15', '23'])).
% 1.65/1.81  thf('25', plain,
% 1.65/1.81      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.65/1.81      inference('sup-', [status(thm)], ['5', '6'])).
% 1.65/1.81  thf('26', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('27', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('29', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 1.65/1.81  thf('30', plain,
% 1.65/1.81      ((((sk_A) != (sk_A))
% 1.65/1.81        | ~ (v2_funct_1 @ sk_D)
% 1.65/1.81        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B_1)))),
% 1.65/1.81      inference('demod', [status(thm)], ['12', '29'])).
% 1.65/1.81  thf('31', plain,
% 1.65/1.81      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B_1))
% 1.65/1.81        | ~ (v2_funct_1 @ sk_D))),
% 1.65/1.81      inference('simplify', [status(thm)], ['30'])).
% 1.65/1.81  thf('32', plain,
% 1.65/1.81      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.81        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 1.65/1.81        (k6_relat_1 @ sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['13', '14'])).
% 1.65/1.81  thf('33', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('34', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf(dt_k1_partfun1, axiom,
% 1.65/1.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.65/1.81     ( ( ( v1_funct_1 @ E ) & 
% 1.65/1.81         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.81         ( v1_funct_1 @ F ) & 
% 1.65/1.81         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.65/1.81       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.65/1.81         ( m1_subset_1 @
% 1.65/1.81           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.65/1.81           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.65/1.81  thf('35', plain,
% 1.65/1.81      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.65/1.81         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.65/1.81          | ~ (v1_funct_1 @ X25)
% 1.65/1.81          | ~ (v1_funct_1 @ X28)
% 1.65/1.81          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.65/1.81          | (m1_subset_1 @ (k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 1.65/1.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 1.65/1.81      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.65/1.81  thf('36', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.81         ((m1_subset_1 @ 
% 1.65/1.81           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 1.65/1.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.65/1.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.65/1.81          | ~ (v1_funct_1 @ X1)
% 1.65/1.81          | ~ (v1_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('sup-', [status(thm)], ['34', '35'])).
% 1.65/1.81  thf('37', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('38', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.81         ((m1_subset_1 @ 
% 1.65/1.81           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 1.65/1.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.65/1.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.65/1.81          | ~ (v1_funct_1 @ X1))),
% 1.65/1.81      inference('demod', [status(thm)], ['36', '37'])).
% 1.65/1.81  thf('39', plain,
% 1.65/1.81      ((~ (v1_funct_1 @ sk_D)
% 1.65/1.81        | (m1_subset_1 @ 
% 1.65/1.81           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 1.65/1.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.65/1.81      inference('sup-', [status(thm)], ['33', '38'])).
% 1.65/1.81  thf('40', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('41', plain,
% 1.65/1.81      ((m1_subset_1 @ 
% 1.65/1.81        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 1.65/1.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.65/1.81      inference('demod', [status(thm)], ['39', '40'])).
% 1.65/1.81  thf(redefinition_r2_relset_1, axiom,
% 1.65/1.81    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.81     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.81       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.65/1.81  thf('42', plain,
% 1.65/1.81      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.65/1.81         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.65/1.81          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.65/1.81          | ((X21) = (X24))
% 1.65/1.81          | ~ (r2_relset_1 @ X22 @ X23 @ X21 @ X24))),
% 1.65/1.81      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.65/1.81  thf('43', plain,
% 1.65/1.81      (![X0 : $i]:
% 1.65/1.81         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.81             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ X0)
% 1.65/1.81          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 1.65/1.81              = (X0))
% 1.65/1.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.65/1.81      inference('sup-', [status(thm)], ['41', '42'])).
% 1.65/1.81  thf('44', plain,
% 1.65/1.81      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.65/1.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.65/1.81        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 1.65/1.81            = (k6_relat_1 @ sk_A)))),
% 1.65/1.81      inference('sup-', [status(thm)], ['32', '43'])).
% 1.65/1.81  thf('45', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf(t31_funct_2, axiom,
% 1.65/1.81    (![A:$i,B:$i,C:$i]:
% 1.65/1.81     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.81       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.65/1.81         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.65/1.81           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.65/1.81           ( m1_subset_1 @
% 1.65/1.81             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.65/1.81  thf('46', plain,
% 1.65/1.81      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.65/1.81         (~ (v2_funct_1 @ X51)
% 1.65/1.81          | ((k2_relset_1 @ X53 @ X52 @ X51) != (X52))
% 1.65/1.81          | (m1_subset_1 @ (k2_funct_1 @ X51) @ 
% 1.65/1.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 1.65/1.81          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52)))
% 1.65/1.81          | ~ (v1_funct_2 @ X51 @ X53 @ X52)
% 1.65/1.81          | ~ (v1_funct_1 @ X51))),
% 1.65/1.81      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.65/1.81  thf('47', plain,
% 1.65/1.81      ((~ (v1_funct_1 @ sk_C_1)
% 1.65/1.81        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 1.65/1.81        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.65/1.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 1.65/1.81        | ((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) != (sk_B_1))
% 1.65/1.81        | ~ (v2_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('sup-', [status(thm)], ['45', '46'])).
% 1.65/1.81  thf('48', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('49', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('50', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('51', plain, ((v2_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('52', plain,
% 1.65/1.81      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.65/1.81         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 1.65/1.81        | ((sk_B_1) != (sk_B_1)))),
% 1.65/1.81      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 1.65/1.81  thf('53', plain,
% 1.65/1.81      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.65/1.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.65/1.81      inference('simplify', [status(thm)], ['52'])).
% 1.65/1.81  thf('54', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.81         ((m1_subset_1 @ 
% 1.65/1.81           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 1.65/1.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.65/1.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.65/1.81          | ~ (v1_funct_1 @ X1))),
% 1.65/1.81      inference('demod', [status(thm)], ['36', '37'])).
% 1.65/1.81  thf('55', plain,
% 1.65/1.81      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.65/1.81        | (m1_subset_1 @ 
% 1.65/1.81           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ 
% 1.65/1.81            (k2_funct_1 @ sk_C_1)) @ 
% 1.65/1.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.65/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.65/1.81  thf('56', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('57', plain,
% 1.65/1.81      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.65/1.81         (~ (v2_funct_1 @ X51)
% 1.65/1.81          | ((k2_relset_1 @ X53 @ X52 @ X51) != (X52))
% 1.65/1.81          | (v1_funct_1 @ (k2_funct_1 @ X51))
% 1.65/1.81          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52)))
% 1.65/1.81          | ~ (v1_funct_2 @ X51 @ X53 @ X52)
% 1.65/1.81          | ~ (v1_funct_1 @ X51))),
% 1.65/1.81      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.65/1.81  thf('58', plain,
% 1.65/1.81      ((~ (v1_funct_1 @ sk_C_1)
% 1.65/1.81        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 1.65/1.81        | (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.65/1.81        | ((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) != (sk_B_1))
% 1.65/1.81        | ~ (v2_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('sup-', [status(thm)], ['56', '57'])).
% 1.65/1.81  thf('59', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('60', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('61', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('62', plain, ((v2_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('63', plain,
% 1.65/1.81      (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)) | ((sk_B_1) != (sk_B_1)))),
% 1.65/1.81      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 1.65/1.81  thf('64', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('simplify', [status(thm)], ['63'])).
% 1.65/1.81  thf('65', plain,
% 1.65/1.81      ((m1_subset_1 @ 
% 1.65/1.81        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ 
% 1.65/1.81         (k2_funct_1 @ sk_C_1)) @ 
% 1.65/1.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.65/1.81      inference('demod', [status(thm)], ['55', '64'])).
% 1.65/1.81  thf('66', plain,
% 1.65/1.81      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.65/1.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.65/1.81      inference('simplify', [status(thm)], ['52'])).
% 1.65/1.81  thf('67', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf(redefinition_k1_partfun1, axiom,
% 1.65/1.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.65/1.81     ( ( ( v1_funct_1 @ E ) & 
% 1.65/1.81         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.81         ( v1_funct_1 @ F ) & 
% 1.65/1.81         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.65/1.81       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.65/1.81  thf('68', plain,
% 1.65/1.81      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.65/1.81         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.65/1.81          | ~ (v1_funct_1 @ X31)
% 1.65/1.81          | ~ (v1_funct_1 @ X34)
% 1.65/1.81          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.65/1.81          | ((k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34)
% 1.65/1.81              = (k5_relat_1 @ X31 @ X34)))),
% 1.65/1.81      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.65/1.81  thf('69', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.81         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 1.65/1.81            = (k5_relat_1 @ sk_C_1 @ X0))
% 1.65/1.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.65/1.81          | ~ (v1_funct_1 @ X0)
% 1.65/1.81          | ~ (v1_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('sup-', [status(thm)], ['67', '68'])).
% 1.65/1.81  thf('70', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('71', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.81         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 1.65/1.81            = (k5_relat_1 @ sk_C_1 @ X0))
% 1.65/1.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.65/1.81          | ~ (v1_funct_1 @ X0))),
% 1.65/1.81      inference('demod', [status(thm)], ['69', '70'])).
% 1.65/1.81  thf('72', plain,
% 1.65/1.81      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.65/1.81        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ 
% 1.65/1.81            (k2_funct_1 @ sk_C_1))
% 1.65/1.81            = (k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.65/1.81      inference('sup-', [status(thm)], ['66', '71'])).
% 1.65/1.81  thf('73', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('simplify', [status(thm)], ['63'])).
% 1.65/1.81  thf('74', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('75', plain,
% 1.65/1.81      (![X54 : $i, X55 : $i, X56 : $i]:
% 1.65/1.81         (((X54) = (k1_xboole_0))
% 1.65/1.81          | ~ (v1_funct_1 @ X55)
% 1.65/1.81          | ~ (v1_funct_2 @ X55 @ X56 @ X54)
% 1.65/1.81          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X54)))
% 1.65/1.81          | ((k5_relat_1 @ X55 @ (k2_funct_1 @ X55)) = (k6_relat_1 @ X56))
% 1.65/1.81          | ~ (v2_funct_1 @ X55)
% 1.65/1.81          | ((k2_relset_1 @ X56 @ X54 @ X55) != (X54)))),
% 1.65/1.81      inference('demod', [status(thm)], ['1', '2'])).
% 1.65/1.81  thf('76', plain,
% 1.65/1.81      ((((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) != (sk_B_1))
% 1.65/1.81        | ~ (v2_funct_1 @ sk_C_1)
% 1.65/1.81        | ((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1)) = (k6_relat_1 @ sk_A))
% 1.65/1.81        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 1.65/1.81        | ~ (v1_funct_1 @ sk_C_1)
% 1.65/1.81        | ((sk_B_1) = (k1_xboole_0)))),
% 1.65/1.81      inference('sup-', [status(thm)], ['74', '75'])).
% 1.65/1.81  thf('77', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('78', plain, ((v2_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('79', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('80', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('81', plain,
% 1.65/1.81      ((((sk_B_1) != (sk_B_1))
% 1.65/1.81        | ((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1)) = (k6_relat_1 @ sk_A))
% 1.65/1.81        | ((sk_B_1) = (k1_xboole_0)))),
% 1.65/1.81      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 1.65/1.81  thf('82', plain,
% 1.65/1.81      ((((sk_B_1) = (k1_xboole_0))
% 1.65/1.81        | ((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1)) = (k6_relat_1 @ sk_A)))),
% 1.65/1.81      inference('simplify', [status(thm)], ['81'])).
% 1.65/1.81  thf('83', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('84', plain,
% 1.65/1.81      (((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1)) = (k6_relat_1 @ sk_A))),
% 1.65/1.81      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 1.65/1.81  thf('85', plain,
% 1.65/1.81      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ 
% 1.65/1.81         (k2_funct_1 @ sk_C_1)) = (k6_relat_1 @ sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['72', '73', '84'])).
% 1.65/1.81  thf('86', plain,
% 1.65/1.81      ((m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.65/1.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.65/1.81      inference('demod', [status(thm)], ['65', '85'])).
% 1.65/1.81  thf('87', plain,
% 1.65/1.81      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 1.65/1.81         = (k6_relat_1 @ sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['44', '86'])).
% 1.65/1.81  thf('88', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf(t30_funct_2, axiom,
% 1.65/1.81    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.81     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.81         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.65/1.81       ( ![E:$i]:
% 1.65/1.81         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.65/1.81             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.65/1.81           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.65/1.81               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.65/1.81             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.65/1.81               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.65/1.81  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.65/1.81  thf(zf_stmt_2, axiom,
% 1.65/1.81    (![C:$i,B:$i]:
% 1.65/1.81     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.65/1.81       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.65/1.81  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.65/1.81  thf(zf_stmt_4, axiom,
% 1.65/1.81    (![E:$i,D:$i]:
% 1.65/1.81     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.65/1.81  thf(zf_stmt_5, axiom,
% 1.65/1.81    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.81     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.65/1.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.81       ( ![E:$i]:
% 1.65/1.81         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.65/1.81             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.65/1.81           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.65/1.81               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.65/1.81             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.65/1.81  thf('89', plain,
% 1.65/1.81      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 1.65/1.81         (~ (v1_funct_1 @ X46)
% 1.65/1.81          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 1.65/1.81          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.65/1.81          | (zip_tseitin_0 @ X46 @ X49)
% 1.65/1.81          | ~ (v2_funct_1 @ (k1_partfun1 @ X50 @ X47 @ X47 @ X48 @ X49 @ X46))
% 1.65/1.81          | (zip_tseitin_1 @ X48 @ X47)
% 1.65/1.81          | ((k2_relset_1 @ X50 @ X47 @ X49) != (X47))
% 1.65/1.81          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X47)))
% 1.65/1.81          | ~ (v1_funct_2 @ X49 @ X50 @ X47)
% 1.65/1.81          | ~ (v1_funct_1 @ X49))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.65/1.81  thf('90', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         (~ (v1_funct_1 @ X0)
% 1.65/1.81          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 1.65/1.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 1.65/1.81          | ((k2_relset_1 @ X1 @ sk_B_1 @ X0) != (sk_B_1))
% 1.65/1.81          | (zip_tseitin_1 @ sk_A @ sk_B_1)
% 1.65/1.81          | ~ (v2_funct_1 @ 
% 1.65/1.81               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 1.65/1.81          | (zip_tseitin_0 @ sk_D @ X0)
% 1.65/1.81          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 1.65/1.81          | ~ (v1_funct_1 @ sk_D))),
% 1.65/1.81      inference('sup-', [status(thm)], ['88', '89'])).
% 1.65/1.81  thf('91', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('92', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('93', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         (~ (v1_funct_1 @ X0)
% 1.65/1.81          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 1.65/1.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 1.65/1.81          | ((k2_relset_1 @ X1 @ sk_B_1 @ X0) != (sk_B_1))
% 1.65/1.81          | (zip_tseitin_1 @ sk_A @ sk_B_1)
% 1.65/1.81          | ~ (v2_funct_1 @ 
% 1.65/1.81               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 1.65/1.81          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.65/1.81      inference('demod', [status(thm)], ['90', '91', '92'])).
% 1.65/1.81  thf('94', plain,
% 1.65/1.81      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.65/1.81        | (zip_tseitin_0 @ sk_D @ sk_C_1)
% 1.65/1.81        | (zip_tseitin_1 @ sk_A @ sk_B_1)
% 1.65/1.81        | ((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) != (sk_B_1))
% 1.65/1.81        | ~ (m1_subset_1 @ sk_C_1 @ 
% 1.65/1.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 1.65/1.81        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 1.65/1.81        | ~ (v1_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('sup-', [status(thm)], ['87', '93'])).
% 1.65/1.81  thf(t62_funct_1, axiom,
% 1.65/1.81    (![A:$i]:
% 1.65/1.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.81       ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.65/1.81  thf('95', plain,
% 1.65/1.81      (![X12 : $i]:
% 1.65/1.81         (~ (v2_funct_1 @ X12)
% 1.65/1.81          | (v2_funct_1 @ (k2_funct_1 @ X12))
% 1.65/1.81          | ~ (v1_funct_1 @ X12)
% 1.65/1.81          | ~ (v1_relat_1 @ X12))),
% 1.65/1.81      inference('cnf', [status(esa)], [t62_funct_1])).
% 1.65/1.81  thf('96', plain,
% 1.65/1.81      (((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1)) = (k6_relat_1 @ sk_A))),
% 1.65/1.81      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 1.65/1.81  thf(fc7_funct_1, axiom,
% 1.65/1.81    (![A:$i,B:$i]:
% 1.65/1.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) & 
% 1.65/1.81         ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) & ( v2_funct_1 @ B ) ) =>
% 1.65/1.81       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 1.65/1.81         ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 1.65/1.81  thf('97', plain,
% 1.65/1.81      (![X1 : $i, X2 : $i]:
% 1.65/1.81         (~ (v2_funct_1 @ X1)
% 1.65/1.81          | ~ (v1_funct_1 @ X1)
% 1.65/1.81          | ~ (v1_relat_1 @ X1)
% 1.65/1.81          | ~ (v1_relat_1 @ X2)
% 1.65/1.81          | ~ (v1_funct_1 @ X2)
% 1.65/1.81          | ~ (v2_funct_1 @ X2)
% 1.65/1.81          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X2)))),
% 1.65/1.81      inference('cnf', [status(esa)], [fc7_funct_1])).
% 1.65/1.81  thf('98', plain,
% 1.65/1.81      (((v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.65/1.81        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.65/1.81        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.65/1.81        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 1.65/1.81        | ~ (v1_relat_1 @ sk_C_1)
% 1.65/1.81        | ~ (v1_funct_1 @ sk_C_1)
% 1.65/1.81        | ~ (v2_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('sup+', [status(thm)], ['96', '97'])).
% 1.65/1.81  thf('99', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('simplify', [status(thm)], ['63'])).
% 1.65/1.81  thf('100', plain,
% 1.65/1.81      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.65/1.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.65/1.81      inference('simplify', [status(thm)], ['52'])).
% 1.65/1.81  thf(cc1_relset_1, axiom,
% 1.65/1.81    (![A:$i,B:$i,C:$i]:
% 1.65/1.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.81       ( v1_relat_1 @ C ) ))).
% 1.65/1.81  thf('101', plain,
% 1.65/1.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.65/1.81         ((v1_relat_1 @ X15)
% 1.65/1.81          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.65/1.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.65/1.81  thf('102', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('sup-', [status(thm)], ['100', '101'])).
% 1.65/1.81  thf('103', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('104', plain,
% 1.65/1.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.65/1.81         ((v1_relat_1 @ X15)
% 1.65/1.81          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.65/1.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.65/1.81  thf('105', plain, ((v1_relat_1 @ sk_C_1)),
% 1.65/1.81      inference('sup-', [status(thm)], ['103', '104'])).
% 1.65/1.81  thf('106', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('107', plain, ((v2_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('108', plain,
% 1.65/1.81      (((v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.65/1.81        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.65/1.81      inference('demod', [status(thm)],
% 1.65/1.81                ['98', '99', '102', '105', '106', '107'])).
% 1.65/1.81  thf('109', plain,
% 1.65/1.81      ((~ (v1_relat_1 @ sk_C_1)
% 1.65/1.81        | ~ (v1_funct_1 @ sk_C_1)
% 1.65/1.81        | ~ (v2_funct_1 @ sk_C_1)
% 1.65/1.81        | (v2_funct_1 @ (k6_relat_1 @ sk_A)))),
% 1.65/1.81      inference('sup-', [status(thm)], ['95', '108'])).
% 1.65/1.81  thf('110', plain, ((v1_relat_1 @ sk_C_1)),
% 1.65/1.81      inference('sup-', [status(thm)], ['103', '104'])).
% 1.65/1.81  thf('111', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('112', plain, ((v2_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('113', plain, ((v2_funct_1 @ (k6_relat_1 @ sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 1.65/1.81  thf('114', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('115', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('116', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('117', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('118', plain,
% 1.65/1.81      (((zip_tseitin_0 @ sk_D @ sk_C_1)
% 1.65/1.81        | (zip_tseitin_1 @ sk_A @ sk_B_1)
% 1.65/1.81        | ((sk_B_1) != (sk_B_1)))),
% 1.65/1.81      inference('demod', [status(thm)],
% 1.65/1.81                ['94', '113', '114', '115', '116', '117'])).
% 1.65/1.81  thf('119', plain,
% 1.65/1.81      (((zip_tseitin_1 @ sk_A @ sk_B_1) | (zip_tseitin_0 @ sk_D @ sk_C_1))),
% 1.65/1.81      inference('simplify', [status(thm)], ['118'])).
% 1.65/1.81  thf('120', plain,
% 1.65/1.81      (![X44 : $i, X45 : $i]:
% 1.65/1.81         (((X44) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X44 @ X45))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.65/1.81  thf('121', plain,
% 1.65/1.81      (((zip_tseitin_0 @ sk_D @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 1.65/1.81      inference('sup-', [status(thm)], ['119', '120'])).
% 1.65/1.81  thf('122', plain, (((sk_A) != (k1_xboole_0))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('123', plain, ((zip_tseitin_0 @ sk_D @ sk_C_1)),
% 1.65/1.81      inference('simplify_reflect-', [status(thm)], ['121', '122'])).
% 1.65/1.81  thf('124', plain,
% 1.65/1.81      (![X42 : $i, X43 : $i]:
% 1.65/1.81         ((v2_funct_1 @ X43) | ~ (zip_tseitin_0 @ X43 @ X42))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.65/1.81  thf('125', plain, ((v2_funct_1 @ sk_D)),
% 1.65/1.81      inference('sup-', [status(thm)], ['123', '124'])).
% 1.65/1.81  thf('126', plain,
% 1.65/1.81      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B_1))),
% 1.65/1.81      inference('demod', [status(thm)], ['31', '125'])).
% 1.65/1.81  thf(t58_funct_1, axiom,
% 1.65/1.81    (![A:$i]:
% 1.65/1.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.81       ( ( v2_funct_1 @ A ) =>
% 1.65/1.81         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.65/1.81             ( k1_relat_1 @ A ) ) & 
% 1.65/1.81           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.65/1.81             ( k1_relat_1 @ A ) ) ) ) ))).
% 1.65/1.81  thf('127', plain,
% 1.65/1.81      (![X9 : $i]:
% 1.65/1.81         (~ (v2_funct_1 @ X9)
% 1.65/1.81          | ((k2_relat_1 @ (k5_relat_1 @ X9 @ (k2_funct_1 @ X9)))
% 1.65/1.81              = (k1_relat_1 @ X9))
% 1.65/1.81          | ~ (v1_funct_1 @ X9)
% 1.65/1.81          | ~ (v1_relat_1 @ X9))),
% 1.65/1.81      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.65/1.81  thf('128', plain,
% 1.65/1.81      ((((k2_relat_1 @ (k6_relat_1 @ sk_B_1)) = (k1_relat_1 @ sk_D))
% 1.65/1.81        | ~ (v1_relat_1 @ sk_D)
% 1.65/1.81        | ~ (v1_funct_1 @ sk_D)
% 1.65/1.81        | ~ (v2_funct_1 @ sk_D))),
% 1.65/1.81      inference('sup+', [status(thm)], ['126', '127'])).
% 1.65/1.81  thf('129', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('130', plain,
% 1.65/1.81      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.65/1.81         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 1.65/1.81          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.65/1.81      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.65/1.81  thf('131', plain,
% 1.65/1.81      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 1.65/1.81      inference('sup-', [status(thm)], ['129', '130'])).
% 1.65/1.81  thf('132', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('133', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 1.65/1.81      inference('sup+', [status(thm)], ['131', '132'])).
% 1.65/1.81  thf(t61_funct_1, axiom,
% 1.65/1.81    (![A:$i]:
% 1.65/1.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.81       ( ( v2_funct_1 @ A ) =>
% 1.65/1.81         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.65/1.81             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.65/1.81           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.65/1.81             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.65/1.81  thf('134', plain,
% 1.65/1.81      (![X11 : $i]:
% 1.65/1.81         (~ (v2_funct_1 @ X11)
% 1.65/1.81          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 1.65/1.81              = (k6_relat_1 @ (k2_relat_1 @ X11)))
% 1.65/1.81          | ~ (v1_funct_1 @ X11)
% 1.65/1.81          | ~ (v1_relat_1 @ X11))),
% 1.65/1.81      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.65/1.81  thf(t59_funct_1, axiom,
% 1.65/1.81    (![A:$i]:
% 1.65/1.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.81       ( ( v2_funct_1 @ A ) =>
% 1.65/1.81         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 1.65/1.81             ( k2_relat_1 @ A ) ) & 
% 1.65/1.81           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 1.65/1.81             ( k2_relat_1 @ A ) ) ) ) ))).
% 1.65/1.81  thf('135', plain,
% 1.65/1.81      (![X10 : $i]:
% 1.65/1.81         (~ (v2_funct_1 @ X10)
% 1.65/1.81          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X10) @ X10))
% 1.65/1.81              = (k2_relat_1 @ X10))
% 1.65/1.81          | ~ (v1_funct_1 @ X10)
% 1.65/1.81          | ~ (v1_relat_1 @ X10))),
% 1.65/1.81      inference('cnf', [status(esa)], [t59_funct_1])).
% 1.65/1.81  thf('136', plain,
% 1.65/1.81      (![X0 : $i]:
% 1.65/1.81         (((k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (k2_relat_1 @ X0))
% 1.65/1.81          | ~ (v1_relat_1 @ X0)
% 1.65/1.81          | ~ (v1_funct_1 @ X0)
% 1.65/1.81          | ~ (v2_funct_1 @ X0)
% 1.65/1.81          | ~ (v1_relat_1 @ X0)
% 1.65/1.81          | ~ (v1_funct_1 @ X0)
% 1.65/1.81          | ~ (v2_funct_1 @ X0))),
% 1.65/1.81      inference('sup+', [status(thm)], ['134', '135'])).
% 1.65/1.81  thf('137', plain,
% 1.65/1.81      (![X0 : $i]:
% 1.65/1.81         (~ (v2_funct_1 @ X0)
% 1.65/1.81          | ~ (v1_funct_1 @ X0)
% 1.65/1.81          | ~ (v1_relat_1 @ X0)
% 1.65/1.81          | ((k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 1.65/1.81              = (k2_relat_1 @ X0)))),
% 1.65/1.81      inference('simplify', [status(thm)], ['136'])).
% 1.65/1.81  thf('138', plain,
% 1.65/1.81      ((((k2_relat_1 @ (k6_relat_1 @ sk_B_1)) = (k2_relat_1 @ sk_C_1))
% 1.65/1.81        | ~ (v1_relat_1 @ sk_C_1)
% 1.65/1.81        | ~ (v1_funct_1 @ sk_C_1)
% 1.65/1.81        | ~ (v2_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('sup+', [status(thm)], ['133', '137'])).
% 1.65/1.81  thf('139', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 1.65/1.81      inference('sup+', [status(thm)], ['131', '132'])).
% 1.65/1.81  thf('140', plain, ((v1_relat_1 @ sk_C_1)),
% 1.65/1.81      inference('sup-', [status(thm)], ['103', '104'])).
% 1.65/1.81  thf('141', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('142', plain, ((v2_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('143', plain, (((k2_relat_1 @ (k6_relat_1 @ sk_B_1)) = (sk_B_1))),
% 1.65/1.81      inference('demod', [status(thm)], ['138', '139', '140', '141', '142'])).
% 1.65/1.81  thf('144', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('145', plain,
% 1.65/1.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.65/1.81         ((v1_relat_1 @ X15)
% 1.65/1.81          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.65/1.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.65/1.81  thf('146', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.81      inference('sup-', [status(thm)], ['144', '145'])).
% 1.65/1.81  thf('147', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('148', plain, ((v2_funct_1 @ sk_D)),
% 1.65/1.81      inference('sup-', [status(thm)], ['123', '124'])).
% 1.65/1.81  thf('149', plain, (((sk_B_1) = (k1_relat_1 @ sk_D))),
% 1.65/1.81      inference('demod', [status(thm)], ['128', '143', '146', '147', '148'])).
% 1.65/1.81  thf('150', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('151', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.81         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 1.65/1.81            = (k5_relat_1 @ sk_C_1 @ X0))
% 1.65/1.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.65/1.81          | ~ (v1_funct_1 @ X0))),
% 1.65/1.81      inference('demod', [status(thm)], ['69', '70'])).
% 1.65/1.81  thf('152', plain,
% 1.65/1.81      ((~ (v1_funct_1 @ sk_D)
% 1.65/1.81        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 1.65/1.81            = (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 1.65/1.81      inference('sup-', [status(thm)], ['150', '151'])).
% 1.65/1.81  thf('153', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('154', plain,
% 1.65/1.81      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 1.65/1.81         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 1.65/1.81      inference('demod', [status(thm)], ['152', '153'])).
% 1.65/1.81  thf('155', plain,
% 1.65/1.81      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 1.65/1.81         = (k6_relat_1 @ sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['44', '86'])).
% 1.65/1.81  thf('156', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.65/1.81      inference('sup+', [status(thm)], ['154', '155'])).
% 1.65/1.81  thf(t63_funct_1, axiom,
% 1.65/1.81    (![A:$i]:
% 1.65/1.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.81       ( ![B:$i]:
% 1.65/1.81         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.65/1.81           ( ( ( v2_funct_1 @ A ) & 
% 1.65/1.81               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.65/1.81               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 1.65/1.81             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.65/1.81  thf('157', plain,
% 1.65/1.81      (![X13 : $i, X14 : $i]:
% 1.65/1.81         (~ (v1_relat_1 @ X13)
% 1.65/1.81          | ~ (v1_funct_1 @ X13)
% 1.65/1.81          | ((X13) = (k2_funct_1 @ X14))
% 1.65/1.81          | ((k5_relat_1 @ X14 @ X13) != (k6_relat_1 @ (k1_relat_1 @ X14)))
% 1.65/1.81          | ((k2_relat_1 @ X14) != (k1_relat_1 @ X13))
% 1.65/1.81          | ~ (v2_funct_1 @ X14)
% 1.65/1.81          | ~ (v1_funct_1 @ X14)
% 1.65/1.81          | ~ (v1_relat_1 @ X14))),
% 1.65/1.81      inference('cnf', [status(esa)], [t63_funct_1])).
% 1.65/1.81  thf('158', plain,
% 1.65/1.81      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k1_relat_1 @ sk_C_1)))
% 1.65/1.81        | ~ (v1_relat_1 @ sk_C_1)
% 1.65/1.81        | ~ (v1_funct_1 @ sk_C_1)
% 1.65/1.81        | ~ (v2_funct_1 @ sk_C_1)
% 1.65/1.81        | ((k2_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 1.65/1.81        | ((sk_D) = (k2_funct_1 @ sk_C_1))
% 1.65/1.81        | ~ (v1_funct_1 @ sk_D)
% 1.65/1.81        | ~ (v1_relat_1 @ sk_D))),
% 1.65/1.81      inference('sup-', [status(thm)], ['156', '157'])).
% 1.65/1.81  thf('159', plain,
% 1.65/1.81      (![X12 : $i]:
% 1.65/1.81         (~ (v2_funct_1 @ X12)
% 1.65/1.81          | (v2_funct_1 @ (k2_funct_1 @ X12))
% 1.65/1.81          | ~ (v1_funct_1 @ X12)
% 1.65/1.81          | ~ (v1_relat_1 @ X12))),
% 1.65/1.81      inference('cnf', [status(esa)], [t62_funct_1])).
% 1.65/1.81  thf('160', plain,
% 1.65/1.81      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ 
% 1.65/1.81         (k2_funct_1 @ sk_C_1)) = (k6_relat_1 @ sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['72', '73', '84'])).
% 1.65/1.81  thf('161', plain,
% 1.65/1.81      (![X0 : $i]:
% 1.65/1.81         (~ (v1_funct_1 @ X0)
% 1.65/1.81          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 1.65/1.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 1.65/1.81          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 1.65/1.81          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.81               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ X0) @ 
% 1.65/1.81               (k6_relat_1 @ sk_A)))),
% 1.65/1.81      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.65/1.81  thf('162', plain,
% 1.65/1.81      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.65/1.81           (k6_relat_1 @ sk_A))
% 1.65/1.81        | ((k2_relset_1 @ sk_B_1 @ sk_A @ (k2_funct_1 @ sk_C_1)) = (sk_A))
% 1.65/1.81        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.65/1.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 1.65/1.81        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)
% 1.65/1.81        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.65/1.81      inference('sup-', [status(thm)], ['160', '161'])).
% 1.65/1.81  thf('163', plain,
% 1.65/1.81      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.65/1.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.65/1.81      inference('simplify', [status(thm)], ['52'])).
% 1.65/1.81  thf('164', plain,
% 1.65/1.81      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.65/1.81         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 1.65/1.81          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.65/1.81      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.65/1.81  thf('165', plain,
% 1.65/1.81      (((k2_relset_1 @ sk_B_1 @ sk_A @ (k2_funct_1 @ sk_C_1))
% 1.65/1.81         = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.65/1.81      inference('sup-', [status(thm)], ['163', '164'])).
% 1.65/1.81  thf('166', plain,
% 1.65/1.81      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.65/1.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.65/1.81      inference('simplify', [status(thm)], ['52'])).
% 1.65/1.81  thf('167', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('168', plain,
% 1.65/1.81      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.65/1.81         (~ (v2_funct_1 @ X51)
% 1.65/1.81          | ((k2_relset_1 @ X53 @ X52 @ X51) != (X52))
% 1.65/1.81          | (v1_funct_2 @ (k2_funct_1 @ X51) @ X52 @ X53)
% 1.65/1.81          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52)))
% 1.65/1.81          | ~ (v1_funct_2 @ X51 @ X53 @ X52)
% 1.65/1.81          | ~ (v1_funct_1 @ X51))),
% 1.65/1.81      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.65/1.81  thf('169', plain,
% 1.65/1.81      ((~ (v1_funct_1 @ sk_C_1)
% 1.65/1.81        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 1.65/1.81        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)
% 1.65/1.81        | ((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) != (sk_B_1))
% 1.65/1.81        | ~ (v2_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('sup-', [status(thm)], ['167', '168'])).
% 1.65/1.81  thf('170', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('171', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('172', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('173', plain, ((v2_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('174', plain,
% 1.65/1.81      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)
% 1.65/1.81        | ((sk_B_1) != (sk_B_1)))),
% 1.65/1.81      inference('demod', [status(thm)], ['169', '170', '171', '172', '173'])).
% 1.65/1.81  thf('175', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)),
% 1.65/1.81      inference('simplify', [status(thm)], ['174'])).
% 1.65/1.81  thf('176', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('simplify', [status(thm)], ['63'])).
% 1.65/1.81  thf('177', plain,
% 1.65/1.81      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.65/1.81           (k6_relat_1 @ sk_A))
% 1.65/1.81        | ((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (sk_A)))),
% 1.65/1.81      inference('demod', [status(thm)], ['162', '165', '166', '175', '176'])).
% 1.65/1.81  thf('178', plain,
% 1.65/1.81      ((m1_subset_1 @ 
% 1.65/1.81        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ 
% 1.65/1.81         (k2_funct_1 @ sk_C_1)) @ 
% 1.65/1.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.65/1.81      inference('demod', [status(thm)], ['55', '64'])).
% 1.65/1.81  thf('179', plain,
% 1.65/1.81      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.65/1.81         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.65/1.81          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.65/1.81          | (r2_relset_1 @ X22 @ X23 @ X21 @ X24)
% 1.65/1.81          | ((X21) != (X24)))),
% 1.65/1.81      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.65/1.81  thf('180', plain,
% 1.65/1.81      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.65/1.81         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 1.65/1.81          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.65/1.81      inference('simplify', [status(thm)], ['179'])).
% 1.65/1.81  thf('181', plain,
% 1.65/1.81      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.81        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ 
% 1.65/1.81         (k2_funct_1 @ sk_C_1)) @ 
% 1.65/1.81        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ 
% 1.65/1.81         (k2_funct_1 @ sk_C_1)))),
% 1.65/1.81      inference('sup-', [status(thm)], ['178', '180'])).
% 1.65/1.81  thf('182', plain,
% 1.65/1.81      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ 
% 1.65/1.81         (k2_funct_1 @ sk_C_1)) = (k6_relat_1 @ sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['72', '73', '84'])).
% 1.65/1.81  thf('183', plain,
% 1.65/1.81      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ 
% 1.65/1.81         (k2_funct_1 @ sk_C_1)) = (k6_relat_1 @ sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['72', '73', '84'])).
% 1.65/1.81  thf('184', plain,
% 1.65/1.81      ((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['181', '182', '183'])).
% 1.65/1.81  thf('185', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['177', '184'])).
% 1.65/1.81  thf('186', plain,
% 1.65/1.81      (![X0 : $i]:
% 1.65/1.81         (~ (v2_funct_1 @ X0)
% 1.65/1.81          | ~ (v1_funct_1 @ X0)
% 1.65/1.81          | ~ (v1_relat_1 @ X0)
% 1.65/1.81          | ((k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 1.65/1.81              = (k2_relat_1 @ X0)))),
% 1.65/1.81      inference('simplify', [status(thm)], ['136'])).
% 1.65/1.81  thf('187', plain,
% 1.65/1.81      ((((k2_relat_1 @ (k6_relat_1 @ sk_A))
% 1.65/1.81          = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 1.65/1.81        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 1.65/1.81        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.65/1.81        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.65/1.81      inference('sup+', [status(thm)], ['185', '186'])).
% 1.65/1.81  thf('188', plain,
% 1.65/1.81      (((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1)) = (k6_relat_1 @ sk_A))),
% 1.65/1.81      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 1.65/1.81  thf('189', plain,
% 1.65/1.81      (![X9 : $i]:
% 1.65/1.81         (~ (v2_funct_1 @ X9)
% 1.65/1.81          | ((k2_relat_1 @ (k5_relat_1 @ X9 @ (k2_funct_1 @ X9)))
% 1.65/1.81              = (k1_relat_1 @ X9))
% 1.65/1.81          | ~ (v1_funct_1 @ X9)
% 1.65/1.81          | ~ (v1_relat_1 @ X9))),
% 1.65/1.81      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.65/1.81  thf('190', plain,
% 1.65/1.81      ((((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (k1_relat_1 @ sk_C_1))
% 1.65/1.81        | ~ (v1_relat_1 @ sk_C_1)
% 1.65/1.81        | ~ (v1_funct_1 @ sk_C_1)
% 1.65/1.81        | ~ (v2_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('sup+', [status(thm)], ['188', '189'])).
% 1.65/1.81  thf('191', plain, ((v1_relat_1 @ sk_C_1)),
% 1.65/1.81      inference('sup-', [status(thm)], ['103', '104'])).
% 1.65/1.81  thf('192', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('193', plain, ((v2_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('194', plain,
% 1.65/1.81      (((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (k1_relat_1 @ sk_C_1))),
% 1.65/1.81      inference('demod', [status(thm)], ['190', '191', '192', '193'])).
% 1.65/1.81  thf('195', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['177', '184'])).
% 1.65/1.81  thf('196', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('sup-', [status(thm)], ['100', '101'])).
% 1.65/1.81  thf('197', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('simplify', [status(thm)], ['63'])).
% 1.65/1.81  thf('198', plain,
% 1.65/1.81      ((((k1_relat_1 @ sk_C_1) = (sk_A))
% 1.65/1.81        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.65/1.81      inference('demod', [status(thm)], ['187', '194', '195', '196', '197'])).
% 1.65/1.81  thf('199', plain,
% 1.65/1.81      ((~ (v1_relat_1 @ sk_C_1)
% 1.65/1.81        | ~ (v1_funct_1 @ sk_C_1)
% 1.65/1.81        | ~ (v2_funct_1 @ sk_C_1)
% 1.65/1.81        | ((k1_relat_1 @ sk_C_1) = (sk_A)))),
% 1.65/1.81      inference('sup-', [status(thm)], ['159', '198'])).
% 1.65/1.81  thf('200', plain, ((v1_relat_1 @ sk_C_1)),
% 1.65/1.81      inference('sup-', [status(thm)], ['103', '104'])).
% 1.65/1.81  thf('201', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('202', plain, ((v2_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('203', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['199', '200', '201', '202'])).
% 1.65/1.81  thf('204', plain, ((v1_relat_1 @ sk_C_1)),
% 1.65/1.81      inference('sup-', [status(thm)], ['103', '104'])).
% 1.65/1.81  thf('205', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('206', plain, ((v2_funct_1 @ sk_C_1)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('207', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 1.65/1.81      inference('sup+', [status(thm)], ['131', '132'])).
% 1.65/1.81  thf('208', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('209', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.81      inference('sup-', [status(thm)], ['144', '145'])).
% 1.65/1.81  thf('210', plain,
% 1.65/1.81      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 1.65/1.81        | ((sk_B_1) != (k1_relat_1 @ sk_D))
% 1.65/1.81        | ((sk_D) = (k2_funct_1 @ sk_C_1)))),
% 1.65/1.81      inference('demod', [status(thm)],
% 1.65/1.81                ['158', '203', '204', '205', '206', '207', '208', '209'])).
% 1.65/1.81  thf('211', plain,
% 1.65/1.81      ((((sk_D) = (k2_funct_1 @ sk_C_1)) | ((sk_B_1) != (k1_relat_1 @ sk_D)))),
% 1.65/1.81      inference('simplify', [status(thm)], ['210'])).
% 1.65/1.81  thf('212', plain, (((sk_D) != (k2_funct_1 @ sk_C_1))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('213', plain, (((sk_B_1) != (k1_relat_1 @ sk_D))),
% 1.65/1.81      inference('simplify_reflect-', [status(thm)], ['211', '212'])).
% 1.65/1.81  thf('214', plain, ($false),
% 1.65/1.81      inference('simplify_reflect-', [status(thm)], ['149', '213'])).
% 1.65/1.81  
% 1.65/1.81  % SZS output end Refutation
% 1.65/1.81  
% 1.65/1.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
