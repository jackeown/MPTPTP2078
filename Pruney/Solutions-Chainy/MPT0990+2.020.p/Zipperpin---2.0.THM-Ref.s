%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W52jKOT9cf

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:57 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :  489 (7615 expanded)
%              Number of leaves         :   51 (2232 expanded)
%              Depth                    :   45
%              Number of atoms          : 4852 (211497 expanded)
%              Number of equality atoms :  281 (14165 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( X53 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X55 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X53 ) ) )
      | ( ( k5_relat_1 @ X54 @ ( k2_funct_1 @ X54 ) )
        = ( k6_partfun1 @ X55 ) )
      | ~ ( v2_funct_1 @ X54 )
      | ( ( k2_relset_1 @ X55 @ X53 @ X54 )
       != X53 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('2',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','5','6','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_relset_1 @ X38 @ X38 @ ( k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40 ) @ ( k6_partfun1 @ X38 ) )
      | ( ( k2_relset_1 @ X39 @ X38 @ X40 )
        = X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('29',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('35',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','34'])).

thf('36',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('38',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('48',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('53',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X52 @ X51 @ X50 )
       != X51 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X50 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('62',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X52 @ X51 @ X50 )
       != X51 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('65',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('74',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( X53 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X55 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X53 ) ) )
      | ( ( k5_relat_1 @ X54 @ ( k2_funct_1 @ X54 ) )
        = ( k6_partfun1 @ X55 ) )
      | ~ ( v2_funct_1 @ X54 )
      | ( ( k2_relset_1 @ X55 @ X53 @ X54 )
       != X53 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('78',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','86'])).

thf('88',plain,(
    m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','71','87'])).

thf('89',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','88'])).

thf('90',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['37','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('92',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( zip_tseitin_0 @ X45 @ X48 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45 ) )
      | ( zip_tseitin_1 @ X47 @ X46 )
      | ( ( k2_relset_1 @ X49 @ X46 @ X48 )
       != X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['90','96'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('98',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('99',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('100',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X2 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['97','100','101','102','103','104'])).

thf('106',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('108',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v2_funct_1 @ X42 )
      | ~ ( zip_tseitin_0 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('112',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','112'])).

thf('114',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','88'])).

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

thf('115',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X7 @ X8 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('116',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('117',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X7 @ X8 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
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
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('120',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('121',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('122',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('126',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('132',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['118','119','122','123','128','129','132'])).

thf('134',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','88'])).

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

thf('136',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('137',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X2 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('139',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['120','121'])).

thf('140',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['126','127'])).

thf('142',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('144',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['137','138','139','140','141','142','143'])).

thf('145',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['134','144'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('146',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('147',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X52 @ X51 @ X50 )
       != X51 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X50 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('149',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('153',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['149','150','151','152'])).

thf('154',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('155',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['110','111'])).

thf('158',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['158','163'])).

thf('165',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X52 @ X51 @ X50 )
       != X51 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('167',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('171',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['167','168','169','170'])).

thf('172',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('173',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['110','111'])).

thf('176',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','112'])).

thf('178',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['164','176','177'])).

thf('179',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_relset_1 @ X38 @ X38 @ ( k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40 ) @ ( k6_partfun1 @ X38 ) )
      | ( ( k2_relset_1 @ X39 @ X38 @ X40 )
        = X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_B @ X0 )
        = sk_B )
      | ~ ( r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_B @ X0 )
        = sk_B )
      | ~ ( r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k6_partfun1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,
    ( ~ ( r2_relset_1 @ sk_B @ sk_B @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ ( k2_funct_1 @ sk_D ) )
      = sk_B )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_D ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['178','184'])).

thf('186',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('189',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('192',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('194',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('197',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('198',plain,(
    ! [X56: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('199',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('201',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != X22 )
      | ( v2_funct_2 @ X23 @ X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('202',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
      | ( v2_funct_2 @ X23 @ ( k2_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['200','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['197','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['196','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['195','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['194','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['193','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['192','212'])).

thf('214',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('217',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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

thf('219',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('220',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('221',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('223',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X2 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['218','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['217','228'])).

thf('230',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('231',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['229','230','231','232'])).

thf('234',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['216','233'])).

thf('235',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('236',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['234','235','236','237'])).

thf('239',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['126','127'])).

thf('242',plain,(
    v2_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['213','214','215','239','240','241'])).

thf('243',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_2 @ X23 @ X22 )
      | ( ( k2_relat_1 @ X23 )
        = X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('244',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('247',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('250',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('251',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['249','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['248','254'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['255'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['247','256'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['246','257'])).

thf('259',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['258'])).

thf('260',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['245','259'])).

thf('261',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('262',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['238'])).

thf('264',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['126','127'])).

thf('266',plain,(
    v5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['260','261','262','263','264','265'])).

thf('267',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['244','266'])).

thf('268',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['191','267'])).

thf('269',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('270',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['268','269'])).

thf('271',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['190','270'])).

thf('272',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('273',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['271','272','273'])).

thf('275',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['189','274'])).

thf('276',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('277',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['238'])).

thf('278',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['275','276','277'])).

thf('279',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['188','278'])).

thf('280',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('281',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['279','280','281'])).

thf('283',plain,(
    ! [X56: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('284',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['282','283'])).

thf('285',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('286',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['255'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('288',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('289',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['197','204'])).

thf('290',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('294',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['290','291','292','293'])).

thf('295',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['287','294'])).

thf('296',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('297',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['295','296','297'])).

thf('299',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_2 @ X23 @ X22 )
      | ( ( k2_relat_1 @ X23 )
        = X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('300',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['298','299'])).

thf('301',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['286','300'])).

thf('302',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('303',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['301','302','303','304'])).

thf('306',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['285','305'])).

thf('307',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('308',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['306','307','308'])).

thf('310',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('311',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['284','309','310'])).

thf('312',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['187','311'])).

thf('313',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('314',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['312','313','314'])).

thf('316',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('317',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ ( k1_relat_1 @ sk_C ) @ X2 @ X0 @ ( k2_funct_1 @ sk_C ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['315','316'])).

thf('318',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('319',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ ( k1_relat_1 @ sk_C ) @ X2 @ X0 @ ( k2_funct_1 @ sk_C ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['317','318'])).

thf('320',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','86'])).

thf('321',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('322',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
      = sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['320','321'])).

thf('323',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('324',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('325',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['323','324'])).

thf('326',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['306','307','308'])).

thf('327',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['325','326'])).

thf('328',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('329',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X52 @ X51 @ X50 )
       != X51 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X50 ) @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('331',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['329','330'])).

thf('332',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['331','332','333','334','335'])).

thf('337',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['336'])).

thf('338',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('339',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = sk_A ) ),
    inference(demod,[status(thm)],['322','327','328','337','338'])).

thf('340',plain,(
    m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','71','87'])).

thf('341',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('342',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['341'])).

thf('343',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) ),
    inference('sup-',[status(thm)],['340','342'])).

thf('344',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['339','343'])).

thf('345',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ ( k2_funct_1 @ sk_C ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['319','344'])).

thf('346',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['186','345'])).

thf('347',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('348',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('350',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('351',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['349','350'])).

thf('352',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('353',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['351','352'])).

thf('354',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['348','353'])).

thf('355',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('356',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('357',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X7 @ X8 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('358',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['356','357'])).

thf('359',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['306','307','308'])).

thf('360',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['312','313','314'])).

thf('361',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('362',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['360','361'])).

thf('363',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('364',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['238'])).

thf('365',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['126','127'])).

thf('366',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['279','280','281'])).

thf('367',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('368',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('369',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['358','359','362','363','364','365','366','367','368'])).

thf('370',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['369'])).

thf('371',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('372',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('373',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['371','372'])).

thf('374',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('375',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['373','374'])).

thf('376',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('377',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('378',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('379',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['375','376','377','378'])).

thf('380',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['370','379'])).

thf('381',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['380'])).

thf('382',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['371','372'])).

thf('383',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['381','382'])).

thf('384',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['279','280','281'])).

thf('385',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['360','361'])).

thf('386',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('387',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['238'])).

thf('388',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['383','384','385','386','387'])).

thf('389',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['354','355','388'])).

thf('390',plain,(
    m1_subset_1 @ ( k6_partfun1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['346','347','389'])).

thf('391',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['341'])).

thf('392',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ sk_B ) ),
    inference('sup-',[status(thm)],['390','391'])).

thf('393',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('394',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('395',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ ( k2_funct_1 @ sk_D ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['393','394'])).

thf('396',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('397',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('398',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X52 @ X51 @ X50 )
       != X51 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X50 ) @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('399',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_D ) @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['397','398'])).

thf('400',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('401',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('402',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('403',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_D ) @ sk_A @ sk_B )
    | ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['399','400','401','402'])).

thf('404',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('405',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_D ) @ sk_A @ sk_B )
    | ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['403','404'])).

thf('406',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_D ) @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['405'])).

thf('407',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['110','111'])).

thf('408',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_D ) @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['406','407'])).

thf('409',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('410',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
    = sk_B ),
    inference(demod,[status(thm)],['185','392','395','396','408','409'])).

thf('411',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['146','410'])).

thf('412',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['120','121'])).

thf('413',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('414',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['110','111'])).

thf('415',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['411','412','413','414'])).

thf('416',plain,
    ( ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['145','415'])).

thf('417',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['416'])).

thf('418',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['113','417'])).

thf('419',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('420',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['126','127'])).

thf('421',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X7 @ X8 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('422',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_C )
       != ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['420','421'])).

thf('423',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['130','131'])).

thf('424',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('425',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('426',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_C )
       != ( k6_partfun1 @ sk_B ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['422','423','424','425'])).

thf('427',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['419','426'])).

thf('428',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['120','121'])).

thf('429',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('430',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['427','428','429'])).

thf('431',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('432',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['430','431'])).

thf('433',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['339','343'])).

thf('434',plain,
    ( ( sk_A != sk_A )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['432','433'])).

thf('435',plain,(
    ( k5_relat_1 @ sk_D @ sk_C )
 != ( k6_partfun1 @ sk_B ) ),
    inference(simplify,[status(thm)],['434'])).

thf('436',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['418','435'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W52jKOT9cf
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:21:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.79/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/1.01  % Solved by: fo/fo7.sh
% 0.79/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/1.01  % done 1152 iterations in 0.546s
% 0.79/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/1.01  % SZS output start Refutation
% 0.79/1.01  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.79/1.01  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.79/1.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.79/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.79/1.01  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.79/1.01  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.79/1.01  thf(sk_D_type, type, sk_D: $i).
% 0.79/1.01  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.79/1.01  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.79/1.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.79/1.01  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.79/1.01  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.79/1.01  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.79/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.79/1.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.79/1.01  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.79/1.01  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.79/1.01  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.79/1.01  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.79/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.79/1.01  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.79/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/1.01  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.79/1.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.79/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.79/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.79/1.01  thf(t36_funct_2, conjecture,
% 0.79/1.01    (![A:$i,B:$i,C:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.01       ( ![D:$i]:
% 0.79/1.01         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.79/1.01             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.79/1.01           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.79/1.01               ( r2_relset_1 @
% 0.79/1.01                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.79/1.01                 ( k6_partfun1 @ A ) ) & 
% 0.79/1.01               ( v2_funct_1 @ C ) ) =>
% 0.79/1.01             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.79/1.01               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.79/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.79/1.01    (~( ![A:$i,B:$i,C:$i]:
% 0.79/1.01        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/1.01            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.01          ( ![D:$i]:
% 0.79/1.01            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.79/1.01                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.79/1.01              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.79/1.01                  ( r2_relset_1 @
% 0.79/1.01                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.79/1.01                    ( k6_partfun1 @ A ) ) & 
% 0.79/1.01                  ( v2_funct_1 @ C ) ) =>
% 0.79/1.01                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.79/1.01                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.79/1.01    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.79/1.01  thf('0', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(t35_funct_2, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.01       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.79/1.01         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.79/1.01           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.79/1.01             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.79/1.01  thf('1', plain,
% 0.79/1.01      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.79/1.01         (((X53) = (k1_xboole_0))
% 0.79/1.01          | ~ (v1_funct_1 @ X54)
% 0.79/1.01          | ~ (v1_funct_2 @ X54 @ X55 @ X53)
% 0.79/1.01          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X53)))
% 0.79/1.01          | ((k5_relat_1 @ X54 @ (k2_funct_1 @ X54)) = (k6_partfun1 @ X55))
% 0.79/1.01          | ~ (v2_funct_1 @ X54)
% 0.79/1.01          | ((k2_relset_1 @ X55 @ X53 @ X54) != (X53)))),
% 0.79/1.01      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.79/1.01  thf('2', plain,
% 0.79/1.01      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D)
% 0.79/1.01        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.79/1.01        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_D)
% 0.79/1.01        | ((sk_A) = (k1_xboole_0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['0', '1'])).
% 0.79/1.01  thf('3', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(redefinition_k2_relset_1, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i]:
% 0.79/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/1.01       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.79/1.01  thf('4', plain,
% 0.79/1.01      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.79/1.01         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.79/1.01          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.79/1.01  thf('5', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['3', '4'])).
% 0.79/1.01  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('8', plain,
% 0.79/1.01      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D)
% 0.79/1.01        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.79/1.01        | ((sk_A) = (k1_xboole_0)))),
% 0.79/1.01      inference('demod', [status(thm)], ['2', '5', '6', '7'])).
% 0.79/1.01  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('10', plain,
% 0.79/1.01      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D)
% 0.79/1.01        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.79/1.01      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.79/1.01  thf('11', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('12', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(redefinition_k1_partfun1, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ E ) & 
% 0.79/1.01         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/1.01         ( v1_funct_1 @ F ) & 
% 0.79/1.01         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.79/1.01       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.79/1.01  thf('13', plain,
% 0.79/1.01      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.79/1.01          | ~ (v1_funct_1 @ X30)
% 0.79/1.01          | ~ (v1_funct_1 @ X33)
% 0.79/1.01          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.79/1.01          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 0.79/1.01              = (k5_relat_1 @ X30 @ X33)))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.79/1.01  thf('14', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.79/1.01            = (k5_relat_1 @ sk_C @ X0))
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['12', '13'])).
% 0.79/1.01  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('16', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.79/1.01            = (k5_relat_1 @ sk_C @ X0))
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.79/1.01          | ~ (v1_funct_1 @ X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['14', '15'])).
% 0.79/1.01  thf('17', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ sk_D)
% 0.79/1.01        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/1.01            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['11', '16'])).
% 0.79/1.01  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('19', plain,
% 0.79/1.01      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/1.01         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/1.01  thf('20', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(t24_funct_2, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.01       ( ![D:$i]:
% 0.79/1.01         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.79/1.01             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.79/1.01           ( ( r2_relset_1 @
% 0.79/1.01               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.79/1.01               ( k6_partfun1 @ B ) ) =>
% 0.79/1.01             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.79/1.01  thf('21', plain,
% 0.79/1.01      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X37)
% 0.79/1.01          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.79/1.01          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.79/1.01          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 0.79/1.01               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 0.79/1.01               (k6_partfun1 @ X38))
% 0.79/1.01          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 0.79/1.01          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.79/1.01          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 0.79/1.01          | ~ (v1_funct_1 @ X40))),
% 0.79/1.01      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.79/1.01  thf('22', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/1.01          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.79/1.01          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.79/1.01               (k6_partfun1 @ sk_A))
% 0.79/1.01          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.79/1.01          | ~ (v1_funct_1 @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['20', '21'])).
% 0.79/1.01  thf('23', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('25', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/1.01          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.79/1.01          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.79/1.01               (k6_partfun1 @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.79/1.01  thf('26', plain,
% 0.79/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.79/1.01           (k6_partfun1 @ sk_A))
% 0.79/1.01        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.79/1.01        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/1.01        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['19', '25'])).
% 0.79/1.01  thf('27', plain,
% 0.79/1.01      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.79/1.01        (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('28', plain,
% 0.79/1.01      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/1.01         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/1.01  thf('29', plain,
% 0.79/1.01      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.79/1.01        (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['27', '28'])).
% 0.79/1.01  thf('30', plain,
% 0.79/1.01      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['3', '4'])).
% 0.79/1.01  thf('31', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('32', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('34', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 0.79/1.01  thf('35', plain,
% 0.79/1.01      ((((sk_A) != (sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D)
% 0.79/1.01        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['10', '34'])).
% 0.79/1.01  thf('36', plain,
% 0.79/1.01      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D))),
% 0.79/1.01      inference('simplify', [status(thm)], ['35'])).
% 0.79/1.01  thf('37', plain,
% 0.79/1.01      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/1.01         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/1.01  thf('38', plain,
% 0.79/1.01      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.79/1.01        (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['27', '28'])).
% 0.79/1.01  thf('39', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('40', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(dt_k1_partfun1, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ E ) & 
% 0.79/1.01         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/1.01         ( v1_funct_1 @ F ) & 
% 0.79/1.01         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.79/1.01       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.79/1.01         ( m1_subset_1 @
% 0.79/1.01           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.79/1.01           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.79/1.01  thf('41', plain,
% 0.79/1.01      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.79/1.01          | ~ (v1_funct_1 @ X24)
% 0.79/1.01          | ~ (v1_funct_1 @ X27)
% 0.79/1.01          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.79/1.01          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 0.79/1.01             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.79/1.01  thf('42', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.79/1.01          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.79/1.01          | ~ (v1_funct_1 @ X1)
% 0.79/1.01          | ~ (v1_funct_1 @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['40', '41'])).
% 0.79/1.01  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('44', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.79/1.01          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.79/1.01          | ~ (v1_funct_1 @ X1))),
% 0.79/1.01      inference('demod', [status(thm)], ['42', '43'])).
% 0.79/1.01  thf('45', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ sk_D)
% 0.79/1.01        | (m1_subset_1 @ 
% 0.79/1.01           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['39', '44'])).
% 0.79/1.01  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('47', plain,
% 0.79/1.01      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/1.01         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/1.01  thf('48', plain,
% 0.79/1.01      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.79/1.01  thf(redefinition_r2_relset_1, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/1.01     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/1.01         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.01       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.79/1.01  thf('49', plain,
% 0.79/1.01      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.79/1.01          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.79/1.01          | ((X18) = (X21))
% 0.79/1.01          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.79/1.01  thf('50', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.79/1.01          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['48', '49'])).
% 0.79/1.01  thf('51', plain,
% 0.79/1.01      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.79/1.01        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['38', '50'])).
% 0.79/1.01  thf('52', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(t31_funct_2, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.01       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.79/1.01         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.79/1.01           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.79/1.01           ( m1_subset_1 @
% 0.79/1.01             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.79/1.01  thf('53', plain,
% 0.79/1.01      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X50)
% 0.79/1.01          | ((k2_relset_1 @ X52 @ X51 @ X50) != (X51))
% 0.79/1.01          | (m1_subset_1 @ (k2_funct_1 @ X50) @ 
% 0.79/1.01             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 0.79/1.01          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 0.79/1.01          | ~ (v1_funct_2 @ X50 @ X52 @ X51)
% 0.79/1.01          | ~ (v1_funct_1 @ X50))),
% 0.79/1.01      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.79/1.01  thf('54', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.79/1.01        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/1.01        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['52', '53'])).
% 0.79/1.01  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('56', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('57', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('59', plain,
% 0.79/1.01      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/1.01         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/1.01        | ((sk_B) != (sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.79/1.01  thf('60', plain,
% 0.79/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('simplify', [status(thm)], ['59'])).
% 0.79/1.01  thf('61', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.79/1.01          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.79/1.01          | ~ (v1_funct_1 @ X1))),
% 0.79/1.01      inference('demod', [status(thm)], ['42', '43'])).
% 0.79/1.01  thf('62', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.79/1.01        | (m1_subset_1 @ 
% 0.79/1.01           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 0.79/1.01            (k2_funct_1 @ sk_C)) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['60', '61'])).
% 0.79/1.01  thf('63', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('64', plain,
% 0.79/1.01      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X50)
% 0.79/1.01          | ((k2_relset_1 @ X52 @ X51 @ X50) != (X51))
% 0.79/1.01          | (v1_funct_1 @ (k2_funct_1 @ X50))
% 0.79/1.01          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 0.79/1.01          | ~ (v1_funct_2 @ X50 @ X52 @ X51)
% 0.79/1.01          | ~ (v1_funct_1 @ X50))),
% 0.79/1.01      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.79/1.01  thf('65', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.79/1.01        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.79/1.01        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['63', '64'])).
% 0.79/1.01  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('67', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('68', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('69', plain, ((v2_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('70', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.79/1.01  thf('71', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['70'])).
% 0.79/1.01  thf('72', plain,
% 0.79/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('simplify', [status(thm)], ['59'])).
% 0.79/1.01  thf('73', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.79/1.01            = (k5_relat_1 @ sk_C @ X0))
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.79/1.01          | ~ (v1_funct_1 @ X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['14', '15'])).
% 0.79/1.01  thf('74', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.79/1.01        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 0.79/1.01            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['72', '73'])).
% 0.79/1.01  thf('75', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['70'])).
% 0.79/1.01  thf('76', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('77', plain,
% 0.79/1.01      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.79/1.01         (((X53) = (k1_xboole_0))
% 0.79/1.01          | ~ (v1_funct_1 @ X54)
% 0.79/1.01          | ~ (v1_funct_2 @ X54 @ X55 @ X53)
% 0.79/1.01          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X53)))
% 0.79/1.01          | ((k5_relat_1 @ X54 @ (k2_funct_1 @ X54)) = (k6_partfun1 @ X55))
% 0.79/1.01          | ~ (v2_funct_1 @ X54)
% 0.79/1.01          | ((k2_relset_1 @ X55 @ X53 @ X54) != (X53)))),
% 0.79/1.01      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.79/1.01  thf('78', plain,
% 0.79/1.01      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.79/1.01        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.79/1.01        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ((sk_B) = (k1_xboole_0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['76', '77'])).
% 0.79/1.01  thf('79', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('80', plain, ((v2_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('81', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('83', plain,
% 0.79/1.01      ((((sk_B) != (sk_B))
% 0.79/1.01        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.79/1.01        | ((sk_B) = (k1_xboole_0)))),
% 0.79/1.01      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 0.79/1.01  thf('84', plain,
% 0.79/1.01      ((((sk_B) = (k1_xboole_0))
% 0.79/1.01        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.79/1.01      inference('simplify', [status(thm)], ['83'])).
% 0.79/1.01  thf('85', plain, (((sk_B) != (k1_xboole_0))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('86', plain,
% 0.79/1.01      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.79/1.01  thf('87', plain,
% 0.79/1.01      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 0.79/1.01         = (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['74', '75', '86'])).
% 0.79/1.01  thf('88', plain,
% 0.79/1.01      ((m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['62', '71', '87'])).
% 0.79/1.01  thf('89', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['51', '88'])).
% 0.79/1.01  thf('90', plain,
% 0.79/1.01      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/1.01         = (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['37', '89'])).
% 0.79/1.01  thf('91', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(t30_funct_2, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/1.01     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/1.01         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.79/1.01       ( ![E:$i]:
% 0.79/1.01         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.79/1.01             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.79/1.01           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.79/1.01               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.79/1.01             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.79/1.01               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.79/1.01  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.79/1.01  thf(zf_stmt_2, axiom,
% 0.79/1.01    (![C:$i,B:$i]:
% 0.79/1.01     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.79/1.01       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.79/1.01  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.79/1.01  thf(zf_stmt_4, axiom,
% 0.79/1.01    (![E:$i,D:$i]:
% 0.79/1.01     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.79/1.01  thf(zf_stmt_5, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.79/1.01         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.01       ( ![E:$i]:
% 0.79/1.01         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.79/1.01             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.79/1.01           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.79/1.01               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.79/1.01             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.79/1.01  thf('92', plain,
% 0.79/1.01      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X45)
% 0.79/1.01          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 0.79/1.01          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 0.79/1.01          | (zip_tseitin_0 @ X45 @ X48)
% 0.79/1.01          | ~ (v2_funct_1 @ (k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45))
% 0.79/1.01          | (zip_tseitin_1 @ X47 @ X46)
% 0.79/1.01          | ((k2_relset_1 @ X49 @ X46 @ X48) != (X46))
% 0.79/1.01          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X46)))
% 0.79/1.01          | ~ (v1_funct_2 @ X48 @ X49 @ X46)
% 0.79/1.01          | ~ (v1_funct_1 @ X48))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.79/1.01  thf('93', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.79/1.01          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.79/1.01          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.79/1.01          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.79/1.01          | (zip_tseitin_0 @ sk_D @ X0)
% 0.79/1.01          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.79/1.01          | ~ (v1_funct_1 @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['91', '92'])).
% 0.79/1.01  thf('94', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('95', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('96', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.79/1.01          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.79/1.01          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.79/1.01          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.79/1.01          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.79/1.01  thf('97', plain,
% 0.79/1.01      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.79/1.01        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.79/1.01        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.79/1.01        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.79/1.01        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.79/1.01        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['90', '96'])).
% 0.79/1.01  thf(fc4_funct_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.79/1.01       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.79/1.01  thf('98', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 0.79/1.01      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.79/1.01  thf(redefinition_k6_partfun1, axiom,
% 0.79/1.01    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.79/1.01  thf('99', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/1.01  thf('100', plain, (![X2 : $i]: (v2_funct_1 @ (k6_partfun1 @ X2))),
% 0.79/1.01      inference('demod', [status(thm)], ['98', '99'])).
% 0.79/1.01  thf('101', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('102', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('103', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('105', plain,
% 0.79/1.01      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.79/1.01        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.79/1.01        | ((sk_B) != (sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)],
% 0.79/1.01                ['97', '100', '101', '102', '103', '104'])).
% 0.79/1.01  thf('106', plain,
% 0.79/1.01      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['105'])).
% 0.79/1.01  thf('107', plain,
% 0.79/1.01      (![X43 : $i, X44 : $i]:
% 0.79/1.01         (((X43) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X43 @ X44))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.79/1.01  thf('108', plain,
% 0.79/1.01      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['106', '107'])).
% 0.79/1.01  thf('109', plain, (((sk_A) != (k1_xboole_0))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('110', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.79/1.01      inference('simplify_reflect-', [status(thm)], ['108', '109'])).
% 0.79/1.01  thf('111', plain,
% 0.79/1.01      (![X41 : $i, X42 : $i]:
% 0.79/1.01         ((v2_funct_1 @ X42) | ~ (zip_tseitin_0 @ X42 @ X41))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.79/1.01  thf('112', plain, ((v2_funct_1 @ sk_D)),
% 0.79/1.01      inference('sup-', [status(thm)], ['110', '111'])).
% 0.79/1.01  thf('113', plain,
% 0.79/1.01      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['36', '112'])).
% 0.79/1.01  thf('114', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['51', '88'])).
% 0.79/1.01  thf(t64_funct_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.01       ( ![B:$i]:
% 0.79/1.01         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.79/1.01           ( ( ( v2_funct_1 @ A ) & 
% 0.79/1.01               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.79/1.01               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.79/1.01             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.79/1.01  thf('115', plain,
% 0.79/1.01      (![X7 : $i, X8 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X7)
% 0.79/1.01          | ~ (v1_funct_1 @ X7)
% 0.79/1.01          | ((X7) = (k2_funct_1 @ X8))
% 0.79/1.01          | ((k5_relat_1 @ X7 @ X8) != (k6_relat_1 @ (k2_relat_1 @ X8)))
% 0.79/1.01          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.79/1.01          | ~ (v2_funct_1 @ X8)
% 0.79/1.01          | ~ (v1_funct_1 @ X8)
% 0.79/1.01          | ~ (v1_relat_1 @ X8))),
% 0.79/1.01      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.79/1.01  thf('116', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/1.01  thf('117', plain,
% 0.79/1.01      (![X7 : $i, X8 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X7)
% 0.79/1.01          | ~ (v1_funct_1 @ X7)
% 0.79/1.01          | ((X7) = (k2_funct_1 @ X8))
% 0.79/1.01          | ((k5_relat_1 @ X7 @ X8) != (k6_partfun1 @ (k2_relat_1 @ X8)))
% 0.79/1.01          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.79/1.01          | ~ (v2_funct_1 @ X8)
% 0.79/1.01          | ~ (v1_funct_1 @ X8)
% 0.79/1.01          | ~ (v1_relat_1 @ X8))),
% 0.79/1.01      inference('demod', [status(thm)], ['115', '116'])).
% 0.79/1.01  thf('118', plain,
% 0.79/1.01      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_D)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_D)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D)
% 0.79/1.01        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.79/1.01        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ~ (v1_relat_1 @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['114', '117'])).
% 0.79/1.01  thf('119', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 0.79/1.01  thf('120', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(cc1_relset_1, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i]:
% 0.79/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/1.01       ( v1_relat_1 @ C ) ))).
% 0.79/1.01  thf('121', plain,
% 0.79/1.01      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.79/1.01         ((v1_relat_1 @ X9)
% 0.79/1.01          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.79/1.01  thf('122', plain, ((v1_relat_1 @ sk_D)),
% 0.79/1.01      inference('sup-', [status(thm)], ['120', '121'])).
% 0.79/1.01  thf('123', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('124', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('125', plain,
% 0.79/1.01      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.79/1.01         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.79/1.01          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.79/1.01  thf('126', plain,
% 0.79/1.01      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['124', '125'])).
% 0.79/1.01  thf('127', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('128', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.79/1.01      inference('sup+', [status(thm)], ['126', '127'])).
% 0.79/1.01  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('130', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('131', plain,
% 0.79/1.01      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.79/1.01         ((v1_relat_1 @ X9)
% 0.79/1.01          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.79/1.01  thf('132', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.79/1.01  thf('133', plain,
% 0.79/1.01      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D)
% 0.79/1.01        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.79/1.01        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.79/1.01      inference('demod', [status(thm)],
% 0.79/1.01                ['118', '119', '122', '123', '128', '129', '132'])).
% 0.79/1.01  thf('134', plain,
% 0.79/1.01      ((((sk_C) = (k2_funct_1 @ sk_D))
% 0.79/1.01        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D))),
% 0.79/1.01      inference('simplify', [status(thm)], ['133'])).
% 0.79/1.01  thf('135', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['51', '88'])).
% 0.79/1.01  thf(t48_funct_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.01       ( ![B:$i]:
% 0.79/1.01         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.79/1.01           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.79/1.01               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.79/1.01             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.79/1.01  thf('136', plain,
% 0.79/1.01      (![X3 : $i, X4 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X3)
% 0.79/1.01          | ~ (v1_funct_1 @ X3)
% 0.79/1.01          | (v2_funct_1 @ X4)
% 0.79/1.01          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 0.79/1.01          | ~ (v2_funct_1 @ (k5_relat_1 @ X3 @ X4))
% 0.79/1.01          | ~ (v1_funct_1 @ X4)
% 0.79/1.01          | ~ (v1_relat_1 @ X4))),
% 0.79/1.01      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.79/1.01  thf('137', plain,
% 0.79/1.01      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_D)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_D)
% 0.79/1.01        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.79/1.01        | (v2_funct_1 @ sk_D)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ~ (v1_relat_1 @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['135', '136'])).
% 0.79/1.01  thf('138', plain, (![X2 : $i]: (v2_funct_1 @ (k6_partfun1 @ X2))),
% 0.79/1.01      inference('demod', [status(thm)], ['98', '99'])).
% 0.79/1.01  thf('139', plain, ((v1_relat_1 @ sk_D)),
% 0.79/1.01      inference('sup-', [status(thm)], ['120', '121'])).
% 0.79/1.01  thf('140', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('141', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.79/1.01      inference('sup+', [status(thm)], ['126', '127'])).
% 0.79/1.01  thf('142', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('143', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.79/1.01  thf('144', plain, ((((sk_B) != (k1_relat_1 @ sk_D)) | (v2_funct_1 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)],
% 0.79/1.01                ['137', '138', '139', '140', '141', '142', '143'])).
% 0.79/1.01  thf('145', plain,
% 0.79/1.01      ((((sk_B) != (k1_relat_1 @ sk_D)) | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.79/1.01      inference('clc', [status(thm)], ['134', '144'])).
% 0.79/1.01  thf(t55_funct_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.01       ( ( v2_funct_1 @ A ) =>
% 0.79/1.01         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.79/1.01           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.79/1.01  thf('146', plain,
% 0.79/1.01      (![X5 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X5)
% 0.79/1.01          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.79/1.01          | ~ (v1_funct_1 @ X5)
% 0.79/1.01          | ~ (v1_relat_1 @ X5))),
% 0.79/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.79/1.01  thf('147', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('148', plain,
% 0.79/1.01      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X50)
% 0.79/1.01          | ((k2_relset_1 @ X52 @ X51 @ X50) != (X51))
% 0.79/1.01          | (m1_subset_1 @ (k2_funct_1 @ X50) @ 
% 0.79/1.01             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 0.79/1.01          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 0.79/1.01          | ~ (v1_funct_2 @ X50 @ X52 @ X51)
% 0.79/1.01          | ~ (v1_funct_1 @ X50))),
% 0.79/1.01      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.79/1.01  thf('149', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ sk_D)
% 0.79/1.01        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.79/1.01        | (m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.79/1.01        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['147', '148'])).
% 0.79/1.01  thf('150', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('151', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('152', plain,
% 0.79/1.01      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['3', '4'])).
% 0.79/1.01  thf('153', plain,
% 0.79/1.01      (((m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 0.79/1.01         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.79/1.01        | ((k2_relat_1 @ sk_D) != (sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['149', '150', '151', '152'])).
% 0.79/1.01  thf('154', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 0.79/1.01  thf('155', plain,
% 0.79/1.01      (((m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 0.79/1.01         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.79/1.01        | ((sk_A) != (sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['153', '154'])).
% 0.79/1.01  thf('156', plain,
% 0.79/1.01      ((~ (v2_funct_1 @ sk_D)
% 0.79/1.01        | (m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.79/1.01      inference('simplify', [status(thm)], ['155'])).
% 0.79/1.01  thf('157', plain, ((v2_funct_1 @ sk_D)),
% 0.79/1.01      inference('sup-', [status(thm)], ['110', '111'])).
% 0.79/1.01  thf('158', plain,
% 0.79/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['156', '157'])).
% 0.79/1.01  thf('159', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('160', plain,
% 0.79/1.01      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.79/1.01          | ~ (v1_funct_1 @ X30)
% 0.79/1.01          | ~ (v1_funct_1 @ X33)
% 0.79/1.01          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.79/1.01          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 0.79/1.01              = (k5_relat_1 @ X30 @ X33)))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.79/1.01  thf('161', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.79/1.01            = (k5_relat_1 @ sk_D @ X0))
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['159', '160'])).
% 0.79/1.01  thf('162', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('163', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.79/1.01            = (k5_relat_1 @ sk_D @ X0))
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.79/1.01          | ~ (v1_funct_1 @ X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['161', '162'])).
% 0.79/1.01  thf('164', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.79/1.01        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ 
% 0.79/1.01            (k2_funct_1 @ sk_D)) = (k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['158', '163'])).
% 0.79/1.01  thf('165', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('166', plain,
% 0.79/1.01      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X50)
% 0.79/1.01          | ((k2_relset_1 @ X52 @ X51 @ X50) != (X51))
% 0.79/1.01          | (v1_funct_1 @ (k2_funct_1 @ X50))
% 0.79/1.01          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 0.79/1.01          | ~ (v1_funct_2 @ X50 @ X52 @ X51)
% 0.79/1.01          | ~ (v1_funct_1 @ X50))),
% 0.79/1.01      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.79/1.01  thf('167', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ sk_D)
% 0.79/1.01        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.79/1.01        | (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.79/1.01        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['165', '166'])).
% 0.79/1.01  thf('168', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('169', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('170', plain,
% 0.79/1.01      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['3', '4'])).
% 0.79/1.01  thf('171', plain,
% 0.79/1.01      (((v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.79/1.01        | ((k2_relat_1 @ sk_D) != (sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['167', '168', '169', '170'])).
% 0.79/1.01  thf('172', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 0.79/1.01  thf('173', plain,
% 0.79/1.01      (((v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.79/1.01        | ((sk_A) != (sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['171', '172'])).
% 0.79/1.01  thf('174', plain,
% 0.79/1.01      ((~ (v2_funct_1 @ sk_D) | (v1_funct_1 @ (k2_funct_1 @ sk_D)))),
% 0.79/1.01      inference('simplify', [status(thm)], ['173'])).
% 0.79/1.01  thf('175', plain, ((v2_funct_1 @ sk_D)),
% 0.79/1.01      inference('sup-', [status(thm)], ['110', '111'])).
% 0.79/1.01  thf('176', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['174', '175'])).
% 0.79/1.01  thf('177', plain,
% 0.79/1.01      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['36', '112'])).
% 0.79/1.01  thf('178', plain,
% 0.79/1.01      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ (k2_funct_1 @ sk_D))
% 0.79/1.01         = (k6_partfun1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['164', '176', '177'])).
% 0.79/1.01  thf('179', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('180', plain,
% 0.79/1.01      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X37)
% 0.79/1.01          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.79/1.01          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.79/1.01          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 0.79/1.01               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 0.79/1.01               (k6_partfun1 @ X38))
% 0.79/1.01          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 0.79/1.01          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.79/1.01          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 0.79/1.01          | ~ (v1_funct_1 @ X40))),
% 0.79/1.01      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.79/1.01  thf('181', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.79/1.01          | ((k2_relset_1 @ sk_A @ sk_B @ X0) = (sk_B))
% 0.79/1.01          | ~ (r2_relset_1 @ sk_B @ sk_B @ 
% 0.79/1.01               (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ X0) @ 
% 0.79/1.01               (k6_partfun1 @ sk_B))
% 0.79/1.01          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.79/1.01          | ~ (v1_funct_1 @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['179', '180'])).
% 0.79/1.01  thf('182', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('183', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('184', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.79/1.01          | ((k2_relset_1 @ sk_A @ sk_B @ X0) = (sk_B))
% 0.79/1.01          | ~ (r2_relset_1 @ sk_B @ sk_B @ 
% 0.79/1.01               (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ X0) @ 
% 0.79/1.01               (k6_partfun1 @ sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['181', '182', '183'])).
% 0.79/1.01  thf('185', plain,
% 0.79/1.01      ((~ (r2_relset_1 @ sk_B @ sk_B @ (k6_partfun1 @ sk_B) @ 
% 0.79/1.01           (k6_partfun1 @ sk_B))
% 0.79/1.01        | ((k2_relset_1 @ sk_A @ sk_B @ (k2_funct_1 @ sk_D)) = (sk_B))
% 0.79/1.01        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 0.79/1.01             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.79/1.01        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_D) @ sk_A @ sk_B)
% 0.79/1.01        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['178', '184'])).
% 0.79/1.01  thf('186', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(dt_k2_funct_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.01       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.79/1.01         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.79/1.01  thf('187', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/1.01  thf('188', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/1.01  thf('189', plain,
% 0.79/1.01      (![X5 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X5)
% 0.79/1.01          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.79/1.01          | ~ (v1_funct_1 @ X5)
% 0.79/1.01          | ~ (v1_relat_1 @ X5))),
% 0.79/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.79/1.01  thf('190', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/1.01  thf('191', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/1.01  thf('192', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['70'])).
% 0.79/1.01  thf('193', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/1.01  thf('194', plain,
% 0.79/1.01      (![X5 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X5)
% 0.79/1.01          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.79/1.01          | ~ (v1_funct_1 @ X5)
% 0.79/1.01          | ~ (v1_relat_1 @ X5))),
% 0.79/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.79/1.01  thf('195', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/1.01  thf('196', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/1.01  thf('197', plain,
% 0.79/1.01      (![X5 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X5)
% 0.79/1.01          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.79/1.01          | ~ (v1_funct_1 @ X5)
% 0.79/1.01          | ~ (v1_relat_1 @ X5))),
% 0.79/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.79/1.01  thf(t3_funct_2, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.01       ( ( v1_funct_1 @ A ) & 
% 0.79/1.01         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.79/1.01         ( m1_subset_1 @
% 0.79/1.01           A @ 
% 0.79/1.01           ( k1_zfmisc_1 @
% 0.79/1.01             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.79/1.01  thf('198', plain,
% 0.79/1.01      (![X56 : $i]:
% 0.79/1.01         ((m1_subset_1 @ X56 @ 
% 0.79/1.01           (k1_zfmisc_1 @ 
% 0.79/1.01            (k2_zfmisc_1 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 0.79/1.01          | ~ (v1_funct_1 @ X56)
% 0.79/1.01          | ~ (v1_relat_1 @ X56))),
% 0.79/1.01      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.79/1.01  thf(cc2_relset_1, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i]:
% 0.79/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/1.01       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.79/1.01  thf('199', plain,
% 0.79/1.01      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.79/1.01         ((v5_relat_1 @ X12 @ X14)
% 0.79/1.01          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.79/1.01  thf('200', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['198', '199'])).
% 0.79/1.01  thf(d3_funct_2, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.79/1.01       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.79/1.01  thf('201', plain,
% 0.79/1.01      (![X22 : $i, X23 : $i]:
% 0.79/1.01         (((k2_relat_1 @ X23) != (X22))
% 0.79/1.01          | (v2_funct_2 @ X23 @ X22)
% 0.79/1.01          | ~ (v5_relat_1 @ X23 @ X22)
% 0.79/1.01          | ~ (v1_relat_1 @ X23))),
% 0.79/1.01      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.79/1.01  thf('202', plain,
% 0.79/1.01      (![X23 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X23)
% 0.79/1.01          | ~ (v5_relat_1 @ X23 @ (k2_relat_1 @ X23))
% 0.79/1.01          | (v2_funct_2 @ X23 @ (k2_relat_1 @ X23)))),
% 0.79/1.01      inference('simplify', [status(thm)], ['201'])).
% 0.79/1.01  thf('203', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['200', '202'])).
% 0.79/1.01  thf('204', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0))),
% 0.79/1.01      inference('simplify', [status(thm)], ['203'])).
% 0.79/1.01  thf('205', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v2_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['197', '204'])).
% 0.79/1.01  thf('206', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | (v2_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['196', '205'])).
% 0.79/1.01  thf('207', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v2_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('simplify', [status(thm)], ['206'])).
% 0.79/1.01  thf('208', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | (v2_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['195', '207'])).
% 0.79/1.01  thf('209', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v2_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('simplify', [status(thm)], ['208'])).
% 0.79/1.01  thf('210', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v2_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['194', '209'])).
% 0.79/1.01  thf('211', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | (v2_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['193', '210'])).
% 0.79/1.01  thf('212', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v2_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('simplify', [status(thm)], ['211'])).
% 0.79/1.01  thf('213', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.79/1.01        | (v2_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.79/1.01           (k2_relat_1 @ sk_C)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['192', '212'])).
% 0.79/1.01  thf('214', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.79/1.01  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('216', plain,
% 0.79/1.01      (![X5 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X5)
% 0.79/1.01          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.79/1.01          | ~ (v1_funct_1 @ X5)
% 0.79/1.01          | ~ (v1_relat_1 @ X5))),
% 0.79/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.79/1.01  thf('217', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['70'])).
% 0.79/1.01  thf('218', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/1.01  thf(t61_funct_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.01       ( ( v2_funct_1 @ A ) =>
% 0.79/1.01         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.79/1.01             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.79/1.01           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.79/1.01             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.79/1.01  thf('219', plain,
% 0.79/1.01      (![X6 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X6)
% 0.79/1.01          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 0.79/1.01              = (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.79/1.01          | ~ (v1_funct_1 @ X6)
% 0.79/1.01          | ~ (v1_relat_1 @ X6))),
% 0.79/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.79/1.01  thf('220', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/1.01  thf('221', plain,
% 0.79/1.01      (![X6 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X6)
% 0.79/1.01          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 0.79/1.01              = (k6_partfun1 @ (k2_relat_1 @ X6)))
% 0.79/1.01          | ~ (v1_funct_1 @ X6)
% 0.79/1.01          | ~ (v1_relat_1 @ X6))),
% 0.79/1.01      inference('demod', [status(thm)], ['219', '220'])).
% 0.79/1.01  thf('222', plain,
% 0.79/1.01      (![X3 : $i, X4 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X3)
% 0.79/1.01          | ~ (v1_funct_1 @ X3)
% 0.79/1.01          | (v2_funct_1 @ X3)
% 0.79/1.01          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 0.79/1.01          | ~ (v2_funct_1 @ (k5_relat_1 @ X3 @ X4))
% 0.79/1.01          | ~ (v1_funct_1 @ X4)
% 0.79/1.01          | ~ (v1_relat_1 @ X4))),
% 0.79/1.01      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.79/1.01  thf('223', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.79/1.01          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['221', '222'])).
% 0.79/1.01  thf('224', plain, (![X2 : $i]: (v2_funct_1 @ (k6_partfun1 @ X2))),
% 0.79/1.01      inference('demod', [status(thm)], ['98', '99'])).
% 0.79/1.01  thf('225', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.79/1.01          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.79/1.01      inference('demod', [status(thm)], ['223', '224'])).
% 0.79/1.01  thf('226', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('simplify', [status(thm)], ['225'])).
% 0.79/1.01  thf('227', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.79/1.01          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['218', '226'])).
% 0.79/1.01  thf('228', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('simplify', [status(thm)], ['227'])).
% 0.79/1.01  thf('229', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.79/1.01        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.79/1.01        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['217', '228'])).
% 0.79/1.01  thf('230', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.79/1.01  thf('231', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('232', plain, ((v2_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('233', plain,
% 0.79/1.01      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.79/1.01        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/1.01      inference('demod', [status(thm)], ['229', '230', '231', '232'])).
% 0.79/1.01  thf('234', plain,
% 0.79/1.01      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.79/1.01        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['216', '233'])).
% 0.79/1.01  thf('235', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.79/1.01  thf('236', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('237', plain, ((v2_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('238', plain,
% 0.79/1.01      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.79/1.01        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/1.01      inference('demod', [status(thm)], ['234', '235', '236', '237'])).
% 0.79/1.01  thf('239', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['238'])).
% 0.79/1.01  thf('240', plain, ((v2_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('241', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.79/1.01      inference('sup+', [status(thm)], ['126', '127'])).
% 0.79/1.01  thf('242', plain, ((v2_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)],
% 0.79/1.01                ['213', '214', '215', '239', '240', '241'])).
% 0.79/1.01  thf('243', plain,
% 0.79/1.01      (![X22 : $i, X23 : $i]:
% 0.79/1.01         (~ (v2_funct_2 @ X23 @ X22)
% 0.79/1.01          | ((k2_relat_1 @ X23) = (X22))
% 0.79/1.01          | ~ (v5_relat_1 @ X23 @ X22)
% 0.79/1.01          | ~ (v1_relat_1 @ X23))),
% 0.79/1.01      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.79/1.01  thf('244', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.79/1.01        | ~ (v5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_B)
% 0.79/1.01        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['242', '243'])).
% 0.79/1.01  thf('245', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['70'])).
% 0.79/1.01  thf('246', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/1.01  thf('247', plain,
% 0.79/1.01      (![X5 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X5)
% 0.79/1.01          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.79/1.01          | ~ (v1_funct_1 @ X5)
% 0.79/1.01          | ~ (v1_relat_1 @ X5))),
% 0.79/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.79/1.01  thf('248', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/1.01  thf('249', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/1.01  thf('250', plain,
% 0.79/1.01      (![X5 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X5)
% 0.79/1.01          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.79/1.01          | ~ (v1_funct_1 @ X5)
% 0.79/1.01          | ~ (v1_relat_1 @ X5))),
% 0.79/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.79/1.01  thf('251', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['198', '199'])).
% 0.79/1.01  thf('252', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['250', '251'])).
% 0.79/1.01  thf('253', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | (v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['249', '252'])).
% 0.79/1.01  thf('254', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('simplify', [status(thm)], ['253'])).
% 0.79/1.01  thf('255', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | (v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['248', '254'])).
% 0.79/1.01  thf('256', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('simplify', [status(thm)], ['255'])).
% 0.79/1.01  thf('257', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['247', '256'])).
% 0.79/1.01  thf('258', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | (v5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['246', '257'])).
% 0.79/1.01  thf('259', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('simplify', [status(thm)], ['258'])).
% 0.79/1.01  thf('260', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.79/1.01        | (v5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.79/1.01           (k2_relat_1 @ sk_C)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['245', '259'])).
% 0.79/1.01  thf('261', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.79/1.01  thf('262', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('263', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['238'])).
% 0.79/1.01  thf('264', plain, ((v2_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('265', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.79/1.01      inference('sup+', [status(thm)], ['126', '127'])).
% 0.79/1.01  thf('266', plain, ((v5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)],
% 0.79/1.01                ['260', '261', '262', '263', '264', '265'])).
% 0.79/1.01  thf('267', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.79/1.01        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['244', '266'])).
% 0.79/1.01  thf('268', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.79/1.01        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.79/1.01        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['191', '267'])).
% 0.79/1.01  thf('269', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['70'])).
% 0.79/1.01  thf('270', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.79/1.01        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['268', '269'])).
% 0.79/1.01  thf('271', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['190', '270'])).
% 0.79/1.01  thf('272', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.79/1.01  thf('273', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('274', plain,
% 0.79/1.01      (((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['271', '272', '273'])).
% 0.79/1.01  thf('275', plain,
% 0.79/1.01      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_B))
% 0.79/1.01        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.79/1.01        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.79/1.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['189', '274'])).
% 0.79/1.01  thf('276', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['70'])).
% 0.79/1.01  thf('277', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['238'])).
% 0.79/1.01  thf('278', plain,
% 0.79/1.01      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_B))
% 0.79/1.01        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/1.01      inference('demod', [status(thm)], ['275', '276', '277'])).
% 0.79/1.01  thf('279', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_B)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['188', '278'])).
% 0.79/1.01  thf('280', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.79/1.01  thf('281', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('282', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['279', '280', '281'])).
% 0.79/1.01  thf('283', plain,
% 0.79/1.01      (![X56 : $i]:
% 0.79/1.01         ((m1_subset_1 @ X56 @ 
% 0.79/1.01           (k1_zfmisc_1 @ 
% 0.79/1.01            (k2_zfmisc_1 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 0.79/1.01          | ~ (v1_funct_1 @ X56)
% 0.79/1.01          | ~ (v1_relat_1 @ X56))),
% 0.79/1.01      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.79/1.01  thf('284', plain,
% 0.79/1.01      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/1.01         (k1_zfmisc_1 @ 
% 0.79/1.01          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 0.79/1.01        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.79/1.01        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['282', '283'])).
% 0.79/1.01  thf('285', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/1.01  thf('286', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('simplify', [status(thm)], ['255'])).
% 0.79/1.01  thf('287', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/1.01  thf('288', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['70'])).
% 0.79/1.01  thf('289', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v2_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['197', '204'])).
% 0.79/1.01  thf('290', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ~ (v1_relat_1 @ sk_C)
% 0.79/1.01        | (v2_funct_2 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['288', '289'])).
% 0.79/1.01  thf('291', plain, ((v2_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('292', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('293', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.79/1.01  thf('294', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.79/1.01        | (v2_funct_2 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C)))),
% 0.79/1.01      inference('demod', [status(thm)], ['290', '291', '292', '293'])).
% 0.79/1.01  thf('295', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | (v2_funct_2 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['287', '294'])).
% 0.79/1.01  thf('296', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.79/1.01  thf('297', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('298', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C))),
% 0.79/1.01      inference('demod', [status(thm)], ['295', '296', '297'])).
% 0.79/1.01  thf('299', plain,
% 0.79/1.01      (![X22 : $i, X23 : $i]:
% 0.79/1.01         (~ (v2_funct_2 @ X23 @ X22)
% 0.79/1.01          | ((k2_relat_1 @ X23) = (X22))
% 0.79/1.01          | ~ (v5_relat_1 @ X23 @ X22)
% 0.79/1.01          | ~ (v1_relat_1 @ X23))),
% 0.79/1.01      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.79/1.01  thf('300', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.79/1.01        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 0.79/1.01        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['298', '299'])).
% 0.79/1.01  thf('301', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.79/1.01        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.79/1.01        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['286', '300'])).
% 0.79/1.01  thf('302', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.79/1.01  thf('303', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('304', plain, ((v2_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('305', plain,
% 0.79/1.01      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.79/1.01        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/1.01      inference('demod', [status(thm)], ['301', '302', '303', '304'])).
% 0.79/1.01  thf('306', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['285', '305'])).
% 0.79/1.01  thf('307', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.79/1.01  thf('308', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('309', plain,
% 0.79/1.01      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.79/1.01      inference('demod', [status(thm)], ['306', '307', '308'])).
% 0.79/1.01  thf('310', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['70'])).
% 0.79/1.01  thf('311', plain,
% 0.79/1.01      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/1.01         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 0.79/1.01        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/1.01      inference('demod', [status(thm)], ['284', '309', '310'])).
% 0.79/1.01  thf('312', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C)))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['187', '311'])).
% 0.79/1.01  thf('313', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.79/1.01  thf('314', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('315', plain,
% 0.79/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))),
% 0.79/1.01      inference('demod', [status(thm)], ['312', '313', '314'])).
% 0.79/1.01  thf('316', plain,
% 0.79/1.01      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.79/1.01          | ~ (v1_funct_1 @ X24)
% 0.79/1.01          | ~ (v1_funct_1 @ X27)
% 0.79/1.01          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.79/1.01          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 0.79/1.01             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.79/1.01  thf('317', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         ((m1_subset_1 @ 
% 0.79/1.01           (k1_partfun1 @ sk_B @ (k1_relat_1 @ sk_C) @ X2 @ X0 @ 
% 0.79/1.01            (k2_funct_1 @ sk_C) @ X1) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.79/1.01          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.79/1.01          | ~ (v1_funct_1 @ X1)
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['315', '316'])).
% 0.79/1.01  thf('318', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['70'])).
% 0.79/1.01  thf('319', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         ((m1_subset_1 @ 
% 0.79/1.01           (k1_partfun1 @ sk_B @ (k1_relat_1 @ sk_C) @ X2 @ X0 @ 
% 0.79/1.01            (k2_funct_1 @ sk_C) @ X1) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.79/1.01          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.79/1.01          | ~ (v1_funct_1 @ X1))),
% 0.79/1.01      inference('demod', [status(thm)], ['317', '318'])).
% 0.79/1.01  thf('320', plain,
% 0.79/1.01      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 0.79/1.01         = (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['74', '75', '86'])).
% 0.79/1.01  thf('321', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/1.01          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.79/1.01          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.79/1.01               (k6_partfun1 @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.79/1.01  thf('322', plain,
% 0.79/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.79/1.01           (k6_partfun1 @ sk_A))
% 0.79/1.01        | ((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) = (sk_A))
% 0.79/1.01        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/1.01             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/1.01        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.79/1.01        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['320', '321'])).
% 0.79/1.01  thf('323', plain,
% 0.79/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('simplify', [status(thm)], ['59'])).
% 0.79/1.01  thf('324', plain,
% 0.79/1.01      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.79/1.01         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.79/1.01          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.79/1.01  thf('325', plain,
% 0.79/1.01      (((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C))
% 0.79/1.01         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['323', '324'])).
% 0.79/1.01  thf('326', plain,
% 0.79/1.01      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.79/1.01      inference('demod', [status(thm)], ['306', '307', '308'])).
% 0.79/1.01  thf('327', plain,
% 0.79/1.01      (((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.79/1.01      inference('demod', [status(thm)], ['325', '326'])).
% 0.79/1.01  thf('328', plain,
% 0.79/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('simplify', [status(thm)], ['59'])).
% 0.79/1.01  thf('329', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('330', plain,
% 0.79/1.01      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X50)
% 0.79/1.01          | ((k2_relset_1 @ X52 @ X51 @ X50) != (X51))
% 0.79/1.01          | (v1_funct_2 @ (k2_funct_1 @ X50) @ X51 @ X52)
% 0.79/1.01          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 0.79/1.01          | ~ (v1_funct_2 @ X50 @ X52 @ X51)
% 0.79/1.01          | ~ (v1_funct_1 @ X50))),
% 0.79/1.01      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.79/1.01  thf('331', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.79/1.01        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.79/1.01        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['329', '330'])).
% 0.79/1.01  thf('332', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('333', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('334', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('335', plain, ((v2_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('336', plain,
% 0.79/1.01      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['331', '332', '333', '334', '335'])).
% 0.79/1.01  thf('337', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.79/1.01      inference('simplify', [status(thm)], ['336'])).
% 0.79/1.01  thf('338', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['70'])).
% 0.79/1.01  thf('339', plain,
% 0.79/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.79/1.01           (k6_partfun1 @ sk_A))
% 0.79/1.01        | ((k1_relat_1 @ sk_C) = (sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['322', '327', '328', '337', '338'])).
% 0.79/1.01  thf('340', plain,
% 0.79/1.01      ((m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['62', '71', '87'])).
% 0.79/1.01  thf('341', plain,
% 0.79/1.01      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.79/1.01          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.79/1.01          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 0.79/1.01          | ((X18) != (X21)))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.79/1.01  thf('342', plain,
% 0.79/1.01      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.79/1.01         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 0.79/1.01          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.79/1.01      inference('simplify', [status(thm)], ['341'])).
% 0.79/1.01  thf('343', plain,
% 0.79/1.01      ((r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('sup-', [status(thm)], ['340', '342'])).
% 0.79/1.01  thf('344', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['339', '343'])).
% 0.79/1.01  thf('345', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         ((m1_subset_1 @ 
% 0.79/1.01           (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ (k2_funct_1 @ sk_C) @ X1) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.79/1.01          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.79/1.01          | ~ (v1_funct_1 @ X1))),
% 0.79/1.01      inference('demod', [status(thm)], ['319', '344'])).
% 0.79/1.01  thf('346', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | (m1_subset_1 @ 
% 0.79/1.01           (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_C) @ 
% 0.79/1.01            sk_C) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['186', '345'])).
% 0.79/1.01  thf('347', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('348', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('349', plain,
% 0.79/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('simplify', [status(thm)], ['59'])).
% 0.79/1.01  thf('350', plain,
% 0.79/1.01      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.86/1.01          | ~ (v1_funct_1 @ X30)
% 0.86/1.01          | ~ (v1_funct_1 @ X33)
% 0.86/1.01          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.86/1.01          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 0.86/1.01              = (k5_relat_1 @ X30 @ X33)))),
% 0.86/1.01      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.86/1.01  thf('351', plain,
% 0.86/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.01         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.86/1.01            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 0.86/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.86/1.01          | ~ (v1_funct_1 @ X0)
% 0.86/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.86/1.01      inference('sup-', [status(thm)], ['349', '350'])).
% 0.86/1.01  thf('352', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.86/1.01      inference('simplify', [status(thm)], ['70'])).
% 0.86/1.01  thf('353', plain,
% 0.86/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.01         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.86/1.01            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 0.86/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.86/1.01          | ~ (v1_funct_1 @ X0))),
% 0.86/1.01      inference('demod', [status(thm)], ['351', '352'])).
% 0.86/1.01  thf('354', plain,
% 0.86/1.01      ((~ (v1_funct_1 @ sk_C)
% 0.86/1.01        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_C) @ 
% 0.86/1.01            sk_C) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 0.86/1.01      inference('sup-', [status(thm)], ['348', '353'])).
% 0.86/1.01  thf('355', plain, ((v1_funct_1 @ sk_C)),
% 0.86/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.01  thf('356', plain,
% 0.86/1.01      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.86/1.01      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.86/1.01  thf('357', plain,
% 0.86/1.01      (![X7 : $i, X8 : $i]:
% 0.86/1.01         (~ (v1_relat_1 @ X7)
% 0.86/1.01          | ~ (v1_funct_1 @ X7)
% 0.86/1.01          | ((X7) = (k2_funct_1 @ X8))
% 0.86/1.01          | ((k5_relat_1 @ X7 @ X8) != (k6_partfun1 @ (k2_relat_1 @ X8)))
% 0.86/1.01          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.86/1.01          | ~ (v2_funct_1 @ X8)
% 0.86/1.01          | ~ (v1_funct_1 @ X8)
% 0.86/1.01          | ~ (v1_relat_1 @ X8))),
% 0.86/1.01      inference('demod', [status(thm)], ['115', '116'])).
% 0.86/1.01  thf('358', plain,
% 0.86/1.01      ((((k6_partfun1 @ sk_A)
% 0.86/1.01          != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.86/1.01        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.86/1.01        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.86/1.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.86/1.01        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.86/1.01        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.86/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.86/1.01        | ~ (v1_relat_1 @ sk_C))),
% 0.86/1.01      inference('sup-', [status(thm)], ['356', '357'])).
% 0.86/1.01  thf('359', plain,
% 0.86/1.01      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.86/1.01      inference('demod', [status(thm)], ['306', '307', '308'])).
% 0.86/1.01  thf('360', plain,
% 0.86/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.86/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))),
% 0.86/1.01      inference('demod', [status(thm)], ['312', '313', '314'])).
% 0.86/1.01  thf('361', plain,
% 0.86/1.01      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.86/1.01         ((v1_relat_1 @ X9)
% 0.86/1.01          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.86/1.01      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.86/1.01  thf('362', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.86/1.01      inference('sup-', [status(thm)], ['360', '361'])).
% 0.86/1.01  thf('363', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.86/1.01      inference('simplify', [status(thm)], ['70'])).
% 0.86/1.01  thf('364', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.86/1.01      inference('simplify', [status(thm)], ['238'])).
% 0.86/1.01  thf('365', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.86/1.01      inference('sup+', [status(thm)], ['126', '127'])).
% 0.86/1.01  thf('366', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_B))),
% 0.86/1.01      inference('demod', [status(thm)], ['279', '280', '281'])).
% 0.86/1.01  thf('367', plain, ((v1_funct_1 @ sk_C)),
% 0.86/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.01  thf('368', plain, ((v1_relat_1 @ sk_C)),
% 0.86/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.86/1.01  thf('369', plain,
% 0.86/1.01      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.86/1.01        | ((sk_B) != (sk_B))
% 0.86/1.01        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.86/1.01      inference('demod', [status(thm)],
% 0.86/1.01                ['358', '359', '362', '363', '364', '365', '366', '367', '368'])).
% 0.86/1.01  thf('370', plain,
% 0.86/1.01      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.86/1.01        | ((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 0.86/1.01      inference('simplify', [status(thm)], ['369'])).
% 0.86/1.01  thf('371', plain,
% 0.86/1.01      (![X6 : $i]:
% 0.86/1.01         (~ (v2_funct_1 @ X6)
% 0.86/1.01          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 0.86/1.01              = (k6_relat_1 @ (k1_relat_1 @ X6)))
% 0.86/1.01          | ~ (v1_funct_1 @ X6)
% 0.86/1.01          | ~ (v1_relat_1 @ X6))),
% 0.86/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.86/1.01  thf('372', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.86/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.86/1.01  thf('373', plain,
% 0.86/1.01      (![X6 : $i]:
% 0.86/1.01         (~ (v2_funct_1 @ X6)
% 0.86/1.01          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 0.86/1.01              = (k6_partfun1 @ (k1_relat_1 @ X6)))
% 0.86/1.01          | ~ (v1_funct_1 @ X6)
% 0.86/1.01          | ~ (v1_relat_1 @ X6))),
% 0.86/1.01      inference('demod', [status(thm)], ['371', '372'])).
% 0.86/1.01  thf('374', plain,
% 0.86/1.01      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.86/1.01      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.86/1.01  thf('375', plain,
% 0.86/1.01      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.86/1.01        | ~ (v1_relat_1 @ sk_C)
% 0.86/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.86/1.01        | ~ (v2_funct_1 @ sk_C))),
% 0.86/1.01      inference('sup+', [status(thm)], ['373', '374'])).
% 0.86/1.01  thf('376', plain, ((v1_relat_1 @ sk_C)),
% 0.86/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.86/1.01  thf('377', plain, ((v1_funct_1 @ sk_C)),
% 0.86/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.01  thf('378', plain, ((v2_funct_1 @ sk_C)),
% 0.86/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.01  thf('379', plain,
% 0.86/1.01      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.86/1.01      inference('demod', [status(thm)], ['375', '376', '377', '378'])).
% 0.86/1.01  thf('380', plain,
% 0.86/1.01      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.86/1.01        | ((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A)))),
% 0.86/1.01      inference('demod', [status(thm)], ['370', '379'])).
% 0.86/1.01  thf('381', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.86/1.01      inference('simplify', [status(thm)], ['380'])).
% 0.86/1.01  thf('382', plain,
% 0.86/1.01      (![X6 : $i]:
% 0.86/1.01         (~ (v2_funct_1 @ X6)
% 0.86/1.01          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 0.86/1.01              = (k6_partfun1 @ (k1_relat_1 @ X6)))
% 0.86/1.01          | ~ (v1_funct_1 @ X6)
% 0.86/1.01          | ~ (v1_relat_1 @ X6))),
% 0.86/1.01      inference('demod', [status(thm)], ['371', '372'])).
% 0.86/1.01  thf('383', plain,
% 0.86/1.01      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.86/1.01          = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.86/1.01        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.86/1.01        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.86/1.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.86/1.01      inference('sup+', [status(thm)], ['381', '382'])).
% 0.86/1.01  thf('384', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_B))),
% 0.86/1.01      inference('demod', [status(thm)], ['279', '280', '281'])).
% 0.86/1.01  thf('385', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.86/1.01      inference('sup-', [status(thm)], ['360', '361'])).
% 0.86/1.01  thf('386', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.86/1.01      inference('simplify', [status(thm)], ['70'])).
% 0.86/1.01  thf('387', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.86/1.01      inference('simplify', [status(thm)], ['238'])).
% 0.86/1.01  thf('388', plain,
% 0.86/1.01      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.86/1.01      inference('demod', [status(thm)], ['383', '384', '385', '386', '387'])).
% 0.86/1.01  thf('389', plain,
% 0.86/1.01      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.86/1.01         = (k6_partfun1 @ sk_B))),
% 0.86/1.01      inference('demod', [status(thm)], ['354', '355', '388'])).
% 0.86/1.01  thf('390', plain,
% 0.86/1.01      ((m1_subset_1 @ (k6_partfun1 @ sk_B) @ 
% 0.86/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.86/1.01      inference('demod', [status(thm)], ['346', '347', '389'])).
% 0.86/1.01  thf('391', plain,
% 0.86/1.01      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.86/1.01         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 0.86/1.01          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.86/1.01      inference('simplify', [status(thm)], ['341'])).
% 0.86/1.01  thf('392', plain,
% 0.86/1.01      ((r2_relset_1 @ sk_B @ sk_B @ (k6_partfun1 @ sk_B) @ (k6_partfun1 @ sk_B))),
% 0.86/1.01      inference('sup-', [status(thm)], ['390', '391'])).
% 0.86/1.01  thf('393', plain,
% 0.86/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 0.86/1.02        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.86/1.02      inference('demod', [status(thm)], ['156', '157'])).
% 0.86/1.02  thf('394', plain,
% 0.86/1.02      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.86/1.02         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.86/1.02          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.86/1.02      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.86/1.02  thf('395', plain,
% 0.86/1.02      (((k2_relset_1 @ sk_A @ sk_B @ (k2_funct_1 @ sk_D))
% 0.86/1.02         = (k2_relat_1 @ (k2_funct_1 @ sk_D)))),
% 0.86/1.02      inference('sup-', [status(thm)], ['393', '394'])).
% 0.86/1.02  thf('396', plain,
% 0.86/1.02      ((m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 0.86/1.02        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.86/1.02      inference('demod', [status(thm)], ['156', '157'])).
% 0.86/1.02  thf('397', plain,
% 0.86/1.02      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.86/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.02  thf('398', plain,
% 0.86/1.02      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.86/1.02         (~ (v2_funct_1 @ X50)
% 0.86/1.02          | ((k2_relset_1 @ X52 @ X51 @ X50) != (X51))
% 0.86/1.02          | (v1_funct_2 @ (k2_funct_1 @ X50) @ X51 @ X52)
% 0.86/1.02          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 0.86/1.02          | ~ (v1_funct_2 @ X50 @ X52 @ X51)
% 0.86/1.02          | ~ (v1_funct_1 @ X50))),
% 0.86/1.02      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.86/1.02  thf('399', plain,
% 0.86/1.02      ((~ (v1_funct_1 @ sk_D)
% 0.86/1.02        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.86/1.02        | (v1_funct_2 @ (k2_funct_1 @ sk_D) @ sk_A @ sk_B)
% 0.86/1.02        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.86/1.02        | ~ (v2_funct_1 @ sk_D))),
% 0.86/1.02      inference('sup-', [status(thm)], ['397', '398'])).
% 0.86/1.02  thf('400', plain, ((v1_funct_1 @ sk_D)),
% 0.86/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.02  thf('401', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.86/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.02  thf('402', plain,
% 0.86/1.02      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.86/1.02      inference('sup-', [status(thm)], ['3', '4'])).
% 0.86/1.02  thf('403', plain,
% 0.86/1.02      (((v1_funct_2 @ (k2_funct_1 @ sk_D) @ sk_A @ sk_B)
% 0.86/1.02        | ((k2_relat_1 @ sk_D) != (sk_A))
% 0.86/1.02        | ~ (v2_funct_1 @ sk_D))),
% 0.86/1.02      inference('demod', [status(thm)], ['399', '400', '401', '402'])).
% 0.86/1.02  thf('404', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.86/1.02      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 0.86/1.02  thf('405', plain,
% 0.86/1.02      (((v1_funct_2 @ (k2_funct_1 @ sk_D) @ sk_A @ sk_B)
% 0.86/1.02        | ((sk_A) != (sk_A))
% 0.86/1.02        | ~ (v2_funct_1 @ sk_D))),
% 0.86/1.02      inference('demod', [status(thm)], ['403', '404'])).
% 0.86/1.02  thf('406', plain,
% 0.86/1.02      ((~ (v2_funct_1 @ sk_D)
% 0.86/1.02        | (v1_funct_2 @ (k2_funct_1 @ sk_D) @ sk_A @ sk_B))),
% 0.86/1.02      inference('simplify', [status(thm)], ['405'])).
% 0.86/1.02  thf('407', plain, ((v2_funct_1 @ sk_D)),
% 0.86/1.02      inference('sup-', [status(thm)], ['110', '111'])).
% 0.86/1.02  thf('408', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_D) @ sk_A @ sk_B)),
% 0.86/1.02      inference('demod', [status(thm)], ['406', '407'])).
% 0.86/1.02  thf('409', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_D))),
% 0.86/1.02      inference('demod', [status(thm)], ['174', '175'])).
% 0.86/1.02  thf('410', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_D)) = (sk_B))),
% 0.86/1.02      inference('demod', [status(thm)],
% 0.86/1.02                ['185', '392', '395', '396', '408', '409'])).
% 0.86/1.02  thf('411', plain,
% 0.86/1.02      ((((k1_relat_1 @ sk_D) = (sk_B))
% 0.86/1.02        | ~ (v1_relat_1 @ sk_D)
% 0.86/1.02        | ~ (v1_funct_1 @ sk_D)
% 0.86/1.02        | ~ (v2_funct_1 @ sk_D))),
% 0.86/1.02      inference('sup+', [status(thm)], ['146', '410'])).
% 0.86/1.02  thf('412', plain, ((v1_relat_1 @ sk_D)),
% 0.86/1.02      inference('sup-', [status(thm)], ['120', '121'])).
% 0.86/1.02  thf('413', plain, ((v1_funct_1 @ sk_D)),
% 0.86/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.02  thf('414', plain, ((v2_funct_1 @ sk_D)),
% 0.86/1.02      inference('sup-', [status(thm)], ['110', '111'])).
% 0.86/1.02  thf('415', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 0.86/1.02      inference('demod', [status(thm)], ['411', '412', '413', '414'])).
% 0.86/1.02  thf('416', plain, ((((sk_B) != (sk_B)) | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.86/1.02      inference('demod', [status(thm)], ['145', '415'])).
% 0.86/1.02  thf('417', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.86/1.02      inference('simplify', [status(thm)], ['416'])).
% 0.86/1.02  thf('418', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.86/1.02      inference('demod', [status(thm)], ['113', '417'])).
% 0.86/1.02  thf('419', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.86/1.02      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 0.86/1.02  thf('420', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.86/1.02      inference('sup+', [status(thm)], ['126', '127'])).
% 0.86/1.02  thf('421', plain,
% 0.86/1.02      (![X7 : $i, X8 : $i]:
% 0.86/1.02         (~ (v1_relat_1 @ X7)
% 0.86/1.02          | ~ (v1_funct_1 @ X7)
% 0.86/1.02          | ((X7) = (k2_funct_1 @ X8))
% 0.86/1.02          | ((k5_relat_1 @ X7 @ X8) != (k6_partfun1 @ (k2_relat_1 @ X8)))
% 0.86/1.02          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.86/1.02          | ~ (v2_funct_1 @ X8)
% 0.86/1.02          | ~ (v1_funct_1 @ X8)
% 0.86/1.02          | ~ (v1_relat_1 @ X8))),
% 0.86/1.02      inference('demod', [status(thm)], ['115', '116'])).
% 0.86/1.02  thf('422', plain,
% 0.86/1.02      (![X0 : $i]:
% 0.86/1.02         (((k5_relat_1 @ X0 @ sk_C) != (k6_partfun1 @ sk_B))
% 0.86/1.02          | ~ (v1_relat_1 @ sk_C)
% 0.86/1.02          | ~ (v1_funct_1 @ sk_C)
% 0.86/1.02          | ~ (v2_funct_1 @ sk_C)
% 0.86/1.02          | ((k2_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.86/1.02          | ((X0) = (k2_funct_1 @ sk_C))
% 0.86/1.02          | ~ (v1_funct_1 @ X0)
% 0.86/1.02          | ~ (v1_relat_1 @ X0))),
% 0.86/1.02      inference('sup-', [status(thm)], ['420', '421'])).
% 0.86/1.02  thf('423', plain, ((v1_relat_1 @ sk_C)),
% 0.86/1.02      inference('sup-', [status(thm)], ['130', '131'])).
% 0.86/1.02  thf('424', plain, ((v1_funct_1 @ sk_C)),
% 0.86/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.02  thf('425', plain, ((v2_funct_1 @ sk_C)),
% 0.86/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.02  thf('426', plain,
% 0.86/1.02      (![X0 : $i]:
% 0.86/1.02         (((k5_relat_1 @ X0 @ sk_C) != (k6_partfun1 @ sk_B))
% 0.86/1.02          | ((k2_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.86/1.02          | ((X0) = (k2_funct_1 @ sk_C))
% 0.86/1.02          | ~ (v1_funct_1 @ X0)
% 0.86/1.02          | ~ (v1_relat_1 @ X0))),
% 0.86/1.02      inference('demod', [status(thm)], ['422', '423', '424', '425'])).
% 0.86/1.02  thf('427', plain,
% 0.86/1.02      ((((sk_A) != (k1_relat_1 @ sk_C))
% 0.86/1.02        | ~ (v1_relat_1 @ sk_D)
% 0.86/1.02        | ~ (v1_funct_1 @ sk_D)
% 0.86/1.02        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.86/1.02        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_partfun1 @ sk_B)))),
% 0.86/1.02      inference('sup-', [status(thm)], ['419', '426'])).
% 0.86/1.02  thf('428', plain, ((v1_relat_1 @ sk_D)),
% 0.86/1.02      inference('sup-', [status(thm)], ['120', '121'])).
% 0.86/1.02  thf('429', plain, ((v1_funct_1 @ sk_D)),
% 0.86/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.02  thf('430', plain,
% 0.86/1.02      ((((sk_A) != (k1_relat_1 @ sk_C))
% 0.86/1.02        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.86/1.02        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_partfun1 @ sk_B)))),
% 0.86/1.02      inference('demod', [status(thm)], ['427', '428', '429'])).
% 0.86/1.02  thf('431', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.86/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.02  thf('432', plain,
% 0.86/1.02      ((((sk_A) != (k1_relat_1 @ sk_C))
% 0.86/1.02        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_partfun1 @ sk_B)))),
% 0.86/1.02      inference('simplify_reflect-', [status(thm)], ['430', '431'])).
% 0.86/1.02  thf('433', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.86/1.02      inference('demod', [status(thm)], ['339', '343'])).
% 0.86/1.02  thf('434', plain,
% 0.86/1.02      ((((sk_A) != (sk_A))
% 0.86/1.02        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_partfun1 @ sk_B)))),
% 0.86/1.02      inference('demod', [status(thm)], ['432', '433'])).
% 0.86/1.02  thf('435', plain, (((k5_relat_1 @ sk_D @ sk_C) != (k6_partfun1 @ sk_B))),
% 0.86/1.02      inference('simplify', [status(thm)], ['434'])).
% 0.86/1.02  thf('436', plain, ($false),
% 0.86/1.02      inference('simplify_reflect-', [status(thm)], ['418', '435'])).
% 0.86/1.02  
% 0.86/1.02  % SZS output end Refutation
% 0.86/1.02  
% 0.86/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
