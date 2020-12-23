%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2BIOXr3fKM

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:13 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  210 (1316 expanded)
%              Number of leaves         :   45 ( 397 expanded)
%              Depth                    :   27
%              Number of atoms          : 2047 (35393 expanded)
%              Number of equality atoms :  153 (2375 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( X62 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_funct_2 @ X63 @ X64 @ X62 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X62 ) ) )
      | ( ( k5_relat_1 @ X63 @ ( k2_funct_1 @ X63 ) )
        = ( k6_partfun1 @ X64 ) )
      | ~ ( v2_funct_1 @ X63 )
      | ( ( k2_relset_1 @ X64 @ X62 @ X63 )
       != X62 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('22',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('32',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X28 = X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','34'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('36',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('37',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('38',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','39'])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( r2_relset_1 @ X47 @ X47 @ ( k1_partfun1 @ X47 @ X48 @ X48 @ X47 @ X46 @ X49 ) @ ( k6_partfun1 @ X47 ) )
      | ( ( k2_relset_1 @ X48 @ X47 @ X49 )
        = X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X47 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('49',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 )
      | ( X28 != X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('50',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['47','51','52','53','54','55'])).

thf('57',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','56'])).

thf('58',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','39'])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ( zip_tseitin_0 @ X54 @ X57 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X58 @ X55 @ X55 @ X56 @ X57 @ X54 ) )
      | ( zip_tseitin_1 @ X56 @ X55 )
      | ( ( k2_relset_1 @ X58 @ X55 @ X57 )
       != X55 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X55 ) ) )
      | ~ ( v1_funct_2 @ X57 @ X58 @ X55 )
      | ~ ( v1_funct_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,(
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
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('67',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('68',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('69',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['66','69','70','71','72','73'])).

thf('75',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('77',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X50: $i,X51: $i] :
      ( ( v2_funct_1 @ X51 )
      | ~ ( zip_tseitin_0 @ X51 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('81',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['58','81'])).

thf('83',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','38'])).

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

thf('84',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X20
        = ( k2_funct_1 @ X21 ) )
      | ( ( k5_relat_1 @ X20 @ X21 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X21 ) ) )
      | ( ( k2_relat_1 @ X20 )
       != ( k1_relat_1 @ X21 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('85',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('86',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X20
        = ( k2_funct_1 @ X21 ) )
      | ( ( k5_relat_1 @ X20 @ X21 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X21 ) ) )
      | ( ( k2_relat_1 @ X20 )
       != ( k1_relat_1 @ X21 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
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
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('89',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('91',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('92',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('96',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['87','92','93','98','99','104'])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['47','51','52','53','54','55'])).

thf('107',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','38'])).

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

thf('110',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X15 )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('111',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('114',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['96','97'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('118',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['111','112','113','114','115','116','117'])).

thf('119',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['108','118'])).

thf('120',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['58','81'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('121',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) ) )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('122',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('123',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('124',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('125',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('127',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['79','80'])).

thf('129',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['122','125','126','127','128'])).

thf('130',plain,
    ( ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['119','129'])).

thf('131',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['82','131'])).

thf('133',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X20
        = ( k2_funct_1 @ X21 ) )
      | ( ( k5_relat_1 @ X20 @ X21 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X21 ) ) )
      | ( ( k2_relat_1 @ X20 )
       != ( k1_relat_1 @ X21 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('134',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['96','97'])).

thf('136',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('137',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['47','51','52','53','54','55'])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( X62 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_funct_2 @ X63 @ X64 @ X62 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X62 ) ) )
      | ( ( k5_relat_1 @ X63 @ ( k2_funct_1 @ X63 ) )
        = ( k6_partfun1 @ X64 ) )
      | ~ ( v2_funct_1 @ X63 )
      | ( ( k2_relset_1 @ X64 @ X62 @ X63 )
       != X62 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('142',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['142','143','144','145','146'])).

thf('148',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) ) )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('152',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('154',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['152','153','154','155','156'])).

thf('158',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('160',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138','139','157','158','159'])).

thf('161',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['161','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2BIOXr3fKM
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:50:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.79/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/0.97  % Solved by: fo/fo7.sh
% 0.79/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/0.97  % done 1185 iterations in 0.529s
% 0.79/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/0.97  % SZS output start Refutation
% 0.79/0.97  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.79/0.97  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.79/0.97  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.79/0.97  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.79/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.79/0.97  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.79/0.97  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.79/0.97  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.79/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.79/0.97  thf(sk_D_type, type, sk_D: $i).
% 0.79/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.79/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/0.97  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.79/0.97  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.79/0.97  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.79/0.97  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.79/0.97  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.79/0.97  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.79/0.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.79/0.97  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.79/0.97  thf(sk_C_type, type, sk_C: $i).
% 0.79/0.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.79/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.79/0.97  thf(t36_funct_2, conjecture,
% 0.79/0.97    (![A:$i,B:$i,C:$i]:
% 0.79/0.97     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/0.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/0.97       ( ![D:$i]:
% 0.79/0.97         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.79/0.97             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.79/0.97           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.79/0.97               ( r2_relset_1 @
% 0.79/0.97                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.79/0.97                 ( k6_partfun1 @ A ) ) & 
% 0.79/0.97               ( v2_funct_1 @ C ) ) =>
% 0.79/0.97             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.79/0.97               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.79/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.79/0.97    (~( ![A:$i,B:$i,C:$i]:
% 0.79/0.97        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/0.97            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/0.97          ( ![D:$i]:
% 0.79/0.97            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.79/0.97                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.79/0.97              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.79/0.97                  ( r2_relset_1 @
% 0.79/0.97                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.79/0.97                    ( k6_partfun1 @ A ) ) & 
% 0.79/0.97                  ( v2_funct_1 @ C ) ) =>
% 0.79/0.97                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.79/0.97                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.79/0.97    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.79/0.97  thf('0', plain,
% 0.79/0.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf(t35_funct_2, axiom,
% 0.79/0.97    (![A:$i,B:$i,C:$i]:
% 0.79/0.97     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/0.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/0.97       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.79/0.97         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.79/0.97           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.79/0.97             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.79/0.97  thf('1', plain,
% 0.79/0.97      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.79/0.97         (((X62) = (k1_xboole_0))
% 0.79/0.97          | ~ (v1_funct_1 @ X63)
% 0.79/0.97          | ~ (v1_funct_2 @ X63 @ X64 @ X62)
% 0.79/0.97          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X62)))
% 0.79/0.97          | ((k5_relat_1 @ X63 @ (k2_funct_1 @ X63)) = (k6_partfun1 @ X64))
% 0.79/0.97          | ~ (v2_funct_1 @ X63)
% 0.79/0.97          | ((k2_relset_1 @ X64 @ X62 @ X63) != (X62)))),
% 0.79/0.97      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.79/0.97  thf('2', plain,
% 0.79/0.97      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.79/0.97        | ~ (v2_funct_1 @ sk_D)
% 0.79/0.97        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.79/0.97        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.79/0.97        | ~ (v1_funct_1 @ sk_D)
% 0.79/0.97        | ((sk_A) = (k1_xboole_0)))),
% 0.79/0.97      inference('sup-', [status(thm)], ['0', '1'])).
% 0.79/0.97  thf('3', plain,
% 0.79/0.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf(redefinition_k2_relset_1, axiom,
% 0.79/0.97    (![A:$i,B:$i,C:$i]:
% 0.79/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/0.97       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.79/0.97  thf('4', plain,
% 0.79/0.97      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.79/0.97         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.79/0.97          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.79/0.97      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.79/0.97  thf('5', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.79/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.79/0.97  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('8', plain,
% 0.79/0.97      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.79/0.97        | ~ (v2_funct_1 @ sk_D)
% 0.79/0.97        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.79/0.97        | ((sk_A) = (k1_xboole_0)))),
% 0.79/0.97      inference('demod', [status(thm)], ['2', '5', '6', '7'])).
% 0.79/0.97  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('10', plain,
% 0.79/0.97      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.79/0.97        | ~ (v2_funct_1 @ sk_D)
% 0.79/0.97        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.79/0.97      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.79/0.97  thf('11', plain,
% 0.79/0.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('12', plain,
% 0.79/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf(redefinition_k1_partfun1, axiom,
% 0.79/0.97    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.79/0.97     ( ( ( v1_funct_1 @ E ) & 
% 0.79/0.97         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/0.97         ( v1_funct_1 @ F ) & 
% 0.79/0.97         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.79/0.97       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.79/0.97  thf('13', plain,
% 0.79/0.97      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.79/0.97         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.79/0.97          | ~ (v1_funct_1 @ X39)
% 0.79/0.97          | ~ (v1_funct_1 @ X42)
% 0.79/0.97          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.79/0.97          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 0.79/0.97              = (k5_relat_1 @ X39 @ X42)))),
% 0.79/0.97      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.79/0.97  thf('14', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/0.97         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.79/0.97            = (k5_relat_1 @ sk_C @ X0))
% 0.79/0.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.79/0.97          | ~ (v1_funct_1 @ X0)
% 0.79/0.97          | ~ (v1_funct_1 @ sk_C))),
% 0.79/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.79/0.97  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('16', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/0.97         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.79/0.97            = (k5_relat_1 @ sk_C @ X0))
% 0.79/0.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.79/0.97          | ~ (v1_funct_1 @ X0))),
% 0.79/0.97      inference('demod', [status(thm)], ['14', '15'])).
% 0.79/0.97  thf('17', plain,
% 0.79/0.97      ((~ (v1_funct_1 @ sk_D)
% 0.79/0.97        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/0.97            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.79/0.97      inference('sup-', [status(thm)], ['11', '16'])).
% 0.79/0.97  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('19', plain,
% 0.79/0.97      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/0.97         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.79/0.97      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/0.97  thf('20', plain,
% 0.79/0.97      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/0.97        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.79/0.97        (k6_partfun1 @ sk_A))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('21', plain,
% 0.79/0.97      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/0.97         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.79/0.97      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/0.97  thf('22', plain,
% 0.79/0.97      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.79/0.97        (k6_partfun1 @ sk_A))),
% 0.79/0.97      inference('demod', [status(thm)], ['20', '21'])).
% 0.79/0.97  thf('23', plain,
% 0.79/0.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('24', plain,
% 0.79/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf(dt_k1_partfun1, axiom,
% 0.79/0.97    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.79/0.97     ( ( ( v1_funct_1 @ E ) & 
% 0.79/0.97         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/0.97         ( v1_funct_1 @ F ) & 
% 0.79/0.97         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.79/0.97       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.79/0.97         ( m1_subset_1 @
% 0.79/0.97           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.79/0.97           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.79/0.97  thf('25', plain,
% 0.79/0.97      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.79/0.97         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.79/0.97          | ~ (v1_funct_1 @ X33)
% 0.79/0.97          | ~ (v1_funct_1 @ X36)
% 0.79/0.97          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.79/0.97          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 0.79/0.97             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 0.79/0.97      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.79/0.97  thf('26', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/0.97         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.79/0.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.79/0.97          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.79/0.97          | ~ (v1_funct_1 @ X1)
% 0.79/0.97          | ~ (v1_funct_1 @ sk_C))),
% 0.79/0.97      inference('sup-', [status(thm)], ['24', '25'])).
% 0.79/0.97  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('28', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/0.97         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.79/0.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.79/0.97          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.79/0.97          | ~ (v1_funct_1 @ X1))),
% 0.79/0.97      inference('demod', [status(thm)], ['26', '27'])).
% 0.79/0.97  thf('29', plain,
% 0.79/0.97      ((~ (v1_funct_1 @ sk_D)
% 0.79/0.97        | (m1_subset_1 @ 
% 0.79/0.97           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.79/0.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.79/0.97      inference('sup-', [status(thm)], ['23', '28'])).
% 0.79/0.97  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('31', plain,
% 0.79/0.97      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/0.97         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.79/0.97      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/0.97  thf('32', plain,
% 0.79/0.97      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.79/0.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/0.97      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.79/0.97  thf(redefinition_r2_relset_1, axiom,
% 0.79/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/0.97     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/0.97         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/0.97       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.79/0.97  thf('33', plain,
% 0.79/0.97      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.79/0.97         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.79/0.97          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.79/0.97          | ((X28) = (X31))
% 0.79/0.97          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 0.79/0.97      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.79/0.97  thf('34', plain,
% 0.79/0.97      (![X0 : $i]:
% 0.79/0.97         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.79/0.97          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.79/0.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.79/0.97      inference('sup-', [status(thm)], ['32', '33'])).
% 0.79/0.97  thf('35', plain,
% 0.79/0.97      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.79/0.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.79/0.97        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.79/0.97      inference('sup-', [status(thm)], ['22', '34'])).
% 0.79/0.97  thf(t29_relset_1, axiom,
% 0.79/0.97    (![A:$i]:
% 0.79/0.97     ( m1_subset_1 @
% 0.79/0.97       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.79/0.97  thf('36', plain,
% 0.79/0.97      (![X32 : $i]:
% 0.79/0.97         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 0.79/0.97          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.79/0.97      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.79/0.97  thf(redefinition_k6_partfun1, axiom,
% 0.79/0.97    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.79/0.97  thf('37', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 0.79/0.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/0.97  thf('38', plain,
% 0.79/0.97      (![X32 : $i]:
% 0.79/0.97         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 0.79/0.97          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.79/0.97      inference('demod', [status(thm)], ['36', '37'])).
% 0.79/0.97  thf('39', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.79/0.97      inference('demod', [status(thm)], ['35', '38'])).
% 0.79/0.97  thf('40', plain,
% 0.79/0.97      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/0.97         = (k6_partfun1 @ sk_A))),
% 0.79/0.97      inference('demod', [status(thm)], ['19', '39'])).
% 0.79/0.97  thf('41', plain,
% 0.79/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf(t24_funct_2, axiom,
% 0.79/0.97    (![A:$i,B:$i,C:$i]:
% 0.79/0.97     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/0.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/0.97       ( ![D:$i]:
% 0.79/0.97         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.79/0.97             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.79/0.97           ( ( r2_relset_1 @
% 0.79/0.97               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.79/0.97               ( k6_partfun1 @ B ) ) =>
% 0.79/0.97             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.79/0.97  thf('42', plain,
% 0.79/0.97      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.79/0.97         (~ (v1_funct_1 @ X46)
% 0.79/0.97          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 0.79/0.97          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.79/0.97          | ~ (r2_relset_1 @ X47 @ X47 @ 
% 0.79/0.97               (k1_partfun1 @ X47 @ X48 @ X48 @ X47 @ X46 @ X49) @ 
% 0.79/0.97               (k6_partfun1 @ X47))
% 0.79/0.97          | ((k2_relset_1 @ X48 @ X47 @ X49) = (X47))
% 0.79/0.97          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47)))
% 0.79/0.97          | ~ (v1_funct_2 @ X49 @ X48 @ X47)
% 0.79/0.97          | ~ (v1_funct_1 @ X49))),
% 0.79/0.97      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.79/0.97  thf('43', plain,
% 0.79/0.97      (![X0 : $i]:
% 0.79/0.97         (~ (v1_funct_1 @ X0)
% 0.79/0.97          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.79/0.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/0.97          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.79/0.97          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/0.97               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.79/0.97               (k6_partfun1 @ sk_A))
% 0.79/0.97          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.79/0.97          | ~ (v1_funct_1 @ sk_C))),
% 0.79/0.97      inference('sup-', [status(thm)], ['41', '42'])).
% 0.79/0.97  thf('44', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('46', plain,
% 0.79/0.97      (![X0 : $i]:
% 0.79/0.97         (~ (v1_funct_1 @ X0)
% 0.79/0.97          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.79/0.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/0.97          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.79/0.97          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/0.97               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.79/0.97               (k6_partfun1 @ sk_A)))),
% 0.79/0.97      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.79/0.97  thf('47', plain,
% 0.79/0.97      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.79/0.97           (k6_partfun1 @ sk_A))
% 0.79/0.97        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.79/0.97        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/0.97        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.79/0.97        | ~ (v1_funct_1 @ sk_D))),
% 0.79/0.97      inference('sup-', [status(thm)], ['40', '46'])).
% 0.79/0.97  thf('48', plain,
% 0.79/0.97      (![X32 : $i]:
% 0.79/0.97         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 0.79/0.97          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.79/0.97      inference('demod', [status(thm)], ['36', '37'])).
% 0.79/0.97  thf('49', plain,
% 0.79/0.97      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.79/0.97         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.79/0.97          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.79/0.97          | (r2_relset_1 @ X29 @ X30 @ X28 @ X31)
% 0.79/0.97          | ((X28) != (X31)))),
% 0.79/0.97      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.79/0.97  thf('50', plain,
% 0.79/0.97      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.79/0.97         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 0.79/0.97          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.79/0.97      inference('simplify', [status(thm)], ['49'])).
% 0.79/0.97  thf('51', plain,
% 0.79/0.97      (![X0 : $i]:
% 0.79/0.97         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.79/0.97      inference('sup-', [status(thm)], ['48', '50'])).
% 0.79/0.97  thf('52', plain,
% 0.79/0.97      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.79/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.79/0.97  thf('53', plain,
% 0.79/0.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('54', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('56', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.79/0.97      inference('demod', [status(thm)], ['47', '51', '52', '53', '54', '55'])).
% 0.79/0.97  thf('57', plain,
% 0.79/0.97      ((((sk_A) != (sk_A))
% 0.79/0.97        | ~ (v2_funct_1 @ sk_D)
% 0.79/0.97        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.79/0.97      inference('demod', [status(thm)], ['10', '56'])).
% 0.79/0.97  thf('58', plain,
% 0.79/0.97      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.79/0.97        | ~ (v2_funct_1 @ sk_D))),
% 0.79/0.97      inference('simplify', [status(thm)], ['57'])).
% 0.79/0.97  thf('59', plain,
% 0.79/0.97      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/0.97         = (k6_partfun1 @ sk_A))),
% 0.79/0.97      inference('demod', [status(thm)], ['19', '39'])).
% 0.79/0.97  thf('60', plain,
% 0.79/0.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf(t30_funct_2, axiom,
% 0.79/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/0.97     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/0.97         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.79/0.97       ( ![E:$i]:
% 0.79/0.97         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.79/0.97             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.79/0.97           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.79/0.97               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.79/0.97             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.79/0.97               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.79/0.97  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.79/0.97  thf(zf_stmt_2, axiom,
% 0.79/0.97    (![C:$i,B:$i]:
% 0.79/0.97     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.79/0.97       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.79/0.97  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.79/0.97  thf(zf_stmt_4, axiom,
% 0.79/0.97    (![E:$i,D:$i]:
% 0.79/0.97     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.79/0.97  thf(zf_stmt_5, axiom,
% 0.79/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/0.97     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.79/0.97         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/0.97       ( ![E:$i]:
% 0.79/0.97         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.79/0.97             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.79/0.97           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.79/0.97               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.79/0.97             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.79/0.97  thf('61', plain,
% 0.79/0.97      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.79/0.97         (~ (v1_funct_1 @ X54)
% 0.79/0.97          | ~ (v1_funct_2 @ X54 @ X55 @ X56)
% 0.79/0.97          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 0.79/0.97          | (zip_tseitin_0 @ X54 @ X57)
% 0.79/0.97          | ~ (v2_funct_1 @ (k1_partfun1 @ X58 @ X55 @ X55 @ X56 @ X57 @ X54))
% 0.79/0.97          | (zip_tseitin_1 @ X56 @ X55)
% 0.79/0.97          | ((k2_relset_1 @ X58 @ X55 @ X57) != (X55))
% 0.79/0.97          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X55)))
% 0.79/0.97          | ~ (v1_funct_2 @ X57 @ X58 @ X55)
% 0.79/0.97          | ~ (v1_funct_1 @ X57))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.79/0.97  thf('62', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i]:
% 0.79/0.97         (~ (v1_funct_1 @ X0)
% 0.79/0.97          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.79/0.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.79/0.97          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.79/0.97          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.79/0.97          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.79/0.97          | (zip_tseitin_0 @ sk_D @ X0)
% 0.79/0.97          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.79/0.97          | ~ (v1_funct_1 @ sk_D))),
% 0.79/0.97      inference('sup-', [status(thm)], ['60', '61'])).
% 0.79/0.97  thf('63', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('65', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i]:
% 0.79/0.97         (~ (v1_funct_1 @ X0)
% 0.79/0.97          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.79/0.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.79/0.97          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.79/0.97          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.79/0.97          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.79/0.97          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.79/0.97      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.79/0.97  thf('66', plain,
% 0.79/0.97      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.79/0.97        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.79/0.97        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.79/0.97        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.79/0.97        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.79/0.97        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.79/0.97        | ~ (v1_funct_1 @ sk_C))),
% 0.79/0.97      inference('sup-', [status(thm)], ['59', '65'])).
% 0.79/0.97  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.79/0.97  thf('67', plain, (![X17 : $i]: (v2_funct_1 @ (k6_relat_1 @ X17))),
% 0.79/0.97      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.79/0.97  thf('68', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 0.79/0.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/0.97  thf('69', plain, (![X17 : $i]: (v2_funct_1 @ (k6_partfun1 @ X17))),
% 0.79/0.97      inference('demod', [status(thm)], ['67', '68'])).
% 0.79/0.97  thf('70', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('71', plain,
% 0.79/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('72', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('74', plain,
% 0.79/0.97      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.79/0.97        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.79/0.97        | ((sk_B) != (sk_B)))),
% 0.79/0.97      inference('demod', [status(thm)], ['66', '69', '70', '71', '72', '73'])).
% 0.79/0.97  thf('75', plain,
% 0.79/0.97      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.79/0.97      inference('simplify', [status(thm)], ['74'])).
% 0.79/0.97  thf('76', plain,
% 0.79/0.97      (![X52 : $i, X53 : $i]:
% 0.79/0.97         (((X52) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X52 @ X53))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.79/0.97  thf('77', plain,
% 0.79/0.97      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.79/0.97      inference('sup-', [status(thm)], ['75', '76'])).
% 0.79/0.97  thf('78', plain, (((sk_A) != (k1_xboole_0))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('79', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.79/0.97      inference('simplify_reflect-', [status(thm)], ['77', '78'])).
% 0.79/0.97  thf('80', plain,
% 0.79/0.97      (![X50 : $i, X51 : $i]:
% 0.79/0.97         ((v2_funct_1 @ X51) | ~ (zip_tseitin_0 @ X51 @ X50))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.79/0.97  thf('81', plain, ((v2_funct_1 @ sk_D)),
% 0.79/0.97      inference('sup-', [status(thm)], ['79', '80'])).
% 0.79/0.97  thf('82', plain,
% 0.79/0.97      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.79/0.97      inference('demod', [status(thm)], ['58', '81'])).
% 0.79/0.97  thf('83', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.79/0.97      inference('demod', [status(thm)], ['35', '38'])).
% 0.79/0.97  thf(t64_funct_1, axiom,
% 0.79/0.97    (![A:$i]:
% 0.79/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/0.97       ( ![B:$i]:
% 0.79/0.97         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.79/0.97           ( ( ( v2_funct_1 @ A ) & 
% 0.79/0.97               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.79/0.97               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.79/0.97             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.79/0.97  thf('84', plain,
% 0.79/0.97      (![X20 : $i, X21 : $i]:
% 0.79/0.97         (~ (v1_relat_1 @ X20)
% 0.79/0.97          | ~ (v1_funct_1 @ X20)
% 0.79/0.97          | ((X20) = (k2_funct_1 @ X21))
% 0.79/0.97          | ((k5_relat_1 @ X20 @ X21) != (k6_relat_1 @ (k2_relat_1 @ X21)))
% 0.79/0.97          | ((k2_relat_1 @ X20) != (k1_relat_1 @ X21))
% 0.79/0.97          | ~ (v2_funct_1 @ X21)
% 0.79/0.97          | ~ (v1_funct_1 @ X21)
% 0.79/0.97          | ~ (v1_relat_1 @ X21))),
% 0.79/0.97      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.79/0.97  thf('85', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 0.79/0.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/0.97  thf('86', plain,
% 0.79/0.97      (![X20 : $i, X21 : $i]:
% 0.79/0.97         (~ (v1_relat_1 @ X20)
% 0.79/0.97          | ~ (v1_funct_1 @ X20)
% 0.79/0.97          | ((X20) = (k2_funct_1 @ X21))
% 0.79/0.97          | ((k5_relat_1 @ X20 @ X21) != (k6_partfun1 @ (k2_relat_1 @ X21)))
% 0.79/0.97          | ((k2_relat_1 @ X20) != (k1_relat_1 @ X21))
% 0.79/0.97          | ~ (v2_funct_1 @ X21)
% 0.79/0.97          | ~ (v1_funct_1 @ X21)
% 0.79/0.97          | ~ (v1_relat_1 @ X21))),
% 0.79/0.97      inference('demod', [status(thm)], ['84', '85'])).
% 0.79/0.97  thf('87', plain,
% 0.79/0.97      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.79/0.97        | ~ (v1_relat_1 @ sk_D)
% 0.79/0.97        | ~ (v1_funct_1 @ sk_D)
% 0.79/0.97        | ~ (v2_funct_1 @ sk_D)
% 0.79/0.97        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.79/0.97        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.79/0.97        | ~ (v1_funct_1 @ sk_C)
% 0.79/0.97        | ~ (v1_relat_1 @ sk_C))),
% 0.79/0.97      inference('sup-', [status(thm)], ['83', '86'])).
% 0.79/0.97  thf('88', plain,
% 0.79/0.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf(cc2_relat_1, axiom,
% 0.79/0.97    (![A:$i]:
% 0.79/0.97     ( ( v1_relat_1 @ A ) =>
% 0.79/0.97       ( ![B:$i]:
% 0.79/0.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.79/0.97  thf('89', plain,
% 0.79/0.97      (![X3 : $i, X4 : $i]:
% 0.79/0.97         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.79/0.97          | (v1_relat_1 @ X3)
% 0.79/0.97          | ~ (v1_relat_1 @ X4))),
% 0.79/0.97      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.79/0.97  thf('90', plain,
% 0.79/0.97      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.79/0.97      inference('sup-', [status(thm)], ['88', '89'])).
% 0.79/0.97  thf(fc6_relat_1, axiom,
% 0.79/0.97    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.79/0.97  thf('91', plain,
% 0.79/0.97      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.79/0.97      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.79/0.97  thf('92', plain, ((v1_relat_1 @ sk_D)),
% 0.79/0.97      inference('demod', [status(thm)], ['90', '91'])).
% 0.79/0.97  thf('93', plain, ((v1_funct_1 @ sk_D)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('94', plain,
% 0.79/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('95', plain,
% 0.79/0.97      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.79/0.97         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.79/0.97          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.79/0.97      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.79/0.97  thf('96', plain,
% 0.79/0.97      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.79/0.97      inference('sup-', [status(thm)], ['94', '95'])).
% 0.79/0.97  thf('97', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('98', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.79/0.97      inference('sup+', [status(thm)], ['96', '97'])).
% 0.79/0.97  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('100', plain,
% 0.79/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('101', plain,
% 0.79/0.97      (![X3 : $i, X4 : $i]:
% 0.79/0.97         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.79/0.97          | (v1_relat_1 @ X3)
% 0.79/0.97          | ~ (v1_relat_1 @ X4))),
% 0.79/0.97      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.79/0.97  thf('102', plain,
% 0.79/0.97      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.79/0.97      inference('sup-', [status(thm)], ['100', '101'])).
% 0.79/0.97  thf('103', plain,
% 0.79/0.97      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.79/0.97      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.79/0.97  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.97      inference('demod', [status(thm)], ['102', '103'])).
% 0.79/0.97  thf('105', plain,
% 0.79/0.97      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.79/0.97        | ~ (v2_funct_1 @ sk_D)
% 0.79/0.97        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.79/0.97        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.79/0.97      inference('demod', [status(thm)], ['87', '92', '93', '98', '99', '104'])).
% 0.79/0.97  thf('106', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.79/0.97      inference('demod', [status(thm)], ['47', '51', '52', '53', '54', '55'])).
% 0.79/0.97  thf('107', plain,
% 0.79/0.97      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.79/0.97        | ~ (v2_funct_1 @ sk_D)
% 0.79/0.97        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.79/0.97        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.79/0.97      inference('demod', [status(thm)], ['105', '106'])).
% 0.79/0.97  thf('108', plain,
% 0.79/0.97      ((((sk_C) = (k2_funct_1 @ sk_D))
% 0.79/0.97        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.79/0.97        | ~ (v2_funct_1 @ sk_D))),
% 0.79/0.97      inference('simplify', [status(thm)], ['107'])).
% 0.79/0.97  thf('109', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.79/0.97      inference('demod', [status(thm)], ['35', '38'])).
% 0.79/0.97  thf(t48_funct_1, axiom,
% 0.79/0.97    (![A:$i]:
% 0.79/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/0.97       ( ![B:$i]:
% 0.79/0.97         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.79/0.97           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.79/0.97               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.79/0.97             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.79/0.97  thf('110', plain,
% 0.79/0.97      (![X15 : $i, X16 : $i]:
% 0.79/0.97         (~ (v1_relat_1 @ X15)
% 0.79/0.97          | ~ (v1_funct_1 @ X15)
% 0.79/0.97          | (v2_funct_1 @ X16)
% 0.79/0.97          | ((k2_relat_1 @ X15) != (k1_relat_1 @ X16))
% 0.79/0.97          | ~ (v2_funct_1 @ (k5_relat_1 @ X15 @ X16))
% 0.79/0.97          | ~ (v1_funct_1 @ X16)
% 0.79/0.97          | ~ (v1_relat_1 @ X16))),
% 0.79/0.97      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.79/0.97  thf('111', plain,
% 0.79/0.97      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.79/0.97        | ~ (v1_relat_1 @ sk_D)
% 0.79/0.97        | ~ (v1_funct_1 @ sk_D)
% 0.79/0.97        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.79/0.97        | (v2_funct_1 @ sk_D)
% 0.79/0.97        | ~ (v1_funct_1 @ sk_C)
% 0.79/0.97        | ~ (v1_relat_1 @ sk_C))),
% 0.79/0.97      inference('sup-', [status(thm)], ['109', '110'])).
% 0.79/0.97  thf('112', plain, (![X17 : $i]: (v2_funct_1 @ (k6_partfun1 @ X17))),
% 0.79/0.97      inference('demod', [status(thm)], ['67', '68'])).
% 0.79/0.97  thf('113', plain, ((v1_relat_1 @ sk_D)),
% 0.79/0.97      inference('demod', [status(thm)], ['90', '91'])).
% 0.79/0.97  thf('114', plain, ((v1_funct_1 @ sk_D)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('115', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.79/0.97      inference('sup+', [status(thm)], ['96', '97'])).
% 0.79/0.97  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('117', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.97      inference('demod', [status(thm)], ['102', '103'])).
% 0.79/0.97  thf('118', plain, ((((sk_B) != (k1_relat_1 @ sk_D)) | (v2_funct_1 @ sk_D))),
% 0.79/0.97      inference('demod', [status(thm)],
% 0.79/0.97                ['111', '112', '113', '114', '115', '116', '117'])).
% 0.79/0.97  thf('119', plain,
% 0.79/0.97      ((((sk_B) != (k1_relat_1 @ sk_D)) | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.79/0.97      inference('clc', [status(thm)], ['108', '118'])).
% 0.79/0.97  thf('120', plain,
% 0.79/0.97      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.79/0.97      inference('demod', [status(thm)], ['58', '81'])).
% 0.79/0.97  thf(t58_funct_1, axiom,
% 0.79/0.97    (![A:$i]:
% 0.79/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/0.97       ( ( v2_funct_1 @ A ) =>
% 0.79/0.97         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.79/0.97             ( k1_relat_1 @ A ) ) & 
% 0.79/0.97           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.79/0.97             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.79/0.97  thf('121', plain,
% 0.79/0.97      (![X19 : $i]:
% 0.79/0.97         (~ (v2_funct_1 @ X19)
% 0.79/0.97          | ((k2_relat_1 @ (k5_relat_1 @ X19 @ (k2_funct_1 @ X19)))
% 0.79/0.97              = (k1_relat_1 @ X19))
% 0.79/0.97          | ~ (v1_funct_1 @ X19)
% 0.79/0.97          | ~ (v1_relat_1 @ X19))),
% 0.79/0.97      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.79/0.97  thf('122', plain,
% 0.79/0.97      ((((k2_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 0.79/0.97        | ~ (v1_relat_1 @ sk_D)
% 0.79/0.97        | ~ (v1_funct_1 @ sk_D)
% 0.79/0.97        | ~ (v2_funct_1 @ sk_D))),
% 0.79/0.97      inference('sup+', [status(thm)], ['120', '121'])).
% 0.79/0.97  thf(t71_relat_1, axiom,
% 0.79/0.97    (![A:$i]:
% 0.79/0.97     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.79/0.97       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.79/0.97  thf('123', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.79/0.97      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.79/0.97  thf('124', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 0.79/0.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/0.97  thf('125', plain,
% 0.79/0.97      (![X12 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 0.79/0.97      inference('demod', [status(thm)], ['123', '124'])).
% 0.79/0.97  thf('126', plain, ((v1_relat_1 @ sk_D)),
% 0.79/0.97      inference('demod', [status(thm)], ['90', '91'])).
% 0.79/0.97  thf('127', plain, ((v1_funct_1 @ sk_D)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('128', plain, ((v2_funct_1 @ sk_D)),
% 0.79/0.97      inference('sup-', [status(thm)], ['79', '80'])).
% 0.79/0.97  thf('129', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.79/0.97      inference('demod', [status(thm)], ['122', '125', '126', '127', '128'])).
% 0.79/0.97  thf('130', plain, ((((sk_B) != (sk_B)) | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.79/0.97      inference('demod', [status(thm)], ['119', '129'])).
% 0.79/0.97  thf('131', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.79/0.97      inference('simplify', [status(thm)], ['130'])).
% 0.79/0.97  thf('132', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.79/0.97      inference('demod', [status(thm)], ['82', '131'])).
% 0.79/0.97  thf('133', plain,
% 0.79/0.97      (![X20 : $i, X21 : $i]:
% 0.79/0.97         (~ (v1_relat_1 @ X20)
% 0.79/0.97          | ~ (v1_funct_1 @ X20)
% 0.79/0.97          | ((X20) = (k2_funct_1 @ X21))
% 0.79/0.97          | ((k5_relat_1 @ X20 @ X21) != (k6_partfun1 @ (k2_relat_1 @ X21)))
% 0.79/0.97          | ((k2_relat_1 @ X20) != (k1_relat_1 @ X21))
% 0.79/0.97          | ~ (v2_funct_1 @ X21)
% 0.79/0.97          | ~ (v1_funct_1 @ X21)
% 0.79/0.97          | ~ (v1_relat_1 @ X21))),
% 0.79/0.97      inference('demod', [status(thm)], ['84', '85'])).
% 0.79/0.97  thf('134', plain,
% 0.79/0.97      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 0.79/0.97        | ~ (v1_relat_1 @ sk_C)
% 0.79/0.97        | ~ (v1_funct_1 @ sk_C)
% 0.79/0.97        | ~ (v2_funct_1 @ sk_C)
% 0.79/0.97        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 0.79/0.97        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.79/0.97        | ~ (v1_funct_1 @ sk_D)
% 0.79/0.97        | ~ (v1_relat_1 @ sk_D))),
% 0.79/0.97      inference('sup-', [status(thm)], ['132', '133'])).
% 0.79/0.97  thf('135', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.79/0.97      inference('sup+', [status(thm)], ['96', '97'])).
% 0.79/0.97  thf('136', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.97      inference('demod', [status(thm)], ['102', '103'])).
% 0.79/0.97  thf('137', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('139', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.79/0.97      inference('demod', [status(thm)], ['47', '51', '52', '53', '54', '55'])).
% 0.79/0.97  thf('140', plain,
% 0.79/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('141', plain,
% 0.79/0.97      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.79/0.97         (((X62) = (k1_xboole_0))
% 0.79/0.97          | ~ (v1_funct_1 @ X63)
% 0.79/0.97          | ~ (v1_funct_2 @ X63 @ X64 @ X62)
% 0.79/0.97          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X62)))
% 0.79/0.97          | ((k5_relat_1 @ X63 @ (k2_funct_1 @ X63)) = (k6_partfun1 @ X64))
% 0.79/0.97          | ~ (v2_funct_1 @ X63)
% 0.79/0.97          | ((k2_relset_1 @ X64 @ X62 @ X63) != (X62)))),
% 0.79/0.97      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.79/0.97  thf('142', plain,
% 0.79/0.97      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.79/0.97        | ~ (v2_funct_1 @ sk_C)
% 0.79/0.97        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.79/0.97        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.79/0.97        | ~ (v1_funct_1 @ sk_C)
% 0.79/0.97        | ((sk_B) = (k1_xboole_0)))),
% 0.79/0.97      inference('sup-', [status(thm)], ['140', '141'])).
% 0.79/0.97  thf('143', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('145', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('147', plain,
% 0.79/0.97      ((((sk_B) != (sk_B))
% 0.79/0.97        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.79/0.97        | ((sk_B) = (k1_xboole_0)))),
% 0.79/0.97      inference('demod', [status(thm)], ['142', '143', '144', '145', '146'])).
% 0.79/0.97  thf('148', plain,
% 0.79/0.97      ((((sk_B) = (k1_xboole_0))
% 0.79/0.97        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.79/0.97      inference('simplify', [status(thm)], ['147'])).
% 0.79/0.97  thf('149', plain, (((sk_B) != (k1_xboole_0))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('150', plain,
% 0.79/0.97      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.79/0.97      inference('simplify_reflect-', [status(thm)], ['148', '149'])).
% 0.79/0.97  thf('151', plain,
% 0.79/0.97      (![X19 : $i]:
% 0.79/0.97         (~ (v2_funct_1 @ X19)
% 0.79/0.97          | ((k2_relat_1 @ (k5_relat_1 @ X19 @ (k2_funct_1 @ X19)))
% 0.79/0.97              = (k1_relat_1 @ X19))
% 0.79/0.97          | ~ (v1_funct_1 @ X19)
% 0.79/0.97          | ~ (v1_relat_1 @ X19))),
% 0.79/0.97      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.79/0.97  thf('152', plain,
% 0.79/0.97      ((((k2_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 0.79/0.97        | ~ (v1_relat_1 @ sk_C)
% 0.79/0.97        | ~ (v1_funct_1 @ sk_C)
% 0.79/0.97        | ~ (v2_funct_1 @ sk_C))),
% 0.79/0.97      inference('sup+', [status(thm)], ['150', '151'])).
% 0.79/0.97  thf('153', plain,
% 0.79/0.97      (![X12 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 0.79/0.97      inference('demod', [status(thm)], ['123', '124'])).
% 0.79/0.97  thf('154', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.97      inference('demod', [status(thm)], ['102', '103'])).
% 0.79/0.97  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('157', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.79/0.97      inference('demod', [status(thm)], ['152', '153', '154', '155', '156'])).
% 0.79/0.97  thf('158', plain, ((v1_funct_1 @ sk_D)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('159', plain, ((v1_relat_1 @ sk_D)),
% 0.79/0.97      inference('demod', [status(thm)], ['90', '91'])).
% 0.79/0.97  thf('160', plain,
% 0.79/0.97      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 0.79/0.97        | ((sk_A) != (sk_A))
% 0.79/0.97        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.79/0.97      inference('demod', [status(thm)],
% 0.79/0.97                ['134', '135', '136', '137', '138', '139', '157', '158', '159'])).
% 0.79/0.97  thf('161', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.79/0.97      inference('simplify', [status(thm)], ['160'])).
% 0.79/0.97  thf('162', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('163', plain, ($false),
% 0.79/0.97      inference('simplify_reflect-', [status(thm)], ['161', '162'])).
% 0.79/0.97  
% 0.79/0.97  % SZS output end Refutation
% 0.79/0.97  
% 0.79/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
