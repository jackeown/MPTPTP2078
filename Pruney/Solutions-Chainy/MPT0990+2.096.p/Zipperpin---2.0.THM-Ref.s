%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L89lzqWoTG

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:10 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  191 (1092 expanded)
%              Number of leaves         :   43 ( 331 expanded)
%              Depth                    :   27
%              Number of atoms          : 1892 (30783 expanded)
%              Number of equality atoms :  143 (2102 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ X46 @ ( k2_funct_1 @ X46 ) )
        = ( k6_partfun1 @ X47 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
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
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_relset_1 @ X33 @ X33 @ ( k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35 ) @ ( k6_partfun1 @ X33 ) )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A_1 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
      = sk_A_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('29',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('35',plain,
    ( ( sk_A_1 != sk_A_1 )
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
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('38',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('48',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('49',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( X14 = X17 )
      | ~ ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['38','50'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('52',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('53',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['37','55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( zip_tseitin_0 @ X40 @ X43 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X44 @ X41 @ X41 @ X42 @ X43 @ X40 ) )
      | ( zip_tseitin_1 @ X42 @ X41 )
      | ( ( k2_relset_1 @ X44 @ X41 @ X43 )
       != X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('59',plain,(
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
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A_1 ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('64',plain,(
    ! [X4: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('65',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('66',plain,(
    ! [X4: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X4 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['63','66','67','68','69','70'])).

thf('72',plain,
    ( ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X38 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('74',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X36: $i,X37: $i] :
      ( ( v2_funct_1 @ X37 )
      | ~ ( zip_tseitin_0 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('78',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','78'])).

thf('80',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['51','54'])).

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

thf('81',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k2_funct_1 @ X7 ) )
      | ( ( k5_relat_1 @ X6 @ X7 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('82',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('83',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k2_funct_1 @ X7 ) )
      | ( ( k5_relat_1 @ X6 @ X7 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X7 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k6_partfun1 @ sk_A_1 )
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
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('87',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('88',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('92',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k6_partfun1 @ sk_A_1 )
     != ( k6_partfun1 @ sk_A_1 ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['84','85','88','89','94','95','98'])).

thf('100',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','77'])).

thf('102',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','78'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('104',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('105',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('106',plain,(
    ! [X2: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X2 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('107',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('108',plain,(
    ! [X2: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X2 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('110',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','77'])).

thf('112',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['105','108','109','110','111'])).

thf('113',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['102','112'])).

thf('114',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['79','114'])).

thf('116',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k2_funct_1 @ X7 ) )
      | ( ( k5_relat_1 @ X6 @ X7 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X7 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('117',plain,
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
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['92','93'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['96','97'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ X46 @ ( k2_funct_1 @ X46 ) )
        = ( k6_partfun1 @ X47 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('125',plain,
    ( ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['125','126','127','128','129'])).

thf('131',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference('simplify_reflect-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('135',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A_1 ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X2: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X2 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['96','97'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( sk_A_1
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['135','136','137','138','139'])).

thf('141',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('143',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A_1 != sk_A_1 )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121','122','140','141','142'])).

thf('144',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L89lzqWoTG
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:03:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.96/2.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.96/2.18  % Solved by: fo/fo7.sh
% 1.96/2.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.96/2.18  % done 1281 iterations in 1.725s
% 1.96/2.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.96/2.18  % SZS output start Refutation
% 1.96/2.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.96/2.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.96/2.18  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.96/2.18  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.96/2.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.96/2.18  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.96/2.18  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.96/2.18  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.96/2.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.96/2.18  thf(sk_A_1_type, type, sk_A_1: $i).
% 1.96/2.18  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.96/2.18  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.96/2.18  thf(sk_D_type, type, sk_D: $i).
% 1.96/2.18  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.96/2.18  thf(sk_C_type, type, sk_C: $i).
% 1.96/2.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.96/2.18  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.96/2.18  thf(sk_B_type, type, sk_B: $i).
% 1.96/2.18  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.96/2.18  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.96/2.18  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.96/2.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.96/2.18  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.96/2.18  thf(t36_funct_2, conjecture,
% 1.96/2.18    (![A:$i,B:$i,C:$i]:
% 1.96/2.18     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.96/2.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.96/2.18       ( ![D:$i]:
% 1.96/2.18         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.96/2.18             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.96/2.18           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.96/2.18               ( r2_relset_1 @
% 1.96/2.18                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.96/2.18                 ( k6_partfun1 @ A ) ) & 
% 1.96/2.18               ( v2_funct_1 @ C ) ) =>
% 1.96/2.18             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.96/2.18               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.96/2.18  thf(zf_stmt_0, negated_conjecture,
% 1.96/2.18    (~( ![A:$i,B:$i,C:$i]:
% 1.96/2.18        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.96/2.18            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.96/2.18          ( ![D:$i]:
% 1.96/2.18            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.96/2.18                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.96/2.18              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.96/2.18                  ( r2_relset_1 @
% 1.96/2.18                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.96/2.18                    ( k6_partfun1 @ A ) ) & 
% 1.96/2.18                  ( v2_funct_1 @ C ) ) =>
% 1.96/2.18                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.96/2.18                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.96/2.18    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.96/2.18  thf('0', plain,
% 1.96/2.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf(t35_funct_2, axiom,
% 1.96/2.18    (![A:$i,B:$i,C:$i]:
% 1.96/2.18     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.96/2.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.96/2.18       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.96/2.18         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.96/2.18           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.96/2.18             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.96/2.18  thf('1', plain,
% 1.96/2.18      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.96/2.18         (((X45) = (k1_xboole_0))
% 1.96/2.18          | ~ (v1_funct_1 @ X46)
% 1.96/2.18          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 1.96/2.18          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 1.96/2.18          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_partfun1 @ X47))
% 1.96/2.18          | ~ (v2_funct_1 @ X46)
% 1.96/2.18          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 1.96/2.18      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.96/2.18  thf('2', plain,
% 1.96/2.18      ((((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) != (sk_A_1))
% 1.96/2.18        | ~ (v2_funct_1 @ sk_D)
% 1.96/2.18        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.96/2.18        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 1.96/2.18        | ~ (v1_funct_1 @ sk_D)
% 1.96/2.18        | ((sk_A_1) = (k1_xboole_0)))),
% 1.96/2.18      inference('sup-', [status(thm)], ['0', '1'])).
% 1.96/2.18  thf('3', plain,
% 1.96/2.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf(redefinition_k2_relset_1, axiom,
% 1.96/2.18    (![A:$i,B:$i,C:$i]:
% 1.96/2.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.96/2.18       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.96/2.18  thf('4', plain,
% 1.96/2.18      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.96/2.18         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.96/2.18          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.96/2.18      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.96/2.18  thf('5', plain,
% 1.96/2.18      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.96/2.18      inference('sup-', [status(thm)], ['3', '4'])).
% 1.96/2.18  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('8', plain,
% 1.96/2.18      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 1.96/2.18        | ~ (v2_funct_1 @ sk_D)
% 1.96/2.18        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.96/2.18        | ((sk_A_1) = (k1_xboole_0)))),
% 1.96/2.18      inference('demod', [status(thm)], ['2', '5', '6', '7'])).
% 1.96/2.18  thf('9', plain, (((sk_A_1) != (k1_xboole_0))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('10', plain,
% 1.96/2.18      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 1.96/2.18        | ~ (v2_funct_1 @ sk_D)
% 1.96/2.18        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.96/2.18      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 1.96/2.18  thf('11', plain,
% 1.96/2.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('12', plain,
% 1.96/2.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf(redefinition_k1_partfun1, axiom,
% 1.96/2.18    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.96/2.18     ( ( ( v1_funct_1 @ E ) & 
% 1.96/2.18         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.96/2.18         ( v1_funct_1 @ F ) & 
% 1.96/2.18         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.96/2.18       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.96/2.18  thf('13', plain,
% 1.96/2.18      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.96/2.18         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.96/2.18          | ~ (v1_funct_1 @ X25)
% 1.96/2.18          | ~ (v1_funct_1 @ X28)
% 1.96/2.18          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.96/2.18          | ((k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 1.96/2.18              = (k5_relat_1 @ X25 @ X28)))),
% 1.96/2.18      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.96/2.18  thf('14', plain,
% 1.96/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.18         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.96/2.18            = (k5_relat_1 @ sk_C @ X0))
% 1.96/2.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.96/2.18          | ~ (v1_funct_1 @ X0)
% 1.96/2.18          | ~ (v1_funct_1 @ sk_C))),
% 1.96/2.18      inference('sup-', [status(thm)], ['12', '13'])).
% 1.96/2.18  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('16', plain,
% 1.96/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.18         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.96/2.18            = (k5_relat_1 @ sk_C @ X0))
% 1.96/2.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.96/2.18          | ~ (v1_funct_1 @ X0))),
% 1.96/2.18      inference('demod', [status(thm)], ['14', '15'])).
% 1.96/2.18  thf('17', plain,
% 1.96/2.18      ((~ (v1_funct_1 @ sk_D)
% 1.96/2.18        | ((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 1.96/2.18            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.96/2.18      inference('sup-', [status(thm)], ['11', '16'])).
% 1.96/2.18  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('19', plain,
% 1.96/2.18      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 1.96/2.18         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.96/2.18      inference('demod', [status(thm)], ['17', '18'])).
% 1.96/2.18  thf('20', plain,
% 1.96/2.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf(t24_funct_2, axiom,
% 1.96/2.18    (![A:$i,B:$i,C:$i]:
% 1.96/2.18     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.96/2.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.96/2.18       ( ![D:$i]:
% 1.96/2.18         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.96/2.18             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.96/2.18           ( ( r2_relset_1 @
% 1.96/2.18               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.96/2.18               ( k6_partfun1 @ B ) ) =>
% 1.96/2.18             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.96/2.18  thf('21', plain,
% 1.96/2.18      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.96/2.18         (~ (v1_funct_1 @ X32)
% 1.96/2.18          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 1.96/2.18          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.96/2.18          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 1.96/2.18               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 1.96/2.18               (k6_partfun1 @ X33))
% 1.96/2.18          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 1.96/2.18          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 1.96/2.18          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 1.96/2.18          | ~ (v1_funct_1 @ X35))),
% 1.96/2.18      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.96/2.18  thf('22', plain,
% 1.96/2.18      (![X0 : $i]:
% 1.96/2.18         (~ (v1_funct_1 @ X0)
% 1.96/2.18          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 1.96/2.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 1.96/2.18          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 1.96/2.18          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 1.96/2.18               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 1.96/2.18               (k6_partfun1 @ sk_A_1))
% 1.96/2.18          | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 1.96/2.18          | ~ (v1_funct_1 @ sk_C))),
% 1.96/2.18      inference('sup-', [status(thm)], ['20', '21'])).
% 1.96/2.18  thf('23', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('25', plain,
% 1.96/2.18      (![X0 : $i]:
% 1.96/2.18         (~ (v1_funct_1 @ X0)
% 1.96/2.18          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 1.96/2.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 1.96/2.18          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 1.96/2.18          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 1.96/2.18               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 1.96/2.18               (k6_partfun1 @ sk_A_1)))),
% 1.96/2.18      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.96/2.18  thf('26', plain,
% 1.96/2.18      ((~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.96/2.18           (k6_partfun1 @ sk_A_1))
% 1.96/2.18        | ((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (sk_A_1))
% 1.96/2.18        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 1.96/2.18        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 1.96/2.18        | ~ (v1_funct_1 @ sk_D))),
% 1.96/2.18      inference('sup-', [status(thm)], ['19', '25'])).
% 1.96/2.18  thf('27', plain,
% 1.96/2.18      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 1.96/2.18        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 1.96/2.18        (k6_partfun1 @ sk_A_1))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('28', plain,
% 1.96/2.18      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 1.96/2.18         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.96/2.18      inference('demod', [status(thm)], ['17', '18'])).
% 1.96/2.18  thf('29', plain,
% 1.96/2.18      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.96/2.18        (k6_partfun1 @ sk_A_1))),
% 1.96/2.18      inference('demod', [status(thm)], ['27', '28'])).
% 1.96/2.18  thf('30', plain,
% 1.96/2.18      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.96/2.18      inference('sup-', [status(thm)], ['3', '4'])).
% 1.96/2.18  thf('31', plain,
% 1.96/2.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('32', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('34', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 1.96/2.18      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 1.96/2.18  thf('35', plain,
% 1.96/2.18      ((((sk_A_1) != (sk_A_1))
% 1.96/2.18        | ~ (v2_funct_1 @ sk_D)
% 1.96/2.18        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.96/2.18      inference('demod', [status(thm)], ['10', '34'])).
% 1.96/2.18  thf('36', plain,
% 1.96/2.18      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.96/2.18        | ~ (v2_funct_1 @ sk_D))),
% 1.96/2.18      inference('simplify', [status(thm)], ['35'])).
% 1.96/2.18  thf('37', plain,
% 1.96/2.18      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 1.96/2.18         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.96/2.18      inference('demod', [status(thm)], ['17', '18'])).
% 1.96/2.18  thf('38', plain,
% 1.96/2.18      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.96/2.18        (k6_partfun1 @ sk_A_1))),
% 1.96/2.18      inference('demod', [status(thm)], ['27', '28'])).
% 1.96/2.18  thf('39', plain,
% 1.96/2.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('40', plain,
% 1.96/2.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf(dt_k1_partfun1, axiom,
% 1.96/2.18    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.96/2.18     ( ( ( v1_funct_1 @ E ) & 
% 1.96/2.18         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.96/2.18         ( v1_funct_1 @ F ) & 
% 1.96/2.18         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.96/2.18       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.96/2.18         ( m1_subset_1 @
% 1.96/2.18           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.96/2.18           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.96/2.18  thf('41', plain,
% 1.96/2.18      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.96/2.18         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.96/2.18          | ~ (v1_funct_1 @ X19)
% 1.96/2.18          | ~ (v1_funct_1 @ X22)
% 1.96/2.18          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.96/2.18          | (m1_subset_1 @ (k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22) @ 
% 1.96/2.18             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X24))))),
% 1.96/2.18      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.96/2.18  thf('42', plain,
% 1.96/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.18         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.96/2.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 1.96/2.18          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.96/2.18          | ~ (v1_funct_1 @ X1)
% 1.96/2.18          | ~ (v1_funct_1 @ sk_C))),
% 1.96/2.18      inference('sup-', [status(thm)], ['40', '41'])).
% 1.96/2.18  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('44', plain,
% 1.96/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.18         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.96/2.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 1.96/2.18          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.96/2.18          | ~ (v1_funct_1 @ X1))),
% 1.96/2.18      inference('demod', [status(thm)], ['42', '43'])).
% 1.96/2.18  thf('45', plain,
% 1.96/2.18      ((~ (v1_funct_1 @ sk_D)
% 1.96/2.18        | (m1_subset_1 @ 
% 1.96/2.18           (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 1.96/2.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 1.96/2.18      inference('sup-', [status(thm)], ['39', '44'])).
% 1.96/2.18  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('47', plain,
% 1.96/2.18      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 1.96/2.18         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.96/2.18      inference('demod', [status(thm)], ['17', '18'])).
% 1.96/2.18  thf('48', plain,
% 1.96/2.18      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.96/2.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))),
% 1.96/2.18      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.96/2.18  thf(redefinition_r2_relset_1, axiom,
% 1.96/2.18    (![A:$i,B:$i,C:$i,D:$i]:
% 1.96/2.18     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.96/2.18         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.96/2.18       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.96/2.18  thf('49', plain,
% 1.96/2.18      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.96/2.18         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.96/2.18          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.96/2.18          | ((X14) = (X17))
% 1.96/2.18          | ~ (r2_relset_1 @ X15 @ X16 @ X14 @ X17))),
% 1.96/2.18      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.96/2.19  thf('50', plain,
% 1.96/2.19      (![X0 : $i]:
% 1.96/2.19         (~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.96/2.19          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.96/2.19          | ~ (m1_subset_1 @ X0 @ 
% 1.96/2.19               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 1.96/2.19      inference('sup-', [status(thm)], ['48', '49'])).
% 1.96/2.19  thf('51', plain,
% 1.96/2.19      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A_1) @ 
% 1.96/2.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))
% 1.96/2.19        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1)))),
% 1.96/2.19      inference('sup-', [status(thm)], ['38', '50'])).
% 1.96/2.19  thf(t29_relset_1, axiom,
% 1.96/2.19    (![A:$i]:
% 1.96/2.19     ( m1_subset_1 @
% 1.96/2.19       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.96/2.19  thf('52', plain,
% 1.96/2.19      (![X18 : $i]:
% 1.96/2.19         (m1_subset_1 @ (k6_relat_1 @ X18) @ 
% 1.96/2.19          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 1.96/2.19      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.96/2.19  thf(redefinition_k6_partfun1, axiom,
% 1.96/2.19    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.96/2.19  thf('53', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 1.96/2.19      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.96/2.19  thf('54', plain,
% 1.96/2.19      (![X18 : $i]:
% 1.96/2.19         (m1_subset_1 @ (k6_partfun1 @ X18) @ 
% 1.96/2.19          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 1.96/2.19      inference('demod', [status(thm)], ['52', '53'])).
% 1.96/2.19  thf('55', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1))),
% 1.96/2.19      inference('demod', [status(thm)], ['51', '54'])).
% 1.96/2.19  thf('56', plain,
% 1.96/2.19      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 1.96/2.19         = (k6_partfun1 @ sk_A_1))),
% 1.96/2.19      inference('demod', [status(thm)], ['37', '55'])).
% 1.96/2.19  thf('57', plain,
% 1.96/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf(t30_funct_2, axiom,
% 1.96/2.19    (![A:$i,B:$i,C:$i,D:$i]:
% 1.96/2.19     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.96/2.19         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.96/2.19       ( ![E:$i]:
% 1.96/2.19         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.96/2.19             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.96/2.19           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.96/2.19               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.96/2.19             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.96/2.19               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.96/2.19  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.96/2.19  thf(zf_stmt_2, axiom,
% 1.96/2.19    (![C:$i,B:$i]:
% 1.96/2.19     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.96/2.19       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.96/2.19  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.96/2.19  thf(zf_stmt_4, axiom,
% 1.96/2.19    (![E:$i,D:$i]:
% 1.96/2.19     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.96/2.19  thf(zf_stmt_5, axiom,
% 1.96/2.19    (![A:$i,B:$i,C:$i,D:$i]:
% 1.96/2.19     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.96/2.19         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.96/2.19       ( ![E:$i]:
% 1.96/2.19         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.96/2.19             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.96/2.19           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.96/2.19               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.96/2.19             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.96/2.19  thf('58', plain,
% 1.96/2.19      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.96/2.19         (~ (v1_funct_1 @ X40)
% 1.96/2.19          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 1.96/2.19          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.96/2.19          | (zip_tseitin_0 @ X40 @ X43)
% 1.96/2.19          | ~ (v2_funct_1 @ (k1_partfun1 @ X44 @ X41 @ X41 @ X42 @ X43 @ X40))
% 1.96/2.19          | (zip_tseitin_1 @ X42 @ X41)
% 1.96/2.19          | ((k2_relset_1 @ X44 @ X41 @ X43) != (X41))
% 1.96/2.19          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X41)))
% 1.96/2.19          | ~ (v1_funct_2 @ X43 @ X44 @ X41)
% 1.96/2.19          | ~ (v1_funct_1 @ X43))),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.96/2.19  thf('59', plain,
% 1.96/2.19      (![X0 : $i, X1 : $i]:
% 1.96/2.19         (~ (v1_funct_1 @ X0)
% 1.96/2.19          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.96/2.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.96/2.19          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.96/2.19          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 1.96/2.19          | ~ (v2_funct_1 @ 
% 1.96/2.19               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 1.96/2.19          | (zip_tseitin_0 @ sk_D @ X0)
% 1.96/2.19          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 1.96/2.19          | ~ (v1_funct_1 @ sk_D))),
% 1.96/2.19      inference('sup-', [status(thm)], ['57', '58'])).
% 1.96/2.19  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('62', plain,
% 1.96/2.19      (![X0 : $i, X1 : $i]:
% 1.96/2.19         (~ (v1_funct_1 @ X0)
% 1.96/2.19          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.96/2.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.96/2.19          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.96/2.19          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 1.96/2.19          | ~ (v2_funct_1 @ 
% 1.96/2.19               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 1.96/2.19          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.96/2.19      inference('demod', [status(thm)], ['59', '60', '61'])).
% 1.96/2.19  thf('63', plain,
% 1.96/2.19      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A_1))
% 1.96/2.19        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.96/2.19        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 1.96/2.19        | ((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 1.96/2.19        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 1.96/2.19        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 1.96/2.19        | ~ (v1_funct_1 @ sk_C))),
% 1.96/2.19      inference('sup-', [status(thm)], ['56', '62'])).
% 1.96/2.19  thf(fc4_funct_1, axiom,
% 1.96/2.19    (![A:$i]:
% 1.96/2.19     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.96/2.19       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.96/2.19  thf('64', plain, (![X4 : $i]: (v2_funct_1 @ (k6_relat_1 @ X4))),
% 1.96/2.19      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.96/2.19  thf('65', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 1.96/2.19      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.96/2.19  thf('66', plain, (![X4 : $i]: (v2_funct_1 @ (k6_partfun1 @ X4))),
% 1.96/2.19      inference('demod', [status(thm)], ['64', '65'])).
% 1.96/2.19  thf('67', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('68', plain,
% 1.96/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('69', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('71', plain,
% 1.96/2.19      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.96/2.19        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 1.96/2.19        | ((sk_B) != (sk_B)))),
% 1.96/2.19      inference('demod', [status(thm)], ['63', '66', '67', '68', '69', '70'])).
% 1.96/2.19  thf('72', plain,
% 1.96/2.19      (((zip_tseitin_1 @ sk_A_1 @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.96/2.19      inference('simplify', [status(thm)], ['71'])).
% 1.96/2.19  thf('73', plain,
% 1.96/2.19      (![X38 : $i, X39 : $i]:
% 1.96/2.19         (((X38) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X38 @ X39))),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.96/2.19  thf('74', plain,
% 1.96/2.19      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A_1) = (k1_xboole_0)))),
% 1.96/2.19      inference('sup-', [status(thm)], ['72', '73'])).
% 1.96/2.19  thf('75', plain, (((sk_A_1) != (k1_xboole_0))),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('76', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.96/2.19      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 1.96/2.19  thf('77', plain,
% 1.96/2.19      (![X36 : $i, X37 : $i]:
% 1.96/2.19         ((v2_funct_1 @ X37) | ~ (zip_tseitin_0 @ X37 @ X36))),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.96/2.19  thf('78', plain, ((v2_funct_1 @ sk_D)),
% 1.96/2.19      inference('sup-', [status(thm)], ['76', '77'])).
% 1.96/2.19  thf('79', plain,
% 1.96/2.19      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.96/2.19      inference('demod', [status(thm)], ['36', '78'])).
% 1.96/2.19  thf('80', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1))),
% 1.96/2.19      inference('demod', [status(thm)], ['51', '54'])).
% 1.96/2.19  thf(t64_funct_1, axiom,
% 1.96/2.19    (![A:$i]:
% 1.96/2.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.96/2.19       ( ![B:$i]:
% 1.96/2.19         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.96/2.19           ( ( ( v2_funct_1 @ A ) & 
% 1.96/2.19               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.96/2.19               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.96/2.19             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.96/2.19  thf('81', plain,
% 1.96/2.19      (![X6 : $i, X7 : $i]:
% 1.96/2.19         (~ (v1_relat_1 @ X6)
% 1.96/2.19          | ~ (v1_funct_1 @ X6)
% 1.96/2.19          | ((X6) = (k2_funct_1 @ X7))
% 1.96/2.19          | ((k5_relat_1 @ X6 @ X7) != (k6_relat_1 @ (k2_relat_1 @ X7)))
% 1.96/2.19          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 1.96/2.19          | ~ (v2_funct_1 @ X7)
% 1.96/2.19          | ~ (v1_funct_1 @ X7)
% 1.96/2.19          | ~ (v1_relat_1 @ X7))),
% 1.96/2.19      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.96/2.19  thf('82', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 1.96/2.19      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.96/2.19  thf('83', plain,
% 1.96/2.19      (![X6 : $i, X7 : $i]:
% 1.96/2.19         (~ (v1_relat_1 @ X6)
% 1.96/2.19          | ~ (v1_funct_1 @ X6)
% 1.96/2.19          | ((X6) = (k2_funct_1 @ X7))
% 1.96/2.19          | ((k5_relat_1 @ X6 @ X7) != (k6_partfun1 @ (k2_relat_1 @ X7)))
% 1.96/2.19          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 1.96/2.19          | ~ (v2_funct_1 @ X7)
% 1.96/2.19          | ~ (v1_funct_1 @ X7)
% 1.96/2.19          | ~ (v1_relat_1 @ X7))),
% 1.96/2.19      inference('demod', [status(thm)], ['81', '82'])).
% 1.96/2.19  thf('84', plain,
% 1.96/2.19      ((((k6_partfun1 @ sk_A_1) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.96/2.19        | ~ (v1_relat_1 @ sk_D)
% 1.96/2.19        | ~ (v1_funct_1 @ sk_D)
% 1.96/2.19        | ~ (v2_funct_1 @ sk_D)
% 1.96/2.19        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.96/2.19        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.96/2.19        | ~ (v1_funct_1 @ sk_C)
% 1.96/2.19        | ~ (v1_relat_1 @ sk_C))),
% 1.96/2.19      inference('sup-', [status(thm)], ['80', '83'])).
% 1.96/2.19  thf('85', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 1.96/2.19      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 1.96/2.19  thf('86', plain,
% 1.96/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf(cc1_relset_1, axiom,
% 1.96/2.19    (![A:$i,B:$i,C:$i]:
% 1.96/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.96/2.19       ( v1_relat_1 @ C ) ))).
% 1.96/2.19  thf('87', plain,
% 1.96/2.19      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.96/2.19         ((v1_relat_1 @ X8)
% 1.96/2.19          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.96/2.19      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.96/2.19  thf('88', plain, ((v1_relat_1 @ sk_D)),
% 1.96/2.19      inference('sup-', [status(thm)], ['86', '87'])).
% 1.96/2.19  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('90', plain,
% 1.96/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('91', plain,
% 1.96/2.19      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.96/2.19         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.96/2.19          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.96/2.19      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.96/2.19  thf('92', plain,
% 1.96/2.19      (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.96/2.19      inference('sup-', [status(thm)], ['90', '91'])).
% 1.96/2.19  thf('93', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('94', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.96/2.19      inference('sup+', [status(thm)], ['92', '93'])).
% 1.96/2.19  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('96', plain,
% 1.96/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('97', plain,
% 1.96/2.19      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.96/2.19         ((v1_relat_1 @ X8)
% 1.96/2.19          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.96/2.19      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.96/2.19  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 1.96/2.19      inference('sup-', [status(thm)], ['96', '97'])).
% 1.96/2.19  thf('99', plain,
% 1.96/2.19      ((((k6_partfun1 @ sk_A_1) != (k6_partfun1 @ sk_A_1))
% 1.96/2.19        | ~ (v2_funct_1 @ sk_D)
% 1.96/2.19        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.96/2.19        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.96/2.19      inference('demod', [status(thm)],
% 1.96/2.19                ['84', '85', '88', '89', '94', '95', '98'])).
% 1.96/2.19  thf('100', plain,
% 1.96/2.19      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.96/2.19        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.96/2.19        | ~ (v2_funct_1 @ sk_D))),
% 1.96/2.19      inference('simplify', [status(thm)], ['99'])).
% 1.96/2.19  thf('101', plain, ((v2_funct_1 @ sk_D)),
% 1.96/2.19      inference('sup-', [status(thm)], ['76', '77'])).
% 1.96/2.19  thf('102', plain,
% 1.96/2.19      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 1.96/2.19      inference('demod', [status(thm)], ['100', '101'])).
% 1.96/2.19  thf('103', plain,
% 1.96/2.19      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.96/2.19      inference('demod', [status(thm)], ['36', '78'])).
% 1.96/2.19  thf(t58_funct_1, axiom,
% 1.96/2.19    (![A:$i]:
% 1.96/2.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.96/2.19       ( ( v2_funct_1 @ A ) =>
% 1.96/2.19         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.96/2.19             ( k1_relat_1 @ A ) ) & 
% 1.96/2.19           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.96/2.19             ( k1_relat_1 @ A ) ) ) ) ))).
% 1.96/2.19  thf('104', plain,
% 1.96/2.19      (![X5 : $i]:
% 1.96/2.19         (~ (v2_funct_1 @ X5)
% 1.96/2.19          | ((k2_relat_1 @ (k5_relat_1 @ X5 @ (k2_funct_1 @ X5)))
% 1.96/2.19              = (k1_relat_1 @ X5))
% 1.96/2.19          | ~ (v1_funct_1 @ X5)
% 1.96/2.19          | ~ (v1_relat_1 @ X5))),
% 1.96/2.19      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.96/2.19  thf('105', plain,
% 1.96/2.19      ((((k2_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 1.96/2.19        | ~ (v1_relat_1 @ sk_D)
% 1.96/2.19        | ~ (v1_funct_1 @ sk_D)
% 1.96/2.19        | ~ (v2_funct_1 @ sk_D))),
% 1.96/2.19      inference('sup+', [status(thm)], ['103', '104'])).
% 1.96/2.19  thf(t71_relat_1, axiom,
% 1.96/2.19    (![A:$i]:
% 1.96/2.19     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.96/2.19       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.96/2.19  thf('106', plain, (![X2 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X2)) = (X2))),
% 1.96/2.19      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.96/2.19  thf('107', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 1.96/2.19      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.96/2.19  thf('108', plain, (![X2 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X2)) = (X2))),
% 1.96/2.19      inference('demod', [status(thm)], ['106', '107'])).
% 1.96/2.19  thf('109', plain, ((v1_relat_1 @ sk_D)),
% 1.96/2.19      inference('sup-', [status(thm)], ['86', '87'])).
% 1.96/2.19  thf('110', plain, ((v1_funct_1 @ sk_D)),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('111', plain, ((v2_funct_1 @ sk_D)),
% 1.96/2.19      inference('sup-', [status(thm)], ['76', '77'])).
% 1.96/2.19  thf('112', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.96/2.19      inference('demod', [status(thm)], ['105', '108', '109', '110', '111'])).
% 1.96/2.19  thf('113', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 1.96/2.19      inference('demod', [status(thm)], ['102', '112'])).
% 1.96/2.19  thf('114', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.96/2.19      inference('simplify', [status(thm)], ['113'])).
% 1.96/2.19  thf('115', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.96/2.19      inference('demod', [status(thm)], ['79', '114'])).
% 1.96/2.19  thf('116', plain,
% 1.96/2.19      (![X6 : $i, X7 : $i]:
% 1.96/2.19         (~ (v1_relat_1 @ X6)
% 1.96/2.19          | ~ (v1_funct_1 @ X6)
% 1.96/2.19          | ((X6) = (k2_funct_1 @ X7))
% 1.96/2.19          | ((k5_relat_1 @ X6 @ X7) != (k6_partfun1 @ (k2_relat_1 @ X7)))
% 1.96/2.19          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 1.96/2.19          | ~ (v2_funct_1 @ X7)
% 1.96/2.19          | ~ (v1_funct_1 @ X7)
% 1.96/2.19          | ~ (v1_relat_1 @ X7))),
% 1.96/2.19      inference('demod', [status(thm)], ['81', '82'])).
% 1.96/2.19  thf('117', plain,
% 1.96/2.19      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.96/2.19        | ~ (v1_relat_1 @ sk_C)
% 1.96/2.19        | ~ (v1_funct_1 @ sk_C)
% 1.96/2.19        | ~ (v2_funct_1 @ sk_C)
% 1.96/2.19        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 1.96/2.19        | ((sk_D) = (k2_funct_1 @ sk_C))
% 1.96/2.19        | ~ (v1_funct_1 @ sk_D)
% 1.96/2.19        | ~ (v1_relat_1 @ sk_D))),
% 1.96/2.19      inference('sup-', [status(thm)], ['115', '116'])).
% 1.96/2.19  thf('118', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.96/2.19      inference('sup+', [status(thm)], ['92', '93'])).
% 1.96/2.19  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 1.96/2.19      inference('sup-', [status(thm)], ['96', '97'])).
% 1.96/2.19  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('122', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 1.96/2.19      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 1.96/2.19  thf('123', plain,
% 1.96/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('124', plain,
% 1.96/2.19      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.96/2.19         (((X45) = (k1_xboole_0))
% 1.96/2.19          | ~ (v1_funct_1 @ X46)
% 1.96/2.19          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 1.96/2.19          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 1.96/2.19          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_partfun1 @ X47))
% 1.96/2.19          | ~ (v2_funct_1 @ X46)
% 1.96/2.19          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 1.96/2.19      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.96/2.19  thf('125', plain,
% 1.96/2.19      ((((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 1.96/2.19        | ~ (v2_funct_1 @ sk_C)
% 1.96/2.19        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))
% 1.96/2.19        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 1.96/2.19        | ~ (v1_funct_1 @ sk_C)
% 1.96/2.19        | ((sk_B) = (k1_xboole_0)))),
% 1.96/2.19      inference('sup-', [status(thm)], ['123', '124'])).
% 1.96/2.19  thf('126', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('127', plain, ((v2_funct_1 @ sk_C)),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('128', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('130', plain,
% 1.96/2.19      ((((sk_B) != (sk_B))
% 1.96/2.19        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))
% 1.96/2.19        | ((sk_B) = (k1_xboole_0)))),
% 1.96/2.19      inference('demod', [status(thm)], ['125', '126', '127', '128', '129'])).
% 1.96/2.19  thf('131', plain,
% 1.96/2.19      ((((sk_B) = (k1_xboole_0))
% 1.96/2.19        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1)))),
% 1.96/2.19      inference('simplify', [status(thm)], ['130'])).
% 1.96/2.19  thf('132', plain, (((sk_B) != (k1_xboole_0))),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('133', plain,
% 1.96/2.19      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))),
% 1.96/2.19      inference('simplify_reflect-', [status(thm)], ['131', '132'])).
% 1.96/2.19  thf('134', plain,
% 1.96/2.19      (![X5 : $i]:
% 1.96/2.19         (~ (v2_funct_1 @ X5)
% 1.96/2.19          | ((k2_relat_1 @ (k5_relat_1 @ X5 @ (k2_funct_1 @ X5)))
% 1.96/2.19              = (k1_relat_1 @ X5))
% 1.96/2.19          | ~ (v1_funct_1 @ X5)
% 1.96/2.19          | ~ (v1_relat_1 @ X5))),
% 1.96/2.19      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.96/2.19  thf('135', plain,
% 1.96/2.19      ((((k2_relat_1 @ (k6_partfun1 @ sk_A_1)) = (k1_relat_1 @ sk_C))
% 1.96/2.19        | ~ (v1_relat_1 @ sk_C)
% 1.96/2.19        | ~ (v1_funct_1 @ sk_C)
% 1.96/2.19        | ~ (v2_funct_1 @ sk_C))),
% 1.96/2.19      inference('sup+', [status(thm)], ['133', '134'])).
% 1.96/2.19  thf('136', plain, (![X2 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X2)) = (X2))),
% 1.96/2.19      inference('demod', [status(thm)], ['106', '107'])).
% 1.96/2.19  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 1.96/2.19      inference('sup-', [status(thm)], ['96', '97'])).
% 1.96/2.19  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('139', plain, ((v2_funct_1 @ sk_C)),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('140', plain, (((sk_A_1) = (k1_relat_1 @ sk_C))),
% 1.96/2.19      inference('demod', [status(thm)], ['135', '136', '137', '138', '139'])).
% 1.96/2.19  thf('141', plain, ((v1_funct_1 @ sk_D)),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('142', plain, ((v1_relat_1 @ sk_D)),
% 1.96/2.19      inference('sup-', [status(thm)], ['86', '87'])).
% 1.96/2.19  thf('143', plain,
% 1.96/2.19      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 1.96/2.19        | ((sk_A_1) != (sk_A_1))
% 1.96/2.19        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.96/2.19      inference('demod', [status(thm)],
% 1.96/2.19                ['117', '118', '119', '120', '121', '122', '140', '141', '142'])).
% 1.96/2.19  thf('144', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.96/2.19      inference('simplify', [status(thm)], ['143'])).
% 1.96/2.19  thf('145', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.96/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.19  thf('146', plain, ($false),
% 1.96/2.19      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 1.96/2.19  
% 1.96/2.19  % SZS output end Refutation
% 1.96/2.19  
% 1.96/2.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
