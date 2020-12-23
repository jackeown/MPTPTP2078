%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4Q406HEgFa

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:55 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  261 (2016 expanded)
%              Number of leaves         :   51 ( 621 expanded)
%              Depth                    :   30
%              Number of atoms          : 2351 (50114 expanded)
%              Number of equality atoms :  169 (3290 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( X59 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_funct_2 @ X60 @ X61 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X59 ) ) )
      | ( ( k5_relat_1 @ X60 @ ( k2_funct_1 @ X60 ) )
        = ( k6_partfun1 @ X61 ) )
      | ~ ( v2_funct_1 @ X60 )
      | ( ( k2_relset_1 @ X61 @ X59 @ X60 )
       != X59 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
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

thf('19',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('29',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( X25 = X28 )
      | ~ ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('32',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('33',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('34',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18','35'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('41',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('42',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('43',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('50',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18','35'])).

thf('54',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('55',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','43','52','53','54','55','58'])).

thf('60',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','59'])).

thf('61',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('63',plain,(
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

thf('64',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ( zip_tseitin_0 @ X51 @ X54 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X55 @ X52 @ X52 @ X53 @ X54 @ X51 ) )
      | ( zip_tseitin_1 @ X53 @ X52 )
      | ( ( k2_relset_1 @ X55 @ X52 @ X54 )
       != X52 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X54 @ X55 @ X52 )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('65',plain,(
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
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('70',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('71',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('72',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['69','72','73','74','75','76'])).

thf('78',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('80',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X47: $i,X48: $i] :
      ( ( v2_funct_1 @ X48 )
      | ~ ( zip_tseitin_0 @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('84',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['61','84'])).

thf('86',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18','35'])).

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

thf('87',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k2_funct_1 @ X15 ) )
      | ( ( k5_relat_1 @ X14 @ X15 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X15 ) ) )
      | ( ( k2_relat_1 @ X14 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('88',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('89',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k2_funct_1 @ X15 ) )
      | ( ( k5_relat_1 @ X14 @ X15 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X15 ) ) )
      | ( ( k2_relat_1 @ X14 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
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
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('92',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('95',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('100',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['90','91','92','97','98','99'])).

thf('101',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','43','52','53','54','55','58'])).

thf('102',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18','35'])).

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

thf('105',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('106',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('108',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('109',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['95','96'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('113',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['106','107','108','109','110','111','112'])).

thf('114',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['103','113'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('115',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('116',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('117',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( v2_funct_1 @ X56 )
      | ( ( k2_relset_1 @ X58 @ X57 @ X56 )
       != X57 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X56 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X57 ) ) )
      | ~ ( v1_funct_2 @ X56 @ X58 @ X57 )
      | ~ ( v1_funct_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('118',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('122',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['118','119','120','121'])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','43','52','53','54','55','58'])).

thf('124',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['82','83'])).

thf('127',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('129',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('131',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('133',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('134',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) @ sk_B ),
    inference(demod,[status(thm)],['131','134'])).

thf('136',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('137',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ( sk_B
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['61','84'])).

thf('139',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('140',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('142',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('143',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('144',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['137','144'])).

thf('146',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['115','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('148',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['82','83'])).

thf('150',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,
    ( ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['114','150'])).

thf('152',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['85','152'])).

thf('154',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k2_funct_1 @ X15 ) )
      | ( ( k5_relat_1 @ X14 @ X15 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X15 ) ) )
      | ( ( k2_relat_1 @ X14 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('155',plain,
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
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['95','96'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','43','52','53','54','55','58'])).

thf('161',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('162',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( X59 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_funct_2 @ X60 @ X61 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X59 ) ) )
      | ( ( k5_relat_1 @ X60 @ ( k2_funct_1 @ X60 ) )
        = ( k6_partfun1 @ X61 ) )
      | ~ ( v2_funct_1 @ X60 )
      | ( ( k2_relset_1 @ X61 @ X59 @ X60 )
       != X59 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('164',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['164','165','166','167','168'])).

thf('170',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('174',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('176',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( v2_funct_1 @ X56 )
      | ( ( k2_relset_1 @ X58 @ X57 @ X56 )
       != X57 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X56 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X57 ) ) )
      | ~ ( v1_funct_2 @ X56 @ X58 @ X57 )
      | ~ ( v1_funct_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('178',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['178','179','180','181','182'])).

thf('184',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('186',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('188',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('190',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('191',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['188','191'])).

thf('193',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['170','171'])).

thf('194',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('195',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('196',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('197',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['174','175','192','193','194','195','196'])).

thf('198',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['161','197'])).

thf('199',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('200',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['198','199','200','201'])).

thf('203',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('205',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['155','156','157','158','159','160','202','203','204'])).

thf('206',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['206','207'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4Q406HEgFa
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.19/1.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.19/1.36  % Solved by: fo/fo7.sh
% 1.19/1.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.36  % done 769 iterations in 0.917s
% 1.19/1.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.19/1.36  % SZS output start Refutation
% 1.19/1.36  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.19/1.36  thf(sk_B_type, type, sk_B: $i).
% 1.19/1.36  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.19/1.36  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.19/1.36  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.19/1.36  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.19/1.36  thf(sk_C_type, type, sk_C: $i).
% 1.19/1.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.19/1.36  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.19/1.36  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.19/1.36  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.19/1.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.19/1.36  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.19/1.36  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.19/1.36  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.19/1.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.19/1.36  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.19/1.36  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.19/1.36  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.19/1.36  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.19/1.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.19/1.36  thf(sk_D_type, type, sk_D: $i).
% 1.19/1.36  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.19/1.36  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.19/1.36  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.36  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.19/1.36  thf(t36_funct_2, conjecture,
% 1.19/1.36    (![A:$i,B:$i,C:$i]:
% 1.19/1.36     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.19/1.36         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.19/1.36       ( ![D:$i]:
% 1.19/1.36         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.19/1.36             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.19/1.36           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.19/1.36               ( r2_relset_1 @
% 1.19/1.36                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.19/1.36                 ( k6_partfun1 @ A ) ) & 
% 1.19/1.36               ( v2_funct_1 @ C ) ) =>
% 1.19/1.36             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.19/1.36               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.19/1.36  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.36    (~( ![A:$i,B:$i,C:$i]:
% 1.19/1.36        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.19/1.36            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.19/1.36          ( ![D:$i]:
% 1.19/1.36            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.19/1.36                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.19/1.36              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.19/1.36                  ( r2_relset_1 @
% 1.19/1.36                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.19/1.36                    ( k6_partfun1 @ A ) ) & 
% 1.19/1.36                  ( v2_funct_1 @ C ) ) =>
% 1.19/1.36                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.19/1.36                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.19/1.36    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.19/1.36  thf('0', plain,
% 1.19/1.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf(t35_funct_2, axiom,
% 1.19/1.36    (![A:$i,B:$i,C:$i]:
% 1.19/1.36     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.19/1.36         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.19/1.36       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.19/1.36         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.19/1.36           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.19/1.36             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.19/1.36  thf('1', plain,
% 1.19/1.36      (![X59 : $i, X60 : $i, X61 : $i]:
% 1.19/1.36         (((X59) = (k1_xboole_0))
% 1.19/1.36          | ~ (v1_funct_1 @ X60)
% 1.19/1.36          | ~ (v1_funct_2 @ X60 @ X61 @ X59)
% 1.19/1.36          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X59)))
% 1.19/1.36          | ((k5_relat_1 @ X60 @ (k2_funct_1 @ X60)) = (k6_partfun1 @ X61))
% 1.19/1.36          | ~ (v2_funct_1 @ X60)
% 1.19/1.36          | ((k2_relset_1 @ X61 @ X59 @ X60) != (X59)))),
% 1.19/1.36      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.19/1.36  thf('2', plain,
% 1.19/1.36      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.19/1.36        | ~ (v2_funct_1 @ sk_D)
% 1.19/1.36        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.19/1.36        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.19/1.36        | ~ (v1_funct_1 @ sk_D)
% 1.19/1.36        | ((sk_A) = (k1_xboole_0)))),
% 1.19/1.36      inference('sup-', [status(thm)], ['0', '1'])).
% 1.19/1.36  thf('3', plain,
% 1.19/1.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf(redefinition_k2_relset_1, axiom,
% 1.19/1.36    (![A:$i,B:$i,C:$i]:
% 1.19/1.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.36       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.19/1.36  thf('4', plain,
% 1.19/1.36      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.19/1.36         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 1.19/1.36          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.19/1.36      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.19/1.36  thf('5', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.19/1.36      inference('sup-', [status(thm)], ['3', '4'])).
% 1.19/1.36  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('8', plain,
% 1.19/1.36      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.19/1.36        | ~ (v2_funct_1 @ sk_D)
% 1.19/1.36        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.19/1.36        | ((sk_A) = (k1_xboole_0)))),
% 1.19/1.36      inference('demod', [status(thm)], ['2', '5', '6', '7'])).
% 1.19/1.36  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('10', plain,
% 1.19/1.36      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.19/1.36        | ~ (v2_funct_1 @ sk_D)
% 1.19/1.36        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.19/1.36      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 1.19/1.36  thf('11', plain,
% 1.19/1.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('12', plain,
% 1.19/1.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf(redefinition_k1_partfun1, axiom,
% 1.19/1.36    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.19/1.36     ( ( ( v1_funct_1 @ E ) & 
% 1.19/1.36         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.19/1.36         ( v1_funct_1 @ F ) & 
% 1.19/1.36         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.19/1.36       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.19/1.36  thf('13', plain,
% 1.19/1.36      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.19/1.36         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.19/1.36          | ~ (v1_funct_1 @ X36)
% 1.19/1.36          | ~ (v1_funct_1 @ X39)
% 1.19/1.36          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.19/1.36          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 1.19/1.36              = (k5_relat_1 @ X36 @ X39)))),
% 1.19/1.36      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.19/1.36  thf('14', plain,
% 1.19/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.36         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.19/1.36            = (k5_relat_1 @ sk_C @ X0))
% 1.19/1.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.19/1.36          | ~ (v1_funct_1 @ X0)
% 1.19/1.36          | ~ (v1_funct_1 @ sk_C))),
% 1.19/1.36      inference('sup-', [status(thm)], ['12', '13'])).
% 1.19/1.36  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('16', plain,
% 1.19/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.36         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.19/1.36            = (k5_relat_1 @ sk_C @ X0))
% 1.19/1.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.19/1.36          | ~ (v1_funct_1 @ X0))),
% 1.19/1.36      inference('demod', [status(thm)], ['14', '15'])).
% 1.19/1.36  thf('17', plain,
% 1.19/1.36      ((~ (v1_funct_1 @ sk_D)
% 1.19/1.36        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.19/1.36            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.19/1.36      inference('sup-', [status(thm)], ['11', '16'])).
% 1.19/1.36  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('19', plain,
% 1.19/1.36      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.19/1.36        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.19/1.36        (k6_partfun1 @ sk_A))),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('20', plain,
% 1.19/1.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('21', plain,
% 1.19/1.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf(dt_k1_partfun1, axiom,
% 1.19/1.36    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.19/1.36     ( ( ( v1_funct_1 @ E ) & 
% 1.19/1.36         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.19/1.36         ( v1_funct_1 @ F ) & 
% 1.19/1.36         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.19/1.36       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.19/1.36         ( m1_subset_1 @
% 1.19/1.36           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.19/1.36           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.19/1.36  thf('22', plain,
% 1.19/1.36      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.19/1.36         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.19/1.36          | ~ (v1_funct_1 @ X30)
% 1.19/1.36          | ~ (v1_funct_1 @ X33)
% 1.19/1.36          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.19/1.36          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 1.19/1.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 1.19/1.36      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.19/1.36  thf('23', plain,
% 1.19/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.36         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.19/1.36           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.19/1.36          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.19/1.36          | ~ (v1_funct_1 @ X1)
% 1.19/1.36          | ~ (v1_funct_1 @ sk_C))),
% 1.19/1.36      inference('sup-', [status(thm)], ['21', '22'])).
% 1.19/1.36  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('25', plain,
% 1.19/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.36         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.19/1.36           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.19/1.36          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.19/1.36          | ~ (v1_funct_1 @ X1))),
% 1.19/1.36      inference('demod', [status(thm)], ['23', '24'])).
% 1.19/1.36  thf('26', plain,
% 1.19/1.36      ((~ (v1_funct_1 @ sk_D)
% 1.19/1.36        | (m1_subset_1 @ 
% 1.19/1.36           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.19/1.36           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.19/1.36      inference('sup-', [status(thm)], ['20', '25'])).
% 1.19/1.36  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('28', plain,
% 1.19/1.36      ((m1_subset_1 @ 
% 1.19/1.36        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.19/1.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.19/1.36      inference('demod', [status(thm)], ['26', '27'])).
% 1.19/1.36  thf(redefinition_r2_relset_1, axiom,
% 1.19/1.36    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.36     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.19/1.36         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.19/1.36       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.19/1.36  thf('29', plain,
% 1.19/1.36      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.19/1.36         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.19/1.36          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.19/1.36          | ((X25) = (X28))
% 1.19/1.36          | ~ (r2_relset_1 @ X26 @ X27 @ X25 @ X28))),
% 1.19/1.36      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.19/1.36  thf('30', plain,
% 1.19/1.36      (![X0 : $i]:
% 1.19/1.36         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.19/1.36             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.19/1.36          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.19/1.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.19/1.36      inference('sup-', [status(thm)], ['28', '29'])).
% 1.19/1.36  thf('31', plain,
% 1.19/1.36      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.19/1.36           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.19/1.36        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.19/1.36            = (k6_partfun1 @ sk_A)))),
% 1.19/1.36      inference('sup-', [status(thm)], ['19', '30'])).
% 1.19/1.36  thf(t29_relset_1, axiom,
% 1.19/1.36    (![A:$i]:
% 1.19/1.36     ( m1_subset_1 @
% 1.19/1.36       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.19/1.36  thf('32', plain,
% 1.19/1.36      (![X29 : $i]:
% 1.19/1.36         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 1.19/1.36          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 1.19/1.36      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.19/1.36  thf(redefinition_k6_partfun1, axiom,
% 1.19/1.36    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.19/1.36  thf('33', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.19/1.36      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.19/1.36  thf('34', plain,
% 1.19/1.36      (![X29 : $i]:
% 1.19/1.36         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 1.19/1.36          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 1.19/1.36      inference('demod', [status(thm)], ['32', '33'])).
% 1.19/1.36  thf('35', plain,
% 1.19/1.36      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.19/1.36         = (k6_partfun1 @ sk_A))),
% 1.19/1.36      inference('demod', [status(thm)], ['31', '34'])).
% 1.19/1.36  thf('36', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.19/1.36      inference('demod', [status(thm)], ['17', '18', '35'])).
% 1.19/1.36  thf(t45_relat_1, axiom,
% 1.19/1.36    (![A:$i]:
% 1.19/1.36     ( ( v1_relat_1 @ A ) =>
% 1.19/1.36       ( ![B:$i]:
% 1.19/1.36         ( ( v1_relat_1 @ B ) =>
% 1.19/1.36           ( r1_tarski @
% 1.19/1.36             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 1.19/1.36  thf('37', plain,
% 1.19/1.36      (![X5 : $i, X6 : $i]:
% 1.19/1.36         (~ (v1_relat_1 @ X5)
% 1.19/1.36          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 1.19/1.36             (k2_relat_1 @ X5))
% 1.19/1.36          | ~ (v1_relat_1 @ X6))),
% 1.19/1.36      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.19/1.36  thf(d10_xboole_0, axiom,
% 1.19/1.36    (![A:$i,B:$i]:
% 1.19/1.36     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.19/1.36  thf('38', plain,
% 1.19/1.36      (![X0 : $i, X2 : $i]:
% 1.19/1.36         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.19/1.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.19/1.36  thf('39', plain,
% 1.19/1.36      (![X0 : $i, X1 : $i]:
% 1.19/1.36         (~ (v1_relat_1 @ X1)
% 1.19/1.36          | ~ (v1_relat_1 @ X0)
% 1.19/1.36          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 1.19/1.36               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.19/1.36          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 1.19/1.36      inference('sup-', [status(thm)], ['37', '38'])).
% 1.19/1.36  thf('40', plain,
% 1.19/1.36      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 1.19/1.36           (k2_relat_1 @ (k6_partfun1 @ sk_A)))
% 1.19/1.36        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 1.19/1.36        | ~ (v1_relat_1 @ sk_D)
% 1.19/1.36        | ~ (v1_relat_1 @ sk_C))),
% 1.19/1.36      inference('sup-', [status(thm)], ['36', '39'])).
% 1.19/1.36  thf(t71_relat_1, axiom,
% 1.19/1.36    (![A:$i]:
% 1.19/1.36     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.19/1.36       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.19/1.36  thf('41', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 1.19/1.36      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.19/1.36  thf('42', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.19/1.36      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.19/1.36  thf('43', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 1.19/1.36      inference('demod', [status(thm)], ['41', '42'])).
% 1.19/1.36  thf('44', plain,
% 1.19/1.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf(cc2_relset_1, axiom,
% 1.19/1.36    (![A:$i,B:$i,C:$i]:
% 1.19/1.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.36       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.19/1.36  thf('45', plain,
% 1.19/1.36      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.19/1.36         ((v5_relat_1 @ X19 @ X21)
% 1.19/1.36          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.19/1.36      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.19/1.36  thf('46', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 1.19/1.36      inference('sup-', [status(thm)], ['44', '45'])).
% 1.19/1.36  thf(d19_relat_1, axiom,
% 1.19/1.36    (![A:$i,B:$i]:
% 1.19/1.36     ( ( v1_relat_1 @ B ) =>
% 1.19/1.36       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.19/1.36  thf('47', plain,
% 1.19/1.36      (![X3 : $i, X4 : $i]:
% 1.19/1.36         (~ (v5_relat_1 @ X3 @ X4)
% 1.19/1.36          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 1.19/1.36          | ~ (v1_relat_1 @ X3))),
% 1.19/1.36      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.19/1.36  thf('48', plain,
% 1.19/1.36      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 1.19/1.36      inference('sup-', [status(thm)], ['46', '47'])).
% 1.19/1.36  thf('49', plain,
% 1.19/1.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf(cc1_relset_1, axiom,
% 1.19/1.36    (![A:$i,B:$i,C:$i]:
% 1.19/1.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.36       ( v1_relat_1 @ C ) ))).
% 1.19/1.36  thf('50', plain,
% 1.19/1.36      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.19/1.36         ((v1_relat_1 @ X16)
% 1.19/1.36          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.19/1.36      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.19/1.36  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 1.19/1.36      inference('sup-', [status(thm)], ['49', '50'])).
% 1.19/1.36  thf('52', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 1.19/1.36      inference('demod', [status(thm)], ['48', '51'])).
% 1.19/1.36  thf('53', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.19/1.36      inference('demod', [status(thm)], ['17', '18', '35'])).
% 1.19/1.36  thf('54', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 1.19/1.36      inference('demod', [status(thm)], ['41', '42'])).
% 1.19/1.36  thf('55', plain, ((v1_relat_1 @ sk_D)),
% 1.19/1.36      inference('sup-', [status(thm)], ['49', '50'])).
% 1.19/1.36  thf('56', plain,
% 1.19/1.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('57', plain,
% 1.19/1.36      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.19/1.36         ((v1_relat_1 @ X16)
% 1.19/1.36          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.19/1.36      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.19/1.36  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.36      inference('sup-', [status(thm)], ['56', '57'])).
% 1.19/1.36  thf('59', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.19/1.36      inference('demod', [status(thm)],
% 1.19/1.36                ['40', '43', '52', '53', '54', '55', '58'])).
% 1.19/1.36  thf('60', plain,
% 1.19/1.36      ((((sk_A) != (sk_A))
% 1.19/1.36        | ~ (v2_funct_1 @ sk_D)
% 1.19/1.36        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.19/1.36      inference('demod', [status(thm)], ['10', '59'])).
% 1.19/1.36  thf('61', plain,
% 1.19/1.36      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.19/1.36        | ~ (v2_funct_1 @ sk_D))),
% 1.19/1.36      inference('simplify', [status(thm)], ['60'])).
% 1.19/1.36  thf('62', plain,
% 1.19/1.36      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.19/1.36         = (k6_partfun1 @ sk_A))),
% 1.19/1.36      inference('demod', [status(thm)], ['31', '34'])).
% 1.19/1.36  thf('63', plain,
% 1.19/1.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf(t30_funct_2, axiom,
% 1.19/1.36    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.36     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.19/1.36         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.19/1.36       ( ![E:$i]:
% 1.19/1.36         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.19/1.36             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.19/1.36           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.19/1.36               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.19/1.36             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.19/1.36               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.19/1.36  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.19/1.36  thf(zf_stmt_2, axiom,
% 1.19/1.36    (![C:$i,B:$i]:
% 1.19/1.36     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.19/1.36       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.19/1.36  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.19/1.36  thf(zf_stmt_4, axiom,
% 1.19/1.36    (![E:$i,D:$i]:
% 1.19/1.36     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.19/1.36  thf(zf_stmt_5, axiom,
% 1.19/1.36    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.36     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.19/1.36         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.19/1.36       ( ![E:$i]:
% 1.19/1.36         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.19/1.36             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.19/1.36           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.19/1.36               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.19/1.36             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.19/1.36  thf('64', plain,
% 1.19/1.36      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 1.19/1.36         (~ (v1_funct_1 @ X51)
% 1.19/1.36          | ~ (v1_funct_2 @ X51 @ X52 @ X53)
% 1.19/1.36          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 1.19/1.36          | (zip_tseitin_0 @ X51 @ X54)
% 1.19/1.36          | ~ (v2_funct_1 @ (k1_partfun1 @ X55 @ X52 @ X52 @ X53 @ X54 @ X51))
% 1.19/1.36          | (zip_tseitin_1 @ X53 @ X52)
% 1.19/1.36          | ((k2_relset_1 @ X55 @ X52 @ X54) != (X52))
% 1.19/1.36          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X52)))
% 1.19/1.36          | ~ (v1_funct_2 @ X54 @ X55 @ X52)
% 1.19/1.36          | ~ (v1_funct_1 @ X54))),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.19/1.36  thf('65', plain,
% 1.19/1.36      (![X0 : $i, X1 : $i]:
% 1.19/1.36         (~ (v1_funct_1 @ X0)
% 1.19/1.36          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.19/1.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.19/1.36          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.19/1.36          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.19/1.36          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.19/1.36          | (zip_tseitin_0 @ sk_D @ X0)
% 1.19/1.36          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.19/1.36          | ~ (v1_funct_1 @ sk_D))),
% 1.19/1.36      inference('sup-', [status(thm)], ['63', '64'])).
% 1.19/1.36  thf('66', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('67', plain, ((v1_funct_1 @ sk_D)),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('68', plain,
% 1.19/1.36      (![X0 : $i, X1 : $i]:
% 1.19/1.36         (~ (v1_funct_1 @ X0)
% 1.19/1.36          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.19/1.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.19/1.36          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.19/1.36          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.19/1.36          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.19/1.36          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.19/1.36      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.19/1.36  thf('69', plain,
% 1.19/1.36      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.19/1.36        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.19/1.36        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.19/1.36        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.19/1.36        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.19/1.36        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.19/1.36        | ~ (v1_funct_1 @ sk_C))),
% 1.19/1.36      inference('sup-', [status(thm)], ['62', '68'])).
% 1.19/1.36  thf(fc4_funct_1, axiom,
% 1.19/1.36    (![A:$i]:
% 1.19/1.36     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.19/1.36       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.19/1.36  thf('70', plain, (![X10 : $i]: (v2_funct_1 @ (k6_relat_1 @ X10))),
% 1.19/1.36      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.19/1.36  thf('71', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.19/1.36      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.19/1.36  thf('72', plain, (![X10 : $i]: (v2_funct_1 @ (k6_partfun1 @ X10))),
% 1.19/1.36      inference('demod', [status(thm)], ['70', '71'])).
% 1.19/1.36  thf('73', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('74', plain,
% 1.19/1.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('75', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 1.19/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.36  thf('77', plain,
% 1.19/1.36      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.19/1.36        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.19/1.36        | ((sk_B) != (sk_B)))),
% 1.19/1.37      inference('demod', [status(thm)], ['69', '72', '73', '74', '75', '76'])).
% 1.19/1.37  thf('78', plain,
% 1.19/1.37      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.19/1.37      inference('simplify', [status(thm)], ['77'])).
% 1.19/1.37  thf('79', plain,
% 1.19/1.37      (![X49 : $i, X50 : $i]:
% 1.19/1.37         (((X49) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X49 @ X50))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.19/1.37  thf('80', plain,
% 1.19/1.37      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.19/1.37      inference('sup-', [status(thm)], ['78', '79'])).
% 1.19/1.37  thf('81', plain, (((sk_A) != (k1_xboole_0))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('82', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.19/1.37      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 1.19/1.37  thf('83', plain,
% 1.19/1.37      (![X47 : $i, X48 : $i]:
% 1.19/1.37         ((v2_funct_1 @ X48) | ~ (zip_tseitin_0 @ X48 @ X47))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.19/1.37  thf('84', plain, ((v2_funct_1 @ sk_D)),
% 1.19/1.37      inference('sup-', [status(thm)], ['82', '83'])).
% 1.19/1.37  thf('85', plain,
% 1.19/1.37      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.19/1.37      inference('demod', [status(thm)], ['61', '84'])).
% 1.19/1.37  thf('86', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.19/1.37      inference('demod', [status(thm)], ['17', '18', '35'])).
% 1.19/1.37  thf(t64_funct_1, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.19/1.37       ( ![B:$i]:
% 1.19/1.37         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.19/1.37           ( ( ( v2_funct_1 @ A ) & 
% 1.19/1.37               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.19/1.37               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.19/1.37             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.19/1.37  thf('87', plain,
% 1.19/1.37      (![X14 : $i, X15 : $i]:
% 1.19/1.37         (~ (v1_relat_1 @ X14)
% 1.19/1.37          | ~ (v1_funct_1 @ X14)
% 1.19/1.37          | ((X14) = (k2_funct_1 @ X15))
% 1.19/1.37          | ((k5_relat_1 @ X14 @ X15) != (k6_relat_1 @ (k2_relat_1 @ X15)))
% 1.19/1.37          | ((k2_relat_1 @ X14) != (k1_relat_1 @ X15))
% 1.19/1.37          | ~ (v2_funct_1 @ X15)
% 1.19/1.37          | ~ (v1_funct_1 @ X15)
% 1.19/1.37          | ~ (v1_relat_1 @ X15))),
% 1.19/1.37      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.19/1.37  thf('88', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.19/1.37      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.19/1.37  thf('89', plain,
% 1.19/1.37      (![X14 : $i, X15 : $i]:
% 1.19/1.37         (~ (v1_relat_1 @ X14)
% 1.19/1.37          | ~ (v1_funct_1 @ X14)
% 1.19/1.37          | ((X14) = (k2_funct_1 @ X15))
% 1.19/1.37          | ((k5_relat_1 @ X14 @ X15) != (k6_partfun1 @ (k2_relat_1 @ X15)))
% 1.19/1.37          | ((k2_relat_1 @ X14) != (k1_relat_1 @ X15))
% 1.19/1.37          | ~ (v2_funct_1 @ X15)
% 1.19/1.37          | ~ (v1_funct_1 @ X15)
% 1.19/1.37          | ~ (v1_relat_1 @ X15))),
% 1.19/1.37      inference('demod', [status(thm)], ['87', '88'])).
% 1.19/1.37  thf('90', plain,
% 1.19/1.37      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.19/1.37        | ~ (v1_relat_1 @ sk_D)
% 1.19/1.37        | ~ (v1_funct_1 @ sk_D)
% 1.19/1.37        | ~ (v2_funct_1 @ sk_D)
% 1.19/1.37        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.19/1.37        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.19/1.37        | ~ (v1_funct_1 @ sk_C)
% 1.19/1.37        | ~ (v1_relat_1 @ sk_C))),
% 1.19/1.37      inference('sup-', [status(thm)], ['86', '89'])).
% 1.19/1.37  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 1.19/1.37      inference('sup-', [status(thm)], ['49', '50'])).
% 1.19/1.37  thf('92', plain, ((v1_funct_1 @ sk_D)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('93', plain,
% 1.19/1.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('94', plain,
% 1.19/1.37      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.19/1.37         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 1.19/1.37          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.19/1.37      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.19/1.37  thf('95', plain,
% 1.19/1.37      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.19/1.37      inference('sup-', [status(thm)], ['93', '94'])).
% 1.19/1.37  thf('96', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('97', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.19/1.37      inference('sup+', [status(thm)], ['95', '96'])).
% 1.19/1.37  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['56', '57'])).
% 1.19/1.37  thf('100', plain,
% 1.19/1.37      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.19/1.37        | ~ (v2_funct_1 @ sk_D)
% 1.19/1.37        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.19/1.37        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.19/1.37      inference('demod', [status(thm)], ['90', '91', '92', '97', '98', '99'])).
% 1.19/1.37  thf('101', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.19/1.37      inference('demod', [status(thm)],
% 1.19/1.37                ['40', '43', '52', '53', '54', '55', '58'])).
% 1.19/1.37  thf('102', plain,
% 1.19/1.37      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 1.19/1.37        | ~ (v2_funct_1 @ sk_D)
% 1.19/1.37        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.19/1.37        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.19/1.37      inference('demod', [status(thm)], ['100', '101'])).
% 1.19/1.37  thf('103', plain,
% 1.19/1.37      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.19/1.37        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.19/1.37        | ~ (v2_funct_1 @ sk_D))),
% 1.19/1.37      inference('simplify', [status(thm)], ['102'])).
% 1.19/1.37  thf('104', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.19/1.37      inference('demod', [status(thm)], ['17', '18', '35'])).
% 1.19/1.37  thf(t48_funct_1, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.19/1.37       ( ![B:$i]:
% 1.19/1.37         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.19/1.37           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.19/1.37               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.19/1.37             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.19/1.37  thf('105', plain,
% 1.19/1.37      (![X11 : $i, X12 : $i]:
% 1.19/1.37         (~ (v1_relat_1 @ X11)
% 1.19/1.37          | ~ (v1_funct_1 @ X11)
% 1.19/1.37          | (v2_funct_1 @ X12)
% 1.19/1.37          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X12))
% 1.19/1.37          | ~ (v2_funct_1 @ (k5_relat_1 @ X11 @ X12))
% 1.19/1.37          | ~ (v1_funct_1 @ X12)
% 1.19/1.37          | ~ (v1_relat_1 @ X12))),
% 1.19/1.37      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.19/1.37  thf('106', plain,
% 1.19/1.37      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.19/1.37        | ~ (v1_relat_1 @ sk_D)
% 1.19/1.37        | ~ (v1_funct_1 @ sk_D)
% 1.19/1.37        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.19/1.37        | (v2_funct_1 @ sk_D)
% 1.19/1.37        | ~ (v1_funct_1 @ sk_C)
% 1.19/1.37        | ~ (v1_relat_1 @ sk_C))),
% 1.19/1.37      inference('sup-', [status(thm)], ['104', '105'])).
% 1.19/1.37  thf('107', plain, (![X10 : $i]: (v2_funct_1 @ (k6_partfun1 @ X10))),
% 1.19/1.37      inference('demod', [status(thm)], ['70', '71'])).
% 1.19/1.37  thf('108', plain, ((v1_relat_1 @ sk_D)),
% 1.19/1.37      inference('sup-', [status(thm)], ['49', '50'])).
% 1.19/1.37  thf('109', plain, ((v1_funct_1 @ sk_D)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('110', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.19/1.37      inference('sup+', [status(thm)], ['95', '96'])).
% 1.19/1.37  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['56', '57'])).
% 1.19/1.37  thf('113', plain, ((((sk_B) != (k1_relat_1 @ sk_D)) | (v2_funct_1 @ sk_D))),
% 1.19/1.37      inference('demod', [status(thm)],
% 1.19/1.37                ['106', '107', '108', '109', '110', '111', '112'])).
% 1.19/1.37  thf('114', plain,
% 1.19/1.37      ((((sk_B) != (k1_relat_1 @ sk_D)) | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.19/1.37      inference('clc', [status(thm)], ['103', '113'])).
% 1.19/1.37  thf(t55_funct_1, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.19/1.37       ( ( v2_funct_1 @ A ) =>
% 1.19/1.37         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.19/1.37           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.19/1.37  thf('115', plain,
% 1.19/1.37      (![X13 : $i]:
% 1.19/1.37         (~ (v2_funct_1 @ X13)
% 1.19/1.37          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 1.19/1.37          | ~ (v1_funct_1 @ X13)
% 1.19/1.37          | ~ (v1_relat_1 @ X13))),
% 1.19/1.37      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.19/1.37  thf('116', plain,
% 1.19/1.37      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf(t31_funct_2, axiom,
% 1.19/1.37    (![A:$i,B:$i,C:$i]:
% 1.19/1.37     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.19/1.37         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.19/1.37       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.19/1.37         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.19/1.37           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.19/1.37           ( m1_subset_1 @
% 1.19/1.37             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.19/1.37  thf('117', plain,
% 1.19/1.37      (![X56 : $i, X57 : $i, X58 : $i]:
% 1.19/1.37         (~ (v2_funct_1 @ X56)
% 1.19/1.37          | ((k2_relset_1 @ X58 @ X57 @ X56) != (X57))
% 1.19/1.37          | (m1_subset_1 @ (k2_funct_1 @ X56) @ 
% 1.19/1.37             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 1.19/1.37          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X57)))
% 1.19/1.37          | ~ (v1_funct_2 @ X56 @ X58 @ X57)
% 1.19/1.37          | ~ (v1_funct_1 @ X56))),
% 1.19/1.37      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.19/1.37  thf('118', plain,
% 1.19/1.37      ((~ (v1_funct_1 @ sk_D)
% 1.19/1.37        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.19/1.37        | (m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 1.19/1.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.19/1.37        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.19/1.37        | ~ (v2_funct_1 @ sk_D))),
% 1.19/1.37      inference('sup-', [status(thm)], ['116', '117'])).
% 1.19/1.37  thf('119', plain, ((v1_funct_1 @ sk_D)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('120', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('121', plain,
% 1.19/1.37      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.19/1.37      inference('sup-', [status(thm)], ['3', '4'])).
% 1.19/1.37  thf('122', plain,
% 1.19/1.37      (((m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 1.19/1.37         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.19/1.37        | ((k2_relat_1 @ sk_D) != (sk_A))
% 1.19/1.37        | ~ (v2_funct_1 @ sk_D))),
% 1.19/1.37      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 1.19/1.37  thf('123', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.19/1.37      inference('demod', [status(thm)],
% 1.19/1.37                ['40', '43', '52', '53', '54', '55', '58'])).
% 1.19/1.37  thf('124', plain,
% 1.19/1.37      (((m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 1.19/1.37         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.19/1.37        | ((sk_A) != (sk_A))
% 1.19/1.37        | ~ (v2_funct_1 @ sk_D))),
% 1.19/1.37      inference('demod', [status(thm)], ['122', '123'])).
% 1.19/1.37  thf('125', plain,
% 1.19/1.37      ((~ (v2_funct_1 @ sk_D)
% 1.19/1.37        | (m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 1.19/1.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 1.19/1.37      inference('simplify', [status(thm)], ['124'])).
% 1.19/1.37  thf('126', plain, ((v2_funct_1 @ sk_D)),
% 1.19/1.37      inference('sup-', [status(thm)], ['82', '83'])).
% 1.19/1.37  thf('127', plain,
% 1.19/1.37      ((m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 1.19/1.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.37      inference('demod', [status(thm)], ['125', '126'])).
% 1.19/1.37  thf('128', plain,
% 1.19/1.37      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.19/1.37         ((v5_relat_1 @ X19 @ X21)
% 1.19/1.37          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.19/1.37      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.19/1.37  thf('129', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_B)),
% 1.19/1.37      inference('sup-', [status(thm)], ['127', '128'])).
% 1.19/1.37  thf('130', plain,
% 1.19/1.37      (![X3 : $i, X4 : $i]:
% 1.19/1.37         (~ (v5_relat_1 @ X3 @ X4)
% 1.19/1.37          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 1.19/1.37          | ~ (v1_relat_1 @ X3))),
% 1.19/1.37      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.19/1.37  thf('131', plain,
% 1.19/1.37      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 1.19/1.37        | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_D)) @ sk_B))),
% 1.19/1.37      inference('sup-', [status(thm)], ['129', '130'])).
% 1.19/1.37  thf('132', plain,
% 1.19/1.37      ((m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 1.19/1.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.37      inference('demod', [status(thm)], ['125', '126'])).
% 1.19/1.37  thf('133', plain,
% 1.19/1.37      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.19/1.37         ((v1_relat_1 @ X16)
% 1.19/1.37          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.19/1.37      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.19/1.37  thf('134', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_D))),
% 1.19/1.37      inference('sup-', [status(thm)], ['132', '133'])).
% 1.19/1.37  thf('135', plain, ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_D)) @ sk_B)),
% 1.19/1.37      inference('demod', [status(thm)], ['131', '134'])).
% 1.19/1.37  thf('136', plain,
% 1.19/1.37      (![X0 : $i, X2 : $i]:
% 1.19/1.37         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.19/1.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.19/1.37  thf('137', plain,
% 1.19/1.37      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_D)))
% 1.19/1.37        | ((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_D))))),
% 1.19/1.37      inference('sup-', [status(thm)], ['135', '136'])).
% 1.19/1.37  thf('138', plain,
% 1.19/1.37      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.19/1.37      inference('demod', [status(thm)], ['61', '84'])).
% 1.19/1.37  thf('139', plain,
% 1.19/1.37      (![X5 : $i, X6 : $i]:
% 1.19/1.37         (~ (v1_relat_1 @ X5)
% 1.19/1.37          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 1.19/1.37             (k2_relat_1 @ X5))
% 1.19/1.37          | ~ (v1_relat_1 @ X6))),
% 1.19/1.37      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.19/1.37  thf('140', plain,
% 1.19/1.37      (((r1_tarski @ (k2_relat_1 @ (k6_partfun1 @ sk_B)) @ 
% 1.19/1.37         (k2_relat_1 @ (k2_funct_1 @ sk_D)))
% 1.19/1.37        | ~ (v1_relat_1 @ sk_D)
% 1.19/1.37        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 1.19/1.37      inference('sup+', [status(thm)], ['138', '139'])).
% 1.19/1.37  thf('141', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 1.19/1.37      inference('demod', [status(thm)], ['41', '42'])).
% 1.19/1.37  thf('142', plain, ((v1_relat_1 @ sk_D)),
% 1.19/1.37      inference('sup-', [status(thm)], ['49', '50'])).
% 1.19/1.37  thf('143', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_D))),
% 1.19/1.37      inference('sup-', [status(thm)], ['132', '133'])).
% 1.19/1.37  thf('144', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_D)))),
% 1.19/1.37      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 1.19/1.37  thf('145', plain, (((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_D)))),
% 1.19/1.37      inference('demod', [status(thm)], ['137', '144'])).
% 1.19/1.37  thf('146', plain,
% 1.19/1.37      ((((sk_B) = (k1_relat_1 @ sk_D))
% 1.19/1.37        | ~ (v1_relat_1 @ sk_D)
% 1.19/1.37        | ~ (v1_funct_1 @ sk_D)
% 1.19/1.37        | ~ (v2_funct_1 @ sk_D))),
% 1.19/1.37      inference('sup+', [status(thm)], ['115', '145'])).
% 1.19/1.37  thf('147', plain, ((v1_relat_1 @ sk_D)),
% 1.19/1.37      inference('sup-', [status(thm)], ['49', '50'])).
% 1.19/1.37  thf('148', plain, ((v1_funct_1 @ sk_D)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('149', plain, ((v2_funct_1 @ sk_D)),
% 1.19/1.37      inference('sup-', [status(thm)], ['82', '83'])).
% 1.19/1.37  thf('150', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.19/1.37      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 1.19/1.37  thf('151', plain, ((((sk_B) != (sk_B)) | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.19/1.37      inference('demod', [status(thm)], ['114', '150'])).
% 1.19/1.37  thf('152', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.19/1.37      inference('simplify', [status(thm)], ['151'])).
% 1.19/1.37  thf('153', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.19/1.37      inference('demod', [status(thm)], ['85', '152'])).
% 1.19/1.37  thf('154', plain,
% 1.19/1.37      (![X14 : $i, X15 : $i]:
% 1.19/1.37         (~ (v1_relat_1 @ X14)
% 1.19/1.37          | ~ (v1_funct_1 @ X14)
% 1.19/1.37          | ((X14) = (k2_funct_1 @ X15))
% 1.19/1.37          | ((k5_relat_1 @ X14 @ X15) != (k6_partfun1 @ (k2_relat_1 @ X15)))
% 1.19/1.37          | ((k2_relat_1 @ X14) != (k1_relat_1 @ X15))
% 1.19/1.37          | ~ (v2_funct_1 @ X15)
% 1.19/1.37          | ~ (v1_funct_1 @ X15)
% 1.19/1.37          | ~ (v1_relat_1 @ X15))),
% 1.19/1.37      inference('demod', [status(thm)], ['87', '88'])).
% 1.19/1.37  thf('155', plain,
% 1.19/1.37      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.19/1.37        | ~ (v1_relat_1 @ sk_C)
% 1.19/1.37        | ~ (v1_funct_1 @ sk_C)
% 1.19/1.37        | ~ (v2_funct_1 @ sk_C)
% 1.19/1.37        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 1.19/1.37        | ((sk_D) = (k2_funct_1 @ sk_C))
% 1.19/1.37        | ~ (v1_funct_1 @ sk_D)
% 1.19/1.37        | ~ (v1_relat_1 @ sk_D))),
% 1.19/1.37      inference('sup-', [status(thm)], ['153', '154'])).
% 1.19/1.37  thf('156', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.19/1.37      inference('sup+', [status(thm)], ['95', '96'])).
% 1.19/1.37  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['56', '57'])).
% 1.19/1.37  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('160', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.19/1.37      inference('demod', [status(thm)],
% 1.19/1.37                ['40', '43', '52', '53', '54', '55', '58'])).
% 1.19/1.37  thf('161', plain,
% 1.19/1.37      (![X13 : $i]:
% 1.19/1.37         (~ (v2_funct_1 @ X13)
% 1.19/1.37          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 1.19/1.37          | ~ (v1_funct_1 @ X13)
% 1.19/1.37          | ~ (v1_relat_1 @ X13))),
% 1.19/1.37      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.19/1.37  thf('162', plain,
% 1.19/1.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('163', plain,
% 1.19/1.37      (![X59 : $i, X60 : $i, X61 : $i]:
% 1.19/1.37         (((X59) = (k1_xboole_0))
% 1.19/1.37          | ~ (v1_funct_1 @ X60)
% 1.19/1.37          | ~ (v1_funct_2 @ X60 @ X61 @ X59)
% 1.19/1.37          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X59)))
% 1.19/1.37          | ((k5_relat_1 @ X60 @ (k2_funct_1 @ X60)) = (k6_partfun1 @ X61))
% 1.19/1.37          | ~ (v2_funct_1 @ X60)
% 1.19/1.37          | ((k2_relset_1 @ X61 @ X59 @ X60) != (X59)))),
% 1.19/1.37      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.19/1.37  thf('164', plain,
% 1.19/1.37      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.19/1.37        | ~ (v2_funct_1 @ sk_C)
% 1.19/1.37        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.19/1.37        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.19/1.37        | ~ (v1_funct_1 @ sk_C)
% 1.19/1.37        | ((sk_B) = (k1_xboole_0)))),
% 1.19/1.37      inference('sup-', [status(thm)], ['162', '163'])).
% 1.19/1.37  thf('165', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('166', plain, ((v2_funct_1 @ sk_C)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('167', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('169', plain,
% 1.19/1.37      ((((sk_B) != (sk_B))
% 1.19/1.37        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.19/1.37        | ((sk_B) = (k1_xboole_0)))),
% 1.19/1.37      inference('demod', [status(thm)], ['164', '165', '166', '167', '168'])).
% 1.19/1.37  thf('170', plain,
% 1.19/1.37      ((((sk_B) = (k1_xboole_0))
% 1.19/1.37        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 1.19/1.37      inference('simplify', [status(thm)], ['169'])).
% 1.19/1.37  thf('171', plain, (((sk_B) != (k1_xboole_0))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('172', plain,
% 1.19/1.37      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.19/1.37      inference('simplify_reflect-', [status(thm)], ['170', '171'])).
% 1.19/1.37  thf('173', plain,
% 1.19/1.37      (![X0 : $i, X1 : $i]:
% 1.19/1.37         (~ (v1_relat_1 @ X1)
% 1.19/1.37          | ~ (v1_relat_1 @ X0)
% 1.19/1.37          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 1.19/1.37               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.19/1.37          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 1.19/1.37      inference('sup-', [status(thm)], ['37', '38'])).
% 1.19/1.37  thf('174', plain,
% 1.19/1.37      ((~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.19/1.37           (k2_relat_1 @ (k6_partfun1 @ sk_A)))
% 1.19/1.37        | ((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 1.19/1.37            = (k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))
% 1.19/1.37        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.19/1.37        | ~ (v1_relat_1 @ sk_C))),
% 1.19/1.37      inference('sup-', [status(thm)], ['172', '173'])).
% 1.19/1.37  thf('175', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 1.19/1.37      inference('demod', [status(thm)], ['41', '42'])).
% 1.19/1.37  thf('176', plain,
% 1.19/1.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('177', plain,
% 1.19/1.37      (![X56 : $i, X57 : $i, X58 : $i]:
% 1.19/1.37         (~ (v2_funct_1 @ X56)
% 1.19/1.37          | ((k2_relset_1 @ X58 @ X57 @ X56) != (X57))
% 1.19/1.37          | (m1_subset_1 @ (k2_funct_1 @ X56) @ 
% 1.19/1.37             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 1.19/1.37          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X57)))
% 1.19/1.37          | ~ (v1_funct_2 @ X56 @ X58 @ X57)
% 1.19/1.37          | ~ (v1_funct_1 @ X56))),
% 1.19/1.37      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.19/1.37  thf('178', plain,
% 1.19/1.37      ((~ (v1_funct_1 @ sk_C)
% 1.19/1.37        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.19/1.37        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.19/1.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.19/1.37        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.19/1.37        | ~ (v2_funct_1 @ sk_C))),
% 1.19/1.37      inference('sup-', [status(thm)], ['176', '177'])).
% 1.19/1.37  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('180', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('181', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('182', plain, ((v2_funct_1 @ sk_C)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('183', plain,
% 1.19/1.37      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.19/1.37         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.19/1.37        | ((sk_B) != (sk_B)))),
% 1.19/1.37      inference('demod', [status(thm)], ['178', '179', '180', '181', '182'])).
% 1.19/1.37  thf('184', plain,
% 1.19/1.37      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.19/1.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.19/1.37      inference('simplify', [status(thm)], ['183'])).
% 1.19/1.37  thf('185', plain,
% 1.19/1.37      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.19/1.37         ((v5_relat_1 @ X19 @ X21)
% 1.19/1.37          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.19/1.37      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.19/1.37  thf('186', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 1.19/1.37      inference('sup-', [status(thm)], ['184', '185'])).
% 1.19/1.37  thf('187', plain,
% 1.19/1.37      (![X3 : $i, X4 : $i]:
% 1.19/1.37         (~ (v5_relat_1 @ X3 @ X4)
% 1.19/1.37          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 1.19/1.37          | ~ (v1_relat_1 @ X3))),
% 1.19/1.37      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.19/1.37  thf('188', plain,
% 1.19/1.37      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.19/1.37        | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 1.19/1.37      inference('sup-', [status(thm)], ['186', '187'])).
% 1.19/1.37  thf('189', plain,
% 1.19/1.37      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.19/1.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.19/1.37      inference('simplify', [status(thm)], ['183'])).
% 1.19/1.37  thf('190', plain,
% 1.19/1.37      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.19/1.37         ((v1_relat_1 @ X16)
% 1.19/1.37          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.19/1.37      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.19/1.37  thf('191', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.19/1.37      inference('sup-', [status(thm)], ['189', '190'])).
% 1.19/1.37  thf('192', plain, ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 1.19/1.37      inference('demod', [status(thm)], ['188', '191'])).
% 1.19/1.37  thf('193', plain,
% 1.19/1.37      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.19/1.37      inference('simplify_reflect-', [status(thm)], ['170', '171'])).
% 1.19/1.37  thf('194', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 1.19/1.37      inference('demod', [status(thm)], ['41', '42'])).
% 1.19/1.37  thf('195', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.19/1.37      inference('sup-', [status(thm)], ['189', '190'])).
% 1.19/1.37  thf('196', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['56', '57'])).
% 1.19/1.37  thf('197', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 1.19/1.37      inference('demod', [status(thm)],
% 1.19/1.37                ['174', '175', '192', '193', '194', '195', '196'])).
% 1.19/1.37  thf('198', plain,
% 1.19/1.37      ((((k1_relat_1 @ sk_C) = (sk_A))
% 1.19/1.37        | ~ (v1_relat_1 @ sk_C)
% 1.19/1.37        | ~ (v1_funct_1 @ sk_C)
% 1.19/1.37        | ~ (v2_funct_1 @ sk_C))),
% 1.19/1.37      inference('sup+', [status(thm)], ['161', '197'])).
% 1.19/1.37  thf('199', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['56', '57'])).
% 1.19/1.37  thf('200', plain, ((v1_funct_1 @ sk_C)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('201', plain, ((v2_funct_1 @ sk_C)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('202', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.19/1.37      inference('demod', [status(thm)], ['198', '199', '200', '201'])).
% 1.19/1.37  thf('203', plain, ((v1_funct_1 @ sk_D)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('204', plain, ((v1_relat_1 @ sk_D)),
% 1.19/1.37      inference('sup-', [status(thm)], ['49', '50'])).
% 1.19/1.37  thf('205', plain,
% 1.19/1.37      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 1.19/1.37        | ((sk_A) != (sk_A))
% 1.19/1.37        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.19/1.37      inference('demod', [status(thm)],
% 1.19/1.37                ['155', '156', '157', '158', '159', '160', '202', '203', '204'])).
% 1.19/1.37  thf('206', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.19/1.37      inference('simplify', [status(thm)], ['205'])).
% 1.19/1.37  thf('207', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('208', plain, ($false),
% 1.19/1.37      inference('simplify_reflect-', [status(thm)], ['206', '207'])).
% 1.19/1.37  
% 1.19/1.37  % SZS output end Refutation
% 1.19/1.37  
% 1.19/1.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
