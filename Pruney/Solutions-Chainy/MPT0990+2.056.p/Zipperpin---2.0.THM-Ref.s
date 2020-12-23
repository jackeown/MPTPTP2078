%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.usA1FnPZvm

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:03 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 363 expanded)
%              Number of leaves         :   42 ( 124 expanded)
%              Depth                    :   14
%              Number of atoms          : 1710 (9443 expanded)
%              Number of equality atoms :  138 ( 695 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( X11 = X14 )
      | ~ ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ( ( k2_relset_1 @ X38 @ X37 @ X36 )
       != X37 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('34',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ( ( k2_relset_1 @ X38 @ X37 @ X36 )
       != X37 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('37',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['42'])).

thf('48',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('50',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X39 ) ) )
      | ( ( k5_relat_1 @ X40 @ ( k2_funct_1 @ X40 ) )
        = ( k6_partfun1 @ X41 ) )
      | ~ ( v2_funct_1 @ X40 )
      | ( ( k2_relset_1 @ X41 @ X39 @ X40 )
       != X39 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('51',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','43','60'])).

thf('62',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','61'])).

thf('63',plain,(
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

thf('64',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('65',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('66',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('67',plain,(
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

thf('68',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('69',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('74',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('75',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['65','72','75'])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('79',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('83',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('89',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','86','89'])).

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

thf('91',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k2_funct_1 @ X4 ) )
      | ( ( k5_relat_1 @ X4 @ X3 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X3 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('92',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('93',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k2_funct_1 @ X4 ) )
      | ( ( k5_relat_1 @ X4 @ X3 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X3 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k2_relat_1 @ sk_C )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('96',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('97',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ sk_A ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','97','98','99'])).

thf('101',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('104',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','104','105'])).

thf('107',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['106','107'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('109',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X2 ) @ X2 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('110',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('111',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X2 ) @ X2 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X39 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X40 ) @ X40 )
        = ( k6_partfun1 @ X39 ) )
      | ~ ( v2_funct_1 @ X40 )
      | ( ( k2_relset_1 @ X41 @ X39 @ X40 )
       != X39 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('114',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['111','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['95','96'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('129',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['127','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('133',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','133'])).

thf('135',plain,(
    ( k5_relat_1 @ sk_C @ sk_D )
 != ( k6_partfun1 @ sk_A ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['62','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.usA1FnPZvm
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:42:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.05/1.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.28  % Solved by: fo/fo7.sh
% 1.05/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.28  % done 346 iterations in 0.839s
% 1.05/1.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.28  % SZS output start Refutation
% 1.05/1.28  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.05/1.28  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.05/1.28  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.05/1.28  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.05/1.28  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.05/1.28  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.05/1.28  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.05/1.28  thf(sk_D_type, type, sk_D: $i).
% 1.05/1.28  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.05/1.28  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.05/1.28  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.05/1.28  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.05/1.28  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.05/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.28  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.05/1.28  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.28  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.05/1.28  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.05/1.28  thf(sk_C_type, type, sk_C: $i).
% 1.05/1.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.28  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.05/1.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.28  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.05/1.28  thf(t36_funct_2, conjecture,
% 1.05/1.28    (![A:$i,B:$i,C:$i]:
% 1.05/1.28     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.28         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.28       ( ![D:$i]:
% 1.05/1.28         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.05/1.28             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.05/1.28           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.05/1.28               ( r2_relset_1 @
% 1.05/1.28                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.05/1.28                 ( k6_partfun1 @ A ) ) & 
% 1.05/1.28               ( v2_funct_1 @ C ) ) =>
% 1.05/1.28             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.05/1.28               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.05/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.28    (~( ![A:$i,B:$i,C:$i]:
% 1.05/1.28        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.28            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.28          ( ![D:$i]:
% 1.05/1.28            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.05/1.28                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.05/1.28              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.05/1.28                  ( r2_relset_1 @
% 1.05/1.28                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.05/1.28                    ( k6_partfun1 @ A ) ) & 
% 1.05/1.28                  ( v2_funct_1 @ C ) ) =>
% 1.05/1.28                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.05/1.28                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.05/1.28    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.05/1.28  thf('0', plain,
% 1.05/1.28      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.05/1.28        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.05/1.28        (k6_partfun1 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('1', plain,
% 1.05/1.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('2', plain,
% 1.05/1.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf(redefinition_k1_partfun1, axiom,
% 1.05/1.28    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.05/1.28     ( ( ( v1_funct_1 @ E ) & 
% 1.05/1.28         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.05/1.28         ( v1_funct_1 @ F ) & 
% 1.05/1.28         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.05/1.28       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.05/1.28  thf('3', plain,
% 1.05/1.28      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.05/1.28         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.05/1.28          | ~ (v1_funct_1 @ X29)
% 1.05/1.28          | ~ (v1_funct_1 @ X32)
% 1.05/1.29          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.05/1.29          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 1.05/1.29              = (k5_relat_1 @ X29 @ X32)))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.05/1.29  thf('4', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.29         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.05/1.29            = (k5_relat_1 @ sk_C @ X0))
% 1.05/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ sk_C))),
% 1.05/1.29      inference('sup-', [status(thm)], ['2', '3'])).
% 1.05/1.29  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('6', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.29         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.05/1.29            = (k5_relat_1 @ sk_C @ X0))
% 1.05/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.05/1.29          | ~ (v1_funct_1 @ X0))),
% 1.05/1.29      inference('demod', [status(thm)], ['4', '5'])).
% 1.05/1.29  thf('7', plain,
% 1.05/1.29      ((~ (v1_funct_1 @ sk_D)
% 1.05/1.29        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.05/1.29            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['1', '6'])).
% 1.05/1.29  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('9', plain,
% 1.05/1.29      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.05/1.29         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.05/1.29      inference('demod', [status(thm)], ['7', '8'])).
% 1.05/1.29  thf('10', plain,
% 1.05/1.29      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.05/1.29        (k6_partfun1 @ sk_A))),
% 1.05/1.29      inference('demod', [status(thm)], ['0', '9'])).
% 1.05/1.29  thf('11', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('12', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(dt_k1_partfun1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.05/1.29     ( ( ( v1_funct_1 @ E ) & 
% 1.05/1.29         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.05/1.29         ( v1_funct_1 @ F ) & 
% 1.05/1.29         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.05/1.29       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.05/1.29         ( m1_subset_1 @
% 1.05/1.29           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.05/1.29           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.05/1.29  thf('13', plain,
% 1.05/1.29      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.05/1.29         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.05/1.29          | ~ (v1_funct_1 @ X23)
% 1.05/1.29          | ~ (v1_funct_1 @ X26)
% 1.05/1.29          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.05/1.29          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 1.05/1.29             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 1.05/1.29      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.05/1.29  thf('14', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.29         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.05/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.05/1.29          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.05/1.29          | ~ (v1_funct_1 @ X1)
% 1.05/1.29          | ~ (v1_funct_1 @ sk_C))),
% 1.05/1.29      inference('sup-', [status(thm)], ['12', '13'])).
% 1.05/1.29  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('16', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.29         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.05/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.05/1.29          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.05/1.29          | ~ (v1_funct_1 @ X1))),
% 1.05/1.29      inference('demod', [status(thm)], ['14', '15'])).
% 1.05/1.29  thf('17', plain,
% 1.05/1.29      ((~ (v1_funct_1 @ sk_D)
% 1.05/1.29        | (m1_subset_1 @ 
% 1.05/1.29           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.05/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.05/1.29      inference('sup-', [status(thm)], ['11', '16'])).
% 1.05/1.29  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('19', plain,
% 1.05/1.29      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.05/1.29         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.05/1.29      inference('demod', [status(thm)], ['7', '8'])).
% 1.05/1.29  thf('20', plain,
% 1.05/1.29      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.05/1.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.05/1.29      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.05/1.29  thf(redefinition_r2_relset_1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.29     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.05/1.29         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.29       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.05/1.29  thf('21', plain,
% 1.05/1.29      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.05/1.29         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.05/1.29          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.05/1.29          | ((X11) = (X14))
% 1.05/1.29          | ~ (r2_relset_1 @ X12 @ X13 @ X11 @ X14))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.05/1.29  thf('22', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.05/1.29          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.05/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.05/1.29      inference('sup-', [status(thm)], ['20', '21'])).
% 1.05/1.29  thf('23', plain,
% 1.05/1.29      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.05/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.05/1.29        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['10', '22'])).
% 1.05/1.29  thf('24', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(t31_funct_2, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.29       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.05/1.29         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.05/1.29           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.05/1.29           ( m1_subset_1 @
% 1.05/1.29             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.05/1.29  thf('25', plain,
% 1.05/1.29      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.05/1.29         (~ (v2_funct_1 @ X36)
% 1.05/1.29          | ((k2_relset_1 @ X38 @ X37 @ X36) != (X37))
% 1.05/1.29          | (m1_subset_1 @ (k2_funct_1 @ X36) @ 
% 1.05/1.29             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.05/1.29          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 1.05/1.29          | ~ (v1_funct_2 @ X36 @ X38 @ X37)
% 1.05/1.29          | ~ (v1_funct_1 @ X36))),
% 1.05/1.29      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.05/1.29  thf('26', plain,
% 1.05/1.29      ((~ (v1_funct_1 @ sk_C)
% 1.05/1.29        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.05/1.29        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.05/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.05/1.29        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.05/1.29        | ~ (v2_funct_1 @ sk_C))),
% 1.05/1.29      inference('sup-', [status(thm)], ['24', '25'])).
% 1.05/1.29  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('28', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('29', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('30', plain, ((v2_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('31', plain,
% 1.05/1.29      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.05/1.29         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.05/1.29        | ((sk_B) != (sk_B)))),
% 1.05/1.29      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 1.05/1.29  thf('32', plain,
% 1.05/1.29      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.05/1.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.29      inference('simplify', [status(thm)], ['31'])).
% 1.05/1.29  thf('33', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.29         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.05/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.05/1.29          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.05/1.29          | ~ (v1_funct_1 @ X1))),
% 1.05/1.29      inference('demod', [status(thm)], ['14', '15'])).
% 1.05/1.29  thf('34', plain,
% 1.05/1.29      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.05/1.29        | (m1_subset_1 @ 
% 1.05/1.29           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 1.05/1.29            (k2_funct_1 @ sk_C)) @ 
% 1.05/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.05/1.29      inference('sup-', [status(thm)], ['32', '33'])).
% 1.05/1.29  thf('35', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('36', plain,
% 1.05/1.29      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.05/1.29         (~ (v2_funct_1 @ X36)
% 1.05/1.29          | ((k2_relset_1 @ X38 @ X37 @ X36) != (X37))
% 1.05/1.29          | (v1_funct_1 @ (k2_funct_1 @ X36))
% 1.05/1.29          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 1.05/1.29          | ~ (v1_funct_2 @ X36 @ X38 @ X37)
% 1.05/1.29          | ~ (v1_funct_1 @ X36))),
% 1.05/1.29      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.05/1.29  thf('37', plain,
% 1.05/1.29      ((~ (v1_funct_1 @ sk_C)
% 1.05/1.29        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.05/1.29        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.05/1.29        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.05/1.29        | ~ (v2_funct_1 @ sk_C))),
% 1.05/1.29      inference('sup-', [status(thm)], ['35', '36'])).
% 1.05/1.29  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('39', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('40', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('41', plain, ((v2_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('42', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 1.05/1.29      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 1.05/1.29  thf('43', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.05/1.29      inference('simplify', [status(thm)], ['42'])).
% 1.05/1.29  thf('44', plain,
% 1.05/1.29      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.05/1.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.29      inference('simplify', [status(thm)], ['31'])).
% 1.05/1.29  thf('45', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.29         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.05/1.29            = (k5_relat_1 @ sk_C @ X0))
% 1.05/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.05/1.29          | ~ (v1_funct_1 @ X0))),
% 1.05/1.29      inference('demod', [status(thm)], ['4', '5'])).
% 1.05/1.29  thf('46', plain,
% 1.05/1.29      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.05/1.29        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 1.05/1.29            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 1.05/1.29      inference('sup-', [status(thm)], ['44', '45'])).
% 1.05/1.29  thf('47', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.05/1.29      inference('simplify', [status(thm)], ['42'])).
% 1.05/1.29  thf('48', plain,
% 1.05/1.29      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 1.05/1.29         = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 1.05/1.29      inference('demod', [status(thm)], ['46', '47'])).
% 1.05/1.29  thf('49', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(t35_funct_2, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.29       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.05/1.29         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.05/1.29           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.05/1.29             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.05/1.29  thf('50', plain,
% 1.05/1.29      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.05/1.29         (((X39) = (k1_xboole_0))
% 1.05/1.29          | ~ (v1_funct_1 @ X40)
% 1.05/1.29          | ~ (v1_funct_2 @ X40 @ X41 @ X39)
% 1.05/1.29          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X39)))
% 1.05/1.29          | ((k5_relat_1 @ X40 @ (k2_funct_1 @ X40)) = (k6_partfun1 @ X41))
% 1.05/1.29          | ~ (v2_funct_1 @ X40)
% 1.05/1.29          | ((k2_relset_1 @ X41 @ X39 @ X40) != (X39)))),
% 1.05/1.29      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.05/1.29  thf('51', plain,
% 1.05/1.29      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.05/1.29        | ~ (v2_funct_1 @ sk_C)
% 1.05/1.29        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.05/1.29        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.05/1.29        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.29        | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['49', '50'])).
% 1.05/1.29  thf('52', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('54', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('56', plain,
% 1.05/1.29      ((((sk_B) != (sk_B))
% 1.05/1.29        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.05/1.29        | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.29      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 1.05/1.29  thf('57', plain,
% 1.05/1.29      ((((sk_B) = (k1_xboole_0))
% 1.05/1.29        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 1.05/1.29      inference('simplify', [status(thm)], ['56'])).
% 1.05/1.29  thf('58', plain, (((sk_B) != (k1_xboole_0))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('59', plain,
% 1.05/1.29      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.05/1.29      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 1.05/1.29  thf('60', plain,
% 1.05/1.29      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 1.05/1.29         = (k6_partfun1 @ sk_A))),
% 1.05/1.29      inference('demod', [status(thm)], ['48', '59'])).
% 1.05/1.29  thf('61', plain,
% 1.05/1.29      ((m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.05/1.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.05/1.29      inference('demod', [status(thm)], ['34', '43', '60'])).
% 1.05/1.29  thf('62', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.05/1.29      inference('demod', [status(thm)], ['23', '61'])).
% 1.05/1.29  thf('63', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(d1_funct_2, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.29       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.05/1.29           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.05/1.29             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.05/1.29         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.05/1.29           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.05/1.29             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.05/1.29  thf(zf_stmt_1, axiom,
% 1.05/1.29    (![C:$i,B:$i,A:$i]:
% 1.05/1.29     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.05/1.29       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.05/1.29  thf('64', plain,
% 1.05/1.29      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.05/1.29         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 1.05/1.29          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 1.05/1.29          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.05/1.29  thf('65', plain,
% 1.05/1.29      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 1.05/1.29        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['63', '64'])).
% 1.05/1.29  thf(zf_stmt_2, axiom,
% 1.05/1.29    (![B:$i,A:$i]:
% 1.05/1.29     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.05/1.29       ( zip_tseitin_0 @ B @ A ) ))).
% 1.05/1.29  thf('66', plain,
% 1.05/1.29      (![X15 : $i, X16 : $i]:
% 1.05/1.29         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.05/1.29  thf('67', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.05/1.29  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.05/1.29  thf(zf_stmt_5, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.29       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.05/1.29         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.05/1.29           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.05/1.29             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.05/1.29  thf('68', plain,
% 1.05/1.29      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.05/1.29         (~ (zip_tseitin_0 @ X20 @ X21)
% 1.05/1.29          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 1.05/1.29          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.05/1.29  thf('69', plain,
% 1.05/1.29      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 1.05/1.29      inference('sup-', [status(thm)], ['67', '68'])).
% 1.05/1.29  thf('70', plain,
% 1.05/1.29      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 1.05/1.29      inference('sup-', [status(thm)], ['66', '69'])).
% 1.05/1.29  thf('71', plain, (((sk_A) != (k1_xboole_0))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('72', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 1.05/1.29      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 1.05/1.29  thf('73', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(redefinition_k1_relset_1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.29       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.05/1.29  thf('74', plain,
% 1.05/1.29      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.05/1.29         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.05/1.29          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.05/1.29  thf('75', plain,
% 1.05/1.29      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.05/1.29      inference('sup-', [status(thm)], ['73', '74'])).
% 1.05/1.29  thf('76', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.05/1.29      inference('demod', [status(thm)], ['65', '72', '75'])).
% 1.05/1.29  thf('77', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('78', plain,
% 1.05/1.29      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.05/1.29         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 1.05/1.29          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 1.05/1.29          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.05/1.29  thf('79', plain,
% 1.05/1.29      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.05/1.29        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['77', '78'])).
% 1.05/1.29  thf('80', plain,
% 1.05/1.29      (![X15 : $i, X16 : $i]:
% 1.05/1.29         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.05/1.29  thf('81', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('82', plain,
% 1.05/1.29      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.05/1.29         (~ (zip_tseitin_0 @ X20 @ X21)
% 1.05/1.29          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 1.05/1.29          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.05/1.29  thf('83', plain,
% 1.05/1.29      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.05/1.29      inference('sup-', [status(thm)], ['81', '82'])).
% 1.05/1.29  thf('84', plain,
% 1.05/1.29      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.05/1.29      inference('sup-', [status(thm)], ['80', '83'])).
% 1.05/1.29  thf('85', plain, (((sk_B) != (k1_xboole_0))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('86', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 1.05/1.29      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 1.05/1.29  thf('87', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('88', plain,
% 1.05/1.29      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.05/1.29         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.05/1.29          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.05/1.29  thf('89', plain,
% 1.05/1.29      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.05/1.29      inference('sup-', [status(thm)], ['87', '88'])).
% 1.05/1.29  thf('90', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.05/1.29      inference('demod', [status(thm)], ['79', '86', '89'])).
% 1.05/1.29  thf(t63_funct_1, axiom,
% 1.05/1.29    (![A:$i]:
% 1.05/1.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.05/1.29       ( ![B:$i]:
% 1.05/1.29         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.05/1.29           ( ( ( v2_funct_1 @ A ) & 
% 1.05/1.29               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.05/1.29               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 1.05/1.29             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.05/1.29  thf('91', plain,
% 1.05/1.29      (![X3 : $i, X4 : $i]:
% 1.05/1.29         (~ (v1_relat_1 @ X3)
% 1.05/1.29          | ~ (v1_funct_1 @ X3)
% 1.05/1.29          | ((X3) = (k2_funct_1 @ X4))
% 1.05/1.29          | ((k5_relat_1 @ X4 @ X3) != (k6_relat_1 @ (k1_relat_1 @ X4)))
% 1.05/1.29          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X3))
% 1.05/1.29          | ~ (v2_funct_1 @ X4)
% 1.05/1.29          | ~ (v1_funct_1 @ X4)
% 1.05/1.29          | ~ (v1_relat_1 @ X4))),
% 1.05/1.29      inference('cnf', [status(esa)], [t63_funct_1])).
% 1.05/1.29  thf(redefinition_k6_partfun1, axiom,
% 1.05/1.29    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.05/1.29  thf('92', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.29  thf('93', plain,
% 1.05/1.29      (![X3 : $i, X4 : $i]:
% 1.05/1.29         (~ (v1_relat_1 @ X3)
% 1.05/1.29          | ~ (v1_funct_1 @ X3)
% 1.05/1.29          | ((X3) = (k2_funct_1 @ X4))
% 1.05/1.29          | ((k5_relat_1 @ X4 @ X3) != (k6_partfun1 @ (k1_relat_1 @ X4)))
% 1.05/1.29          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X3))
% 1.05/1.29          | ~ (v2_funct_1 @ X4)
% 1.05/1.29          | ~ (v1_funct_1 @ X4)
% 1.05/1.29          | ~ (v1_relat_1 @ X4))),
% 1.05/1.29      inference('demod', [status(thm)], ['91', '92'])).
% 1.05/1.29  thf('94', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A))
% 1.05/1.29          | ~ (v1_relat_1 @ sk_C)
% 1.05/1.29          | ~ (v1_funct_1 @ sk_C)
% 1.05/1.29          | ~ (v2_funct_1 @ sk_C)
% 1.05/1.29          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 1.05/1.29          | ((X0) = (k2_funct_1 @ sk_C))
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_relat_1 @ X0))),
% 1.05/1.29      inference('sup-', [status(thm)], ['90', '93'])).
% 1.05/1.29  thf('95', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(cc1_relset_1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.29       ( v1_relat_1 @ C ) ))).
% 1.05/1.29  thf('96', plain,
% 1.05/1.29      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.05/1.29         ((v1_relat_1 @ X5)
% 1.05/1.29          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.05/1.29      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.05/1.29  thf('97', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.29      inference('sup-', [status(thm)], ['95', '96'])).
% 1.05/1.29  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('99', plain, ((v2_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('100', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A))
% 1.05/1.29          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 1.05/1.29          | ((X0) = (k2_funct_1 @ sk_C))
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_relat_1 @ X0))),
% 1.05/1.29      inference('demod', [status(thm)], ['94', '97', '98', '99'])).
% 1.05/1.29  thf('101', plain,
% 1.05/1.29      ((((k2_relat_1 @ sk_C) != (sk_B))
% 1.05/1.29        | ~ (v1_relat_1 @ sk_D)
% 1.05/1.29        | ~ (v1_funct_1 @ sk_D)
% 1.05/1.29        | ((sk_D) = (k2_funct_1 @ sk_C))
% 1.05/1.29        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['76', '100'])).
% 1.05/1.29  thf('102', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('103', plain,
% 1.05/1.29      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.05/1.29         ((v1_relat_1 @ X5)
% 1.05/1.29          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.05/1.29      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.05/1.29  thf('104', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.29      inference('sup-', [status(thm)], ['102', '103'])).
% 1.05/1.29  thf('105', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('106', plain,
% 1.05/1.29      ((((k2_relat_1 @ sk_C) != (sk_B))
% 1.05/1.29        | ((sk_D) = (k2_funct_1 @ sk_C))
% 1.05/1.29        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 1.05/1.29      inference('demod', [status(thm)], ['101', '104', '105'])).
% 1.05/1.29  thf('107', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('108', plain,
% 1.05/1.29      ((((k2_relat_1 @ sk_C) != (sk_B))
% 1.05/1.29        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 1.05/1.29      inference('simplify_reflect-', [status(thm)], ['106', '107'])).
% 1.05/1.29  thf(t61_funct_1, axiom,
% 1.05/1.29    (![A:$i]:
% 1.05/1.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.05/1.29       ( ( v2_funct_1 @ A ) =>
% 1.05/1.29         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.05/1.29             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.05/1.29           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.05/1.29             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.05/1.29  thf('109', plain,
% 1.05/1.29      (![X2 : $i]:
% 1.05/1.29         (~ (v2_funct_1 @ X2)
% 1.05/1.29          | ((k5_relat_1 @ (k2_funct_1 @ X2) @ X2)
% 1.05/1.29              = (k6_relat_1 @ (k2_relat_1 @ X2)))
% 1.05/1.29          | ~ (v1_funct_1 @ X2)
% 1.05/1.29          | ~ (v1_relat_1 @ X2))),
% 1.05/1.29      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.05/1.29  thf('110', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.29  thf('111', plain,
% 1.05/1.29      (![X2 : $i]:
% 1.05/1.29         (~ (v2_funct_1 @ X2)
% 1.05/1.29          | ((k5_relat_1 @ (k2_funct_1 @ X2) @ X2)
% 1.05/1.29              = (k6_partfun1 @ (k2_relat_1 @ X2)))
% 1.05/1.29          | ~ (v1_funct_1 @ X2)
% 1.05/1.29          | ~ (v1_relat_1 @ X2))),
% 1.05/1.29      inference('demod', [status(thm)], ['109', '110'])).
% 1.05/1.29  thf('112', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('113', plain,
% 1.05/1.29      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.05/1.29         (((X39) = (k1_xboole_0))
% 1.05/1.29          | ~ (v1_funct_1 @ X40)
% 1.05/1.29          | ~ (v1_funct_2 @ X40 @ X41 @ X39)
% 1.05/1.29          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X39)))
% 1.05/1.29          | ((k5_relat_1 @ (k2_funct_1 @ X40) @ X40) = (k6_partfun1 @ X39))
% 1.05/1.29          | ~ (v2_funct_1 @ X40)
% 1.05/1.29          | ((k2_relset_1 @ X41 @ X39 @ X40) != (X39)))),
% 1.05/1.29      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.05/1.29  thf('114', plain,
% 1.05/1.29      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.05/1.29        | ~ (v2_funct_1 @ sk_C)
% 1.05/1.29        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.05/1.29        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.05/1.29        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.29        | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['112', '113'])).
% 1.05/1.29  thf('115', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('116', plain, ((v2_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('117', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('118', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('119', plain,
% 1.05/1.29      ((((sk_B) != (sk_B))
% 1.05/1.29        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.05/1.29        | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.29      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 1.05/1.29  thf('120', plain,
% 1.05/1.29      ((((sk_B) = (k1_xboole_0))
% 1.05/1.29        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.05/1.29      inference('simplify', [status(thm)], ['119'])).
% 1.05/1.29  thf('121', plain, (((sk_B) != (k1_xboole_0))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('122', plain,
% 1.05/1.29      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.05/1.29      inference('simplify_reflect-', [status(thm)], ['120', '121'])).
% 1.05/1.29  thf('123', plain,
% 1.05/1.29      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))
% 1.05/1.29        | ~ (v1_relat_1 @ sk_C)
% 1.05/1.29        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.29        | ~ (v2_funct_1 @ sk_C))),
% 1.05/1.29      inference('sup+', [status(thm)], ['111', '122'])).
% 1.05/1.29  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.29      inference('sup-', [status(thm)], ['95', '96'])).
% 1.05/1.29  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('127', plain,
% 1.05/1.29      (((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))),
% 1.05/1.29      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 1.05/1.29  thf(t71_relat_1, axiom,
% 1.05/1.29    (![A:$i]:
% 1.05/1.29     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.05/1.29       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.05/1.29  thf('128', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 1.05/1.29      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.05/1.29  thf('129', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.29  thf('130', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 1.05/1.29      inference('demod', [status(thm)], ['128', '129'])).
% 1.05/1.29  thf('131', plain,
% 1.05/1.29      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 1.05/1.29      inference('sup+', [status(thm)], ['127', '130'])).
% 1.05/1.29  thf('132', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 1.05/1.29      inference('demod', [status(thm)], ['128', '129'])).
% 1.05/1.29  thf('133', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 1.05/1.29      inference('demod', [status(thm)], ['131', '132'])).
% 1.05/1.29  thf('134', plain,
% 1.05/1.29      ((((sk_B) != (sk_B))
% 1.05/1.29        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 1.05/1.29      inference('demod', [status(thm)], ['108', '133'])).
% 1.05/1.29  thf('135', plain, (((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A))),
% 1.05/1.29      inference('simplify', [status(thm)], ['134'])).
% 1.05/1.29  thf('136', plain, ($false),
% 1.05/1.29      inference('simplify_reflect-', [status(thm)], ['62', '135'])).
% 1.05/1.29  
% 1.05/1.29  % SZS output end Refutation
% 1.05/1.29  
% 1.05/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
