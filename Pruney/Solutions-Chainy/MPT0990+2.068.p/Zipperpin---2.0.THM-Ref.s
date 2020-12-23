%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5FqzHFu0CI

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:05 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  267 (1590 expanded)
%              Number of leaves         :   50 ( 485 expanded)
%              Depth                    :   25
%              Number of atoms          : 2642 (38236 expanded)
%              Number of equality atoms :  189 (2677 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ X51 @ ( k2_funct_1 @ X51 ) )
        = ( k6_partfun1 @ X52 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ X51 @ ( k2_funct_1 @ X51 ) )
        = ( k6_relat_1 @ X52 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
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

thf('18',plain,(
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

thf('19',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_relset_1 @ X38 @ X38 @ ( k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40 ) @ ( k6_relat_1 @ X38 ) )
      | ( ( k2_relset_1 @ X39 @ X38 @ X40 )
        = X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('30',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['25','30','31','32','33','34'])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['7','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','36','37','38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('44',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('54',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('55',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','56'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('58',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('59',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('60',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['43','61'])).

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
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('70',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('71',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['69','70','71','72','73','74'])).

thf('76',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('78',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v2_funct_1 @ X42 )
      | ~ ( zip_tseitin_0 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('82',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['42','82'])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['25','30','31','32','33','34'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('85',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('86',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('88',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('90',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('91',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('92',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('93',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('97',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k4_relat_1 @ sk_D ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['84','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('109',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('110',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k4_relat_1 @ sk_D ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['107','110','111'])).

thf('113',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['25','30','31','32','33','34'])).

thf('114',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('115',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k4_relat_1 @ sk_D ) )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['113','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['108','109'])).

thf('121',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k4_relat_1 @ sk_D ) )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k4_relat_1 @ sk_D )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['112','121'])).

thf('123',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['80','81'])).

thf('124',plain,
    ( ( k4_relat_1 @ sk_D )
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['83','124'])).

thf('126',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

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
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['125','129'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('131',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('132',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['108','109'])).

thf('133',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['80','81'])).

thf('135',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['130','131','132','133','134'])).

thf('136',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('137',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X51 ) @ X51 )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('141',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('142',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X51 ) @ X51 )
        = ( k6_relat_1 @ X50 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('147',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('149',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('153',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('156',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['153','156','157','158'])).

thf('160',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k4_relat_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['146','159'])).

thf('161',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['149','150'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('163',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k4_relat_1 @ sk_C ) )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['154','155'])).

thf('165',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['154','155'])).

thf('167',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['160','165','166','167','168'])).

thf('170',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['143','144','145','169','170','171'])).

thf('173',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['173','174'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('176',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['175','176'])).

thf('178',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['160','165','166','167','168'])).

thf('179',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('180',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['154','155'])).

thf('182',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['154','155'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['177','183','184'])).

thf('186',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['138','185'])).

thf('187',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ X51 @ ( k2_funct_1 @ X51 ) )
        = ( k6_relat_1 @ X52 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('189',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['160','165','166','167','168'])).

thf('193',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['189','190','191','192','193','194'])).

thf('196',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['177','183','184'])).

thf('200',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k4_relat_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('202',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('203',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['200','201','202'])).

thf('204',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['108','109'])).

thf('205',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['186','203','204'])).

thf('206',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['108','109'])).

thf('207',plain,
    ( ( k4_relat_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['137','205','206'])).

thf('208',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('209',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( sk_D
     != ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['154','155'])).

thf('212',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['210','211','212','213'])).

thf('215',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['207','214'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5FqzHFu0CI
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:44:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.40/1.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.40/1.59  % Solved by: fo/fo7.sh
% 1.40/1.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.40/1.59  % done 1185 iterations in 1.122s
% 1.40/1.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.40/1.59  % SZS output start Refutation
% 1.40/1.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.40/1.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.40/1.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.40/1.59  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.40/1.59  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.40/1.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.40/1.59  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.40/1.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.40/1.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.40/1.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.40/1.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.40/1.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.40/1.59  thf(sk_D_type, type, sk_D: $i).
% 1.40/1.59  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.40/1.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.40/1.59  thf(sk_C_type, type, sk_C: $i).
% 1.40/1.59  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.40/1.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.40/1.59  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.40/1.59  thf(sk_A_type, type, sk_A: $i).
% 1.40/1.59  thf(sk_B_type, type, sk_B: $i).
% 1.40/1.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.40/1.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.40/1.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.40/1.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.40/1.59  thf(t36_funct_2, conjecture,
% 1.40/1.59    (![A:$i,B:$i,C:$i]:
% 1.40/1.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.40/1.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.40/1.59       ( ![D:$i]:
% 1.40/1.59         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.40/1.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.40/1.59           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.40/1.59               ( r2_relset_1 @
% 1.40/1.59                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.40/1.59                 ( k6_partfun1 @ A ) ) & 
% 1.40/1.59               ( v2_funct_1 @ C ) ) =>
% 1.40/1.59             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.40/1.59               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.40/1.59  thf(zf_stmt_0, negated_conjecture,
% 1.40/1.59    (~( ![A:$i,B:$i,C:$i]:
% 1.40/1.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.40/1.59            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.40/1.59          ( ![D:$i]:
% 1.40/1.59            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.40/1.59                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.40/1.59              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.40/1.59                  ( r2_relset_1 @
% 1.40/1.59                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.40/1.59                    ( k6_partfun1 @ A ) ) & 
% 1.40/1.59                  ( v2_funct_1 @ C ) ) =>
% 1.40/1.59                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.40/1.59                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.40/1.59    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.40/1.59  thf('0', plain,
% 1.40/1.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf(t35_funct_2, axiom,
% 1.40/1.59    (![A:$i,B:$i,C:$i]:
% 1.40/1.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.40/1.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.40/1.59       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.40/1.59         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.40/1.59           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.40/1.59             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.40/1.59  thf('1', plain,
% 1.40/1.59      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.40/1.59         (((X50) = (k1_xboole_0))
% 1.40/1.59          | ~ (v1_funct_1 @ X51)
% 1.40/1.59          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.40/1.59          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.40/1.59          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_partfun1 @ X52))
% 1.40/1.59          | ~ (v2_funct_1 @ X51)
% 1.40/1.59          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.40/1.59      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.40/1.59  thf(redefinition_k6_partfun1, axiom,
% 1.40/1.59    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.40/1.59  thf('2', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.40/1.59      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.40/1.59  thf('3', plain,
% 1.40/1.59      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.40/1.59         (((X50) = (k1_xboole_0))
% 1.40/1.59          | ~ (v1_funct_1 @ X51)
% 1.40/1.59          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.40/1.59          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.40/1.59          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_relat_1 @ X52))
% 1.40/1.59          | ~ (v2_funct_1 @ X51)
% 1.40/1.59          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.40/1.59      inference('demod', [status(thm)], ['1', '2'])).
% 1.40/1.59  thf('4', plain,
% 1.40/1.59      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.40/1.59        | ~ (v2_funct_1 @ sk_D)
% 1.40/1.59        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.40/1.59        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.40/1.59        | ~ (v1_funct_1 @ sk_D)
% 1.40/1.59        | ((sk_A) = (k1_xboole_0)))),
% 1.40/1.59      inference('sup-', [status(thm)], ['0', '3'])).
% 1.40/1.59  thf('5', plain,
% 1.40/1.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf(redefinition_k2_relset_1, axiom,
% 1.40/1.59    (![A:$i,B:$i,C:$i]:
% 1.40/1.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.40/1.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.40/1.59  thf('6', plain,
% 1.40/1.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.40/1.59         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.40/1.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.40/1.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.40/1.59  thf('7', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.40/1.59      inference('sup-', [status(thm)], ['5', '6'])).
% 1.40/1.59  thf('8', plain,
% 1.40/1.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('9', plain,
% 1.40/1.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf(redefinition_k1_partfun1, axiom,
% 1.40/1.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.40/1.59     ( ( ( v1_funct_1 @ E ) & 
% 1.40/1.59         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.40/1.59         ( v1_funct_1 @ F ) & 
% 1.40/1.59         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.40/1.59       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.40/1.59  thf('10', plain,
% 1.40/1.59      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.40/1.59         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.40/1.59          | ~ (v1_funct_1 @ X30)
% 1.40/1.59          | ~ (v1_funct_1 @ X33)
% 1.40/1.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.40/1.59          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 1.40/1.59              = (k5_relat_1 @ X30 @ X33)))),
% 1.40/1.59      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.40/1.59  thf('11', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.40/1.59         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.40/1.59            = (k5_relat_1 @ sk_C @ X0))
% 1.40/1.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ sk_C))),
% 1.40/1.59      inference('sup-', [status(thm)], ['9', '10'])).
% 1.40/1.59  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('13', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.40/1.59         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.40/1.59            = (k5_relat_1 @ sk_C @ X0))
% 1.40/1.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.40/1.59          | ~ (v1_funct_1 @ X0))),
% 1.40/1.59      inference('demod', [status(thm)], ['11', '12'])).
% 1.40/1.59  thf('14', plain,
% 1.40/1.59      ((~ (v1_funct_1 @ sk_D)
% 1.40/1.59        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.40/1.59            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.40/1.59      inference('sup-', [status(thm)], ['8', '13'])).
% 1.40/1.59  thf('15', plain, ((v1_funct_1 @ sk_D)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('16', plain,
% 1.40/1.59      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.40/1.59         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.40/1.59      inference('demod', [status(thm)], ['14', '15'])).
% 1.40/1.59  thf('17', plain,
% 1.40/1.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf(t24_funct_2, axiom,
% 1.40/1.59    (![A:$i,B:$i,C:$i]:
% 1.40/1.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.40/1.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.40/1.59       ( ![D:$i]:
% 1.40/1.59         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.40/1.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.40/1.59           ( ( r2_relset_1 @
% 1.40/1.59               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.40/1.59               ( k6_partfun1 @ B ) ) =>
% 1.40/1.59             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.40/1.59  thf('18', plain,
% 1.40/1.59      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.40/1.59         (~ (v1_funct_1 @ X37)
% 1.40/1.59          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 1.40/1.59          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.40/1.59          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 1.40/1.59               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 1.40/1.59               (k6_partfun1 @ X38))
% 1.40/1.59          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 1.40/1.59          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 1.40/1.59          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 1.40/1.59          | ~ (v1_funct_1 @ X40))),
% 1.40/1.59      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.40/1.59  thf('19', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.40/1.59      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.40/1.59  thf('20', plain,
% 1.40/1.59      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.40/1.59         (~ (v1_funct_1 @ X37)
% 1.40/1.59          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 1.40/1.59          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.40/1.59          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 1.40/1.59               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 1.40/1.59               (k6_relat_1 @ X38))
% 1.40/1.59          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 1.40/1.59          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 1.40/1.59          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 1.40/1.59          | ~ (v1_funct_1 @ X40))),
% 1.40/1.59      inference('demod', [status(thm)], ['18', '19'])).
% 1.40/1.59  thf('21', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.40/1.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.40/1.59          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.40/1.59          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.40/1.59               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.40/1.59               (k6_relat_1 @ sk_A))
% 1.40/1.59          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.40/1.59          | ~ (v1_funct_1 @ sk_C))),
% 1.40/1.59      inference('sup-', [status(thm)], ['17', '20'])).
% 1.40/1.59  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('24', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.40/1.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.40/1.59          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.40/1.59          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.40/1.59               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.40/1.59               (k6_relat_1 @ sk_A)))),
% 1.40/1.59      inference('demod', [status(thm)], ['21', '22', '23'])).
% 1.40/1.59  thf('25', plain,
% 1.40/1.59      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.40/1.59           (k6_relat_1 @ sk_A))
% 1.40/1.59        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.40/1.59        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.40/1.59        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.40/1.59        | ~ (v1_funct_1 @ sk_D))),
% 1.40/1.59      inference('sup-', [status(thm)], ['16', '24'])).
% 1.40/1.59  thf('26', plain,
% 1.40/1.59      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.40/1.59        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.40/1.59        (k6_partfun1 @ sk_A))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('27', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.40/1.59      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.40/1.59  thf('28', plain,
% 1.40/1.59      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.40/1.59        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.40/1.59        (k6_relat_1 @ sk_A))),
% 1.40/1.59      inference('demod', [status(thm)], ['26', '27'])).
% 1.40/1.59  thf('29', plain,
% 1.40/1.59      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.40/1.59         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.40/1.59      inference('demod', [status(thm)], ['14', '15'])).
% 1.40/1.59  thf('30', plain,
% 1.40/1.59      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.40/1.59        (k6_relat_1 @ sk_A))),
% 1.40/1.59      inference('demod', [status(thm)], ['28', '29'])).
% 1.40/1.59  thf('31', plain,
% 1.40/1.59      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.40/1.59      inference('sup-', [status(thm)], ['5', '6'])).
% 1.40/1.59  thf('32', plain,
% 1.40/1.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('33', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('35', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.40/1.59      inference('demod', [status(thm)], ['25', '30', '31', '32', '33', '34'])).
% 1.40/1.59  thf('36', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 1.40/1.59      inference('demod', [status(thm)], ['7', '35'])).
% 1.40/1.59  thf('37', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('39', plain,
% 1.40/1.59      ((((sk_A) != (sk_A))
% 1.40/1.59        | ~ (v2_funct_1 @ sk_D)
% 1.40/1.59        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.40/1.59        | ((sk_A) = (k1_xboole_0)))),
% 1.40/1.59      inference('demod', [status(thm)], ['4', '36', '37', '38'])).
% 1.40/1.59  thf('40', plain,
% 1.40/1.59      ((((sk_A) = (k1_xboole_0))
% 1.40/1.59        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.40/1.59        | ~ (v2_funct_1 @ sk_D))),
% 1.40/1.59      inference('simplify', [status(thm)], ['39'])).
% 1.40/1.59  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('42', plain,
% 1.40/1.59      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.40/1.59        | ~ (v2_funct_1 @ sk_D))),
% 1.40/1.59      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 1.40/1.59  thf('43', plain,
% 1.40/1.59      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.40/1.59         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.40/1.59      inference('demod', [status(thm)], ['14', '15'])).
% 1.40/1.59  thf('44', plain,
% 1.40/1.59      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.40/1.59        (k6_relat_1 @ sk_A))),
% 1.40/1.59      inference('demod', [status(thm)], ['28', '29'])).
% 1.40/1.59  thf('45', plain,
% 1.40/1.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('46', plain,
% 1.40/1.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf(dt_k1_partfun1, axiom,
% 1.40/1.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.40/1.59     ( ( ( v1_funct_1 @ E ) & 
% 1.40/1.59         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.40/1.59         ( v1_funct_1 @ F ) & 
% 1.40/1.59         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.40/1.59       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.40/1.59         ( m1_subset_1 @
% 1.40/1.59           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.40/1.59           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.40/1.59  thf('47', plain,
% 1.40/1.59      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.40/1.59         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.40/1.59          | ~ (v1_funct_1 @ X22)
% 1.40/1.59          | ~ (v1_funct_1 @ X25)
% 1.40/1.59          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.40/1.59          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 1.40/1.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 1.40/1.59      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.40/1.59  thf('48', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.40/1.59         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.40/1.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.40/1.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.40/1.59          | ~ (v1_funct_1 @ X1)
% 1.40/1.59          | ~ (v1_funct_1 @ sk_C))),
% 1.40/1.59      inference('sup-', [status(thm)], ['46', '47'])).
% 1.40/1.59  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('50', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.40/1.59         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.40/1.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.40/1.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.40/1.59          | ~ (v1_funct_1 @ X1))),
% 1.40/1.59      inference('demod', [status(thm)], ['48', '49'])).
% 1.40/1.59  thf('51', plain,
% 1.40/1.59      ((~ (v1_funct_1 @ sk_D)
% 1.40/1.59        | (m1_subset_1 @ 
% 1.40/1.59           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.40/1.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.40/1.59      inference('sup-', [status(thm)], ['45', '50'])).
% 1.40/1.59  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('53', plain,
% 1.40/1.59      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.40/1.59         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.40/1.59      inference('demod', [status(thm)], ['14', '15'])).
% 1.40/1.59  thf('54', plain,
% 1.40/1.59      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.40/1.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.40/1.59      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.40/1.59  thf(redefinition_r2_relset_1, axiom,
% 1.40/1.59    (![A:$i,B:$i,C:$i,D:$i]:
% 1.40/1.59     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.40/1.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.40/1.59       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.40/1.59  thf('55', plain,
% 1.40/1.59      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.40/1.59         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.40/1.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.40/1.59          | ((X18) = (X21))
% 1.40/1.59          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 1.40/1.59      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.40/1.59  thf('56', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.40/1.59          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.40/1.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.40/1.59      inference('sup-', [status(thm)], ['54', '55'])).
% 1.40/1.59  thf('57', plain,
% 1.40/1.59      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.40/1.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.40/1.59        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 1.40/1.59      inference('sup-', [status(thm)], ['44', '56'])).
% 1.40/1.59  thf(dt_k6_partfun1, axiom,
% 1.40/1.59    (![A:$i]:
% 1.40/1.59     ( ( m1_subset_1 @
% 1.40/1.59         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.40/1.59       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.40/1.59  thf('58', plain,
% 1.40/1.59      (![X29 : $i]:
% 1.40/1.59         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 1.40/1.59          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 1.40/1.59      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.40/1.59  thf('59', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.40/1.59      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.40/1.59  thf('60', plain,
% 1.40/1.59      (![X29 : $i]:
% 1.40/1.59         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 1.40/1.59          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 1.40/1.59      inference('demod', [status(thm)], ['58', '59'])).
% 1.40/1.59  thf('61', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.40/1.59      inference('demod', [status(thm)], ['57', '60'])).
% 1.40/1.59  thf('62', plain,
% 1.40/1.59      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.40/1.59         = (k6_relat_1 @ sk_A))),
% 1.40/1.59      inference('demod', [status(thm)], ['43', '61'])).
% 1.40/1.59  thf('63', plain,
% 1.40/1.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf(t30_funct_2, axiom,
% 1.40/1.59    (![A:$i,B:$i,C:$i,D:$i]:
% 1.40/1.59     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.40/1.59         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.40/1.59       ( ![E:$i]:
% 1.40/1.59         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.40/1.59             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.40/1.59           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.40/1.59               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.40/1.59             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.40/1.59               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.40/1.59  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.40/1.59  thf(zf_stmt_2, axiom,
% 1.40/1.59    (![C:$i,B:$i]:
% 1.40/1.59     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.40/1.59       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.40/1.59  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.40/1.59  thf(zf_stmt_4, axiom,
% 1.40/1.59    (![E:$i,D:$i]:
% 1.40/1.59     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.40/1.59  thf(zf_stmt_5, axiom,
% 1.40/1.59    (![A:$i,B:$i,C:$i,D:$i]:
% 1.40/1.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.40/1.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.40/1.59       ( ![E:$i]:
% 1.40/1.59         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.40/1.59             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.40/1.59           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.40/1.59               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.40/1.59             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.40/1.59  thf('64', plain,
% 1.40/1.59      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.40/1.59         (~ (v1_funct_1 @ X45)
% 1.40/1.59          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 1.40/1.59          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 1.40/1.59          | (zip_tseitin_0 @ X45 @ X48)
% 1.40/1.59          | ~ (v2_funct_1 @ (k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45))
% 1.40/1.59          | (zip_tseitin_1 @ X47 @ X46)
% 1.40/1.59          | ((k2_relset_1 @ X49 @ X46 @ X48) != (X46))
% 1.40/1.59          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X46)))
% 1.40/1.59          | ~ (v1_funct_2 @ X48 @ X49 @ X46)
% 1.40/1.59          | ~ (v1_funct_1 @ X48))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.40/1.59  thf('65', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         (~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.40/1.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.40/1.59          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.40/1.59          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.40/1.59          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.40/1.59          | (zip_tseitin_0 @ sk_D @ X0)
% 1.40/1.59          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.40/1.59          | ~ (v1_funct_1 @ sk_D))),
% 1.40/1.59      inference('sup-', [status(thm)], ['63', '64'])).
% 1.40/1.59  thf('66', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('67', plain, ((v1_funct_1 @ sk_D)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('68', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         (~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.40/1.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.40/1.59          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.40/1.59          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.40/1.59          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.40/1.59          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.40/1.59      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.40/1.59  thf('69', plain,
% 1.40/1.59      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.40/1.59        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.40/1.59        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.40/1.59        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.40/1.59        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.40/1.59        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.40/1.59        | ~ (v1_funct_1 @ sk_C))),
% 1.40/1.59      inference('sup-', [status(thm)], ['62', '68'])).
% 1.40/1.59  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.40/1.59  thf('70', plain, (![X10 : $i]: (v2_funct_1 @ (k6_relat_1 @ X10))),
% 1.40/1.59      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.40/1.59  thf('71', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('72', plain,
% 1.40/1.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('73', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('75', plain,
% 1.40/1.59      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.40/1.59        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.40/1.59        | ((sk_B) != (sk_B)))),
% 1.40/1.59      inference('demod', [status(thm)], ['69', '70', '71', '72', '73', '74'])).
% 1.40/1.59  thf('76', plain,
% 1.40/1.59      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.40/1.59      inference('simplify', [status(thm)], ['75'])).
% 1.40/1.59  thf('77', plain,
% 1.40/1.59      (![X43 : $i, X44 : $i]:
% 1.40/1.59         (((X43) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X43 @ X44))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.40/1.59  thf('78', plain,
% 1.40/1.59      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.40/1.59      inference('sup-', [status(thm)], ['76', '77'])).
% 1.40/1.59  thf('79', plain, (((sk_A) != (k1_xboole_0))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('80', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.40/1.59      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 1.40/1.59  thf('81', plain,
% 1.40/1.59      (![X41 : $i, X42 : $i]:
% 1.40/1.59         ((v2_funct_1 @ X42) | ~ (zip_tseitin_0 @ X42 @ X41))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.40/1.59  thf('82', plain, ((v2_funct_1 @ sk_D)),
% 1.40/1.59      inference('sup-', [status(thm)], ['80', '81'])).
% 1.40/1.59  thf('83', plain,
% 1.40/1.59      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.40/1.59      inference('demod', [status(thm)], ['42', '82'])).
% 1.40/1.59  thf('84', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.40/1.59      inference('demod', [status(thm)], ['25', '30', '31', '32', '33', '34'])).
% 1.40/1.59  thf(d9_funct_1, axiom,
% 1.40/1.59    (![A:$i]:
% 1.40/1.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.40/1.59       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.40/1.59  thf('85', plain,
% 1.40/1.59      (![X8 : $i]:
% 1.40/1.59         (~ (v2_funct_1 @ X8)
% 1.40/1.59          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 1.40/1.59          | ~ (v1_funct_1 @ X8)
% 1.40/1.59          | ~ (v1_relat_1 @ X8))),
% 1.40/1.59      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.40/1.59  thf(t37_relat_1, axiom,
% 1.40/1.59    (![A:$i]:
% 1.40/1.59     ( ( v1_relat_1 @ A ) =>
% 1.40/1.59       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.40/1.59         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.40/1.59  thf('86', plain,
% 1.40/1.59      (![X1 : $i]:
% 1.40/1.59         (((k2_relat_1 @ X1) = (k1_relat_1 @ (k4_relat_1 @ X1)))
% 1.40/1.59          | ~ (v1_relat_1 @ X1))),
% 1.40/1.59      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.40/1.59  thf(dt_k4_relat_1, axiom,
% 1.40/1.59    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 1.40/1.59  thf('87', plain,
% 1.40/1.59      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 1.40/1.59      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.40/1.59  thf('88', plain,
% 1.40/1.59      (![X1 : $i]:
% 1.40/1.59         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 1.40/1.59          | ~ (v1_relat_1 @ X1))),
% 1.40/1.59      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.40/1.59  thf('89', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (~ (v1_relat_1 @ X0)
% 1.40/1.59          | ((k1_relat_1 @ (k4_relat_1 @ X0))
% 1.40/1.59              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 1.40/1.59      inference('sup-', [status(thm)], ['87', '88'])).
% 1.40/1.59  thf(dt_k2_funct_1, axiom,
% 1.40/1.59    (![A:$i]:
% 1.40/1.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.40/1.59       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.40/1.59         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.40/1.59  thf('90', plain,
% 1.40/1.59      (![X9 : $i]:
% 1.40/1.59         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.40/1.59          | ~ (v1_funct_1 @ X9)
% 1.40/1.59          | ~ (v1_relat_1 @ X9))),
% 1.40/1.59      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.40/1.59  thf('91', plain,
% 1.40/1.59      (![X8 : $i]:
% 1.40/1.59         (~ (v2_funct_1 @ X8)
% 1.40/1.59          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 1.40/1.59          | ~ (v1_funct_1 @ X8)
% 1.40/1.59          | ~ (v1_relat_1 @ X8))),
% 1.40/1.59      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.40/1.59  thf('92', plain,
% 1.40/1.59      (![X9 : $i]:
% 1.40/1.59         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.40/1.59          | ~ (v1_funct_1 @ X9)
% 1.40/1.59          | ~ (v1_relat_1 @ X9))),
% 1.40/1.59      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.40/1.59  thf('93', plain,
% 1.40/1.59      (![X1 : $i]:
% 1.40/1.59         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 1.40/1.59          | ~ (v1_relat_1 @ X1))),
% 1.40/1.59      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.40/1.59  thf('94', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (~ (v1_relat_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 1.40/1.59              = (k2_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.40/1.59      inference('sup-', [status(thm)], ['92', '93'])).
% 1.40/1.59  thf('95', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 1.40/1.59            = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v2_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ X0))),
% 1.40/1.59      inference('sup+', [status(thm)], ['91', '94'])).
% 1.40/1.59  thf('96', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (~ (v2_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 1.40/1.59              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 1.40/1.59      inference('simplify', [status(thm)], ['95'])).
% 1.40/1.59  thf(t78_relat_1, axiom,
% 1.40/1.59    (![A:$i]:
% 1.40/1.59     ( ( v1_relat_1 @ A ) =>
% 1.40/1.59       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.40/1.59  thf('97', plain,
% 1.40/1.59      (![X7 : $i]:
% 1.40/1.59         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 1.40/1.59          | ~ (v1_relat_1 @ X7))),
% 1.40/1.59      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.40/1.59  thf('98', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (((k5_relat_1 @ 
% 1.40/1.59            (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))) @ 
% 1.40/1.59            (k2_funct_1 @ X0)) = (k2_funct_1 @ X0))
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v2_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.40/1.59      inference('sup+', [status(thm)], ['96', '97'])).
% 1.40/1.59  thf('99', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (~ (v1_relat_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v2_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ((k5_relat_1 @ 
% 1.40/1.59              (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))) @ 
% 1.40/1.59              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 1.40/1.59      inference('sup-', [status(thm)], ['90', '98'])).
% 1.40/1.59  thf('100', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (((k5_relat_1 @ 
% 1.40/1.59            (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))) @ 
% 1.40/1.59            (k2_funct_1 @ X0)) = (k2_funct_1 @ X0))
% 1.40/1.59          | ~ (v2_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ X0))),
% 1.40/1.59      inference('simplify', [status(thm)], ['99'])).
% 1.40/1.59  thf('101', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))) @ 
% 1.40/1.59            (k2_funct_1 @ X0)) = (k2_funct_1 @ X0))
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v2_funct_1 @ X0))),
% 1.40/1.59      inference('sup+', [status(thm)], ['89', '100'])).
% 1.40/1.59  thf('102', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (~ (v2_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))) @ 
% 1.40/1.59              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 1.40/1.59      inference('simplify', [status(thm)], ['101'])).
% 1.40/1.59  thf('103', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 1.40/1.59            = (k2_funct_1 @ X0))
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v2_funct_1 @ X0))),
% 1.40/1.59      inference('sup+', [status(thm)], ['86', '102'])).
% 1.40/1.59  thf('104', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (~ (v2_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 1.40/1.59              = (k2_funct_1 @ X0)))),
% 1.40/1.59      inference('simplify', [status(thm)], ['103'])).
% 1.40/1.59  thf('105', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0))
% 1.40/1.59            = (k2_funct_1 @ X0))
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v2_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v2_funct_1 @ X0))),
% 1.40/1.59      inference('sup+', [status(thm)], ['85', '104'])).
% 1.40/1.59  thf('106', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (~ (v2_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0))
% 1.40/1.59              = (k2_funct_1 @ X0)))),
% 1.40/1.59      inference('simplify', [status(thm)], ['105'])).
% 1.40/1.59  thf('107', plain,
% 1.40/1.59      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k4_relat_1 @ sk_D))
% 1.40/1.59          = (k2_funct_1 @ sk_D))
% 1.40/1.59        | ~ (v1_relat_1 @ sk_D)
% 1.40/1.59        | ~ (v1_funct_1 @ sk_D)
% 1.40/1.59        | ~ (v2_funct_1 @ sk_D))),
% 1.40/1.59      inference('sup+', [status(thm)], ['84', '106'])).
% 1.40/1.59  thf('108', plain,
% 1.40/1.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf(cc1_relset_1, axiom,
% 1.40/1.59    (![A:$i,B:$i,C:$i]:
% 1.40/1.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.40/1.59       ( v1_relat_1 @ C ) ))).
% 1.40/1.59  thf('109', plain,
% 1.40/1.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.40/1.59         ((v1_relat_1 @ X12)
% 1.40/1.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.40/1.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.40/1.59  thf('110', plain, ((v1_relat_1 @ sk_D)),
% 1.40/1.59      inference('sup-', [status(thm)], ['108', '109'])).
% 1.40/1.59  thf('111', plain, ((v1_funct_1 @ sk_D)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('112', plain,
% 1.40/1.59      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k4_relat_1 @ sk_D))
% 1.40/1.59          = (k2_funct_1 @ sk_D))
% 1.40/1.59        | ~ (v2_funct_1 @ sk_D))),
% 1.40/1.59      inference('demod', [status(thm)], ['107', '110', '111'])).
% 1.40/1.59  thf('113', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.40/1.59      inference('demod', [status(thm)], ['25', '30', '31', '32', '33', '34'])).
% 1.40/1.59  thf('114', plain,
% 1.40/1.59      (![X1 : $i]:
% 1.40/1.59         (((k2_relat_1 @ X1) = (k1_relat_1 @ (k4_relat_1 @ X1)))
% 1.40/1.59          | ~ (v1_relat_1 @ X1))),
% 1.40/1.59      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.40/1.59  thf('115', plain,
% 1.40/1.59      (![X7 : $i]:
% 1.40/1.59         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 1.40/1.59          | ~ (v1_relat_1 @ X7))),
% 1.40/1.59      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.40/1.59  thf('116', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0))
% 1.40/1.59            = (k4_relat_1 @ X0))
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 1.40/1.59      inference('sup+', [status(thm)], ['114', '115'])).
% 1.40/1.59  thf('117', plain,
% 1.40/1.59      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 1.40/1.59      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.40/1.59  thf('118', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (~ (v1_relat_1 @ X0)
% 1.40/1.59          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0))
% 1.40/1.59              = (k4_relat_1 @ X0)))),
% 1.40/1.59      inference('clc', [status(thm)], ['116', '117'])).
% 1.40/1.59  thf('119', plain,
% 1.40/1.59      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k4_relat_1 @ sk_D))
% 1.40/1.59          = (k4_relat_1 @ sk_D))
% 1.40/1.59        | ~ (v1_relat_1 @ sk_D))),
% 1.40/1.59      inference('sup+', [status(thm)], ['113', '118'])).
% 1.40/1.59  thf('120', plain, ((v1_relat_1 @ sk_D)),
% 1.40/1.59      inference('sup-', [status(thm)], ['108', '109'])).
% 1.40/1.59  thf('121', plain,
% 1.40/1.59      (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k4_relat_1 @ sk_D))
% 1.40/1.59         = (k4_relat_1 @ sk_D))),
% 1.40/1.59      inference('demod', [status(thm)], ['119', '120'])).
% 1.40/1.59  thf('122', plain,
% 1.40/1.59      ((((k4_relat_1 @ sk_D) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.40/1.59      inference('demod', [status(thm)], ['112', '121'])).
% 1.40/1.59  thf('123', plain, ((v2_funct_1 @ sk_D)),
% 1.40/1.59      inference('sup-', [status(thm)], ['80', '81'])).
% 1.40/1.59  thf('124', plain, (((k4_relat_1 @ sk_D) = (k2_funct_1 @ sk_D))),
% 1.40/1.59      inference('demod', [status(thm)], ['122', '123'])).
% 1.40/1.59  thf('125', plain,
% 1.40/1.59      (((k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.40/1.59      inference('demod', [status(thm)], ['83', '124'])).
% 1.40/1.59  thf('126', plain,
% 1.40/1.59      (![X8 : $i]:
% 1.40/1.59         (~ (v2_funct_1 @ X8)
% 1.40/1.59          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 1.40/1.59          | ~ (v1_funct_1 @ X8)
% 1.40/1.59          | ~ (v1_relat_1 @ X8))),
% 1.40/1.59      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.40/1.59  thf(t58_funct_1, axiom,
% 1.40/1.59    (![A:$i]:
% 1.40/1.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.40/1.59       ( ( v2_funct_1 @ A ) =>
% 1.40/1.59         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.40/1.59             ( k1_relat_1 @ A ) ) & 
% 1.40/1.59           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.40/1.59             ( k1_relat_1 @ A ) ) ) ) ))).
% 1.40/1.59  thf('127', plain,
% 1.40/1.59      (![X11 : $i]:
% 1.40/1.59         (~ (v2_funct_1 @ X11)
% 1.40/1.59          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ (k2_funct_1 @ X11)))
% 1.40/1.59              = (k1_relat_1 @ X11))
% 1.40/1.59          | ~ (v1_funct_1 @ X11)
% 1.40/1.59          | ~ (v1_relat_1 @ X11))),
% 1.40/1.59      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.40/1.59  thf('128', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 1.40/1.59            = (k1_relat_1 @ X0))
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v2_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v2_funct_1 @ X0))),
% 1.40/1.59      inference('sup+', [status(thm)], ['126', '127'])).
% 1.40/1.59  thf('129', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (~ (v2_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 1.40/1.59              = (k1_relat_1 @ X0)))),
% 1.40/1.59      inference('simplify', [status(thm)], ['128'])).
% 1.40/1.59  thf('130', plain,
% 1.40/1.59      ((((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 1.40/1.59        | ~ (v1_relat_1 @ sk_D)
% 1.40/1.59        | ~ (v1_funct_1 @ sk_D)
% 1.40/1.59        | ~ (v2_funct_1 @ sk_D))),
% 1.40/1.59      inference('sup+', [status(thm)], ['125', '129'])).
% 1.40/1.59  thf(t71_relat_1, axiom,
% 1.40/1.59    (![A:$i]:
% 1.40/1.59     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.40/1.59       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.40/1.59  thf('131', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 1.40/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.40/1.59  thf('132', plain, ((v1_relat_1 @ sk_D)),
% 1.40/1.59      inference('sup-', [status(thm)], ['108', '109'])).
% 1.40/1.59  thf('133', plain, ((v1_funct_1 @ sk_D)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('134', plain, ((v2_funct_1 @ sk_D)),
% 1.40/1.59      inference('sup-', [status(thm)], ['80', '81'])).
% 1.40/1.59  thf('135', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.40/1.59      inference('demod', [status(thm)], ['130', '131', '132', '133', '134'])).
% 1.40/1.59  thf('136', plain,
% 1.40/1.59      (![X7 : $i]:
% 1.40/1.59         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 1.40/1.59          | ~ (v1_relat_1 @ X7))),
% 1.40/1.59      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.40/1.59  thf('137', plain,
% 1.40/1.59      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (sk_D))
% 1.40/1.59        | ~ (v1_relat_1 @ sk_D))),
% 1.40/1.59      inference('sup+', [status(thm)], ['135', '136'])).
% 1.40/1.59  thf('138', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.40/1.59      inference('demod', [status(thm)], ['57', '60'])).
% 1.40/1.59  thf('139', plain,
% 1.40/1.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('140', plain,
% 1.40/1.59      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.40/1.59         (((X50) = (k1_xboole_0))
% 1.40/1.59          | ~ (v1_funct_1 @ X51)
% 1.40/1.59          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.40/1.59          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.40/1.59          | ((k5_relat_1 @ (k2_funct_1 @ X51) @ X51) = (k6_partfun1 @ X50))
% 1.40/1.59          | ~ (v2_funct_1 @ X51)
% 1.40/1.59          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.40/1.59      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.40/1.59  thf('141', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.40/1.59      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.40/1.59  thf('142', plain,
% 1.40/1.59      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.40/1.59         (((X50) = (k1_xboole_0))
% 1.40/1.59          | ~ (v1_funct_1 @ X51)
% 1.40/1.59          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.40/1.59          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.40/1.59          | ((k5_relat_1 @ (k2_funct_1 @ X51) @ X51) = (k6_relat_1 @ X50))
% 1.40/1.59          | ~ (v2_funct_1 @ X51)
% 1.40/1.59          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.40/1.59      inference('demod', [status(thm)], ['140', '141'])).
% 1.40/1.59  thf('143', plain,
% 1.40/1.59      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.40/1.59        | ~ (v2_funct_1 @ sk_C)
% 1.40/1.59        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 1.40/1.59        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.40/1.59        | ~ (v1_funct_1 @ sk_C)
% 1.40/1.59        | ((sk_B) = (k1_xboole_0)))),
% 1.40/1.59      inference('sup-', [status(thm)], ['139', '142'])).
% 1.40/1.59  thf('144', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('145', plain, ((v2_funct_1 @ sk_C)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('146', plain,
% 1.40/1.59      (![X8 : $i]:
% 1.40/1.59         (~ (v2_funct_1 @ X8)
% 1.40/1.59          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 1.40/1.59          | ~ (v1_funct_1 @ X8)
% 1.40/1.59          | ~ (v1_relat_1 @ X8))),
% 1.40/1.59      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.40/1.59  thf('147', plain,
% 1.40/1.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('148', plain,
% 1.40/1.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.40/1.59         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.40/1.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.40/1.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.40/1.59  thf('149', plain,
% 1.40/1.59      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.40/1.59      inference('sup-', [status(thm)], ['147', '148'])).
% 1.40/1.59  thf('150', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('151', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.40/1.59      inference('sup+', [status(thm)], ['149', '150'])).
% 1.40/1.59  thf('152', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (~ (v2_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_funct_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 1.40/1.59              = (k2_funct_1 @ X0)))),
% 1.40/1.59      inference('simplify', [status(thm)], ['103'])).
% 1.40/1.59  thf('153', plain,
% 1.40/1.59      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.40/1.59          = (k2_funct_1 @ sk_C))
% 1.40/1.59        | ~ (v1_relat_1 @ sk_C)
% 1.40/1.59        | ~ (v1_funct_1 @ sk_C)
% 1.40/1.59        | ~ (v2_funct_1 @ sk_C))),
% 1.40/1.59      inference('sup+', [status(thm)], ['151', '152'])).
% 1.40/1.59  thf('154', plain,
% 1.40/1.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('155', plain,
% 1.40/1.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.40/1.59         ((v1_relat_1 @ X12)
% 1.40/1.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.40/1.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.40/1.59  thf('156', plain, ((v1_relat_1 @ sk_C)),
% 1.40/1.59      inference('sup-', [status(thm)], ['154', '155'])).
% 1.40/1.59  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('158', plain, ((v2_funct_1 @ sk_C)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('159', plain,
% 1.40/1.59      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.40/1.59         = (k2_funct_1 @ sk_C))),
% 1.40/1.59      inference('demod', [status(thm)], ['153', '156', '157', '158'])).
% 1.40/1.59  thf('160', plain,
% 1.40/1.59      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k4_relat_1 @ sk_C))
% 1.40/1.59          = (k2_funct_1 @ sk_C))
% 1.40/1.59        | ~ (v1_relat_1 @ sk_C)
% 1.40/1.59        | ~ (v1_funct_1 @ sk_C)
% 1.40/1.59        | ~ (v2_funct_1 @ sk_C))),
% 1.40/1.59      inference('sup+', [status(thm)], ['146', '159'])).
% 1.40/1.59  thf('161', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.40/1.59      inference('sup+', [status(thm)], ['149', '150'])).
% 1.40/1.59  thf('162', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (~ (v1_relat_1 @ X0)
% 1.40/1.59          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0))
% 1.40/1.59              = (k4_relat_1 @ X0)))),
% 1.40/1.59      inference('clc', [status(thm)], ['116', '117'])).
% 1.40/1.59  thf('163', plain,
% 1.40/1.59      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k4_relat_1 @ sk_C))
% 1.40/1.59          = (k4_relat_1 @ sk_C))
% 1.40/1.59        | ~ (v1_relat_1 @ sk_C))),
% 1.40/1.59      inference('sup+', [status(thm)], ['161', '162'])).
% 1.40/1.59  thf('164', plain, ((v1_relat_1 @ sk_C)),
% 1.40/1.59      inference('sup-', [status(thm)], ['154', '155'])).
% 1.40/1.59  thf('165', plain,
% 1.40/1.59      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k4_relat_1 @ sk_C))
% 1.40/1.59         = (k4_relat_1 @ sk_C))),
% 1.40/1.59      inference('demod', [status(thm)], ['163', '164'])).
% 1.40/1.59  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 1.40/1.59      inference('sup-', [status(thm)], ['154', '155'])).
% 1.40/1.59  thf('167', plain, ((v1_funct_1 @ sk_C)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('168', plain, ((v2_funct_1 @ sk_C)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('169', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.40/1.59      inference('demod', [status(thm)], ['160', '165', '166', '167', '168'])).
% 1.40/1.59  thf('170', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('172', plain,
% 1.40/1.59      ((((sk_B) != (sk_B))
% 1.40/1.59        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 1.40/1.59        | ((sk_B) = (k1_xboole_0)))),
% 1.40/1.59      inference('demod', [status(thm)],
% 1.40/1.59                ['143', '144', '145', '169', '170', '171'])).
% 1.40/1.59  thf('173', plain,
% 1.40/1.59      ((((sk_B) = (k1_xboole_0))
% 1.40/1.59        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 1.40/1.59      inference('simplify', [status(thm)], ['172'])).
% 1.40/1.59  thf('174', plain, (((sk_B) != (k1_xboole_0))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('175', plain,
% 1.40/1.59      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 1.40/1.59      inference('simplify_reflect-', [status(thm)], ['173', '174'])).
% 1.40/1.59  thf(t55_relat_1, axiom,
% 1.40/1.59    (![A:$i]:
% 1.40/1.59     ( ( v1_relat_1 @ A ) =>
% 1.40/1.59       ( ![B:$i]:
% 1.40/1.59         ( ( v1_relat_1 @ B ) =>
% 1.40/1.59           ( ![C:$i]:
% 1.40/1.59             ( ( v1_relat_1 @ C ) =>
% 1.40/1.59               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.40/1.59                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.40/1.59  thf('176', plain,
% 1.40/1.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.40/1.59         (~ (v1_relat_1 @ X2)
% 1.40/1.59          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 1.40/1.59              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 1.40/1.59          | ~ (v1_relat_1 @ X4)
% 1.40/1.59          | ~ (v1_relat_1 @ X3))),
% 1.40/1.59      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.40/1.59  thf('177', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 1.40/1.59            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.40/1.59          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.40/1.59          | ~ (v1_relat_1 @ X0)
% 1.40/1.59          | ~ (v1_relat_1 @ sk_C))),
% 1.40/1.59      inference('sup+', [status(thm)], ['175', '176'])).
% 1.40/1.59  thf('178', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.40/1.59      inference('demod', [status(thm)], ['160', '165', '166', '167', '168'])).
% 1.40/1.59  thf('179', plain,
% 1.40/1.59      (![X9 : $i]:
% 1.40/1.59         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.40/1.59          | ~ (v1_funct_1 @ X9)
% 1.40/1.59          | ~ (v1_relat_1 @ X9))),
% 1.40/1.59      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.40/1.59  thf('180', plain,
% 1.40/1.59      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.40/1.59        | ~ (v1_relat_1 @ sk_C)
% 1.40/1.59        | ~ (v1_funct_1 @ sk_C))),
% 1.40/1.59      inference('sup+', [status(thm)], ['178', '179'])).
% 1.40/1.59  thf('181', plain, ((v1_relat_1 @ sk_C)),
% 1.40/1.59      inference('sup-', [status(thm)], ['154', '155'])).
% 1.40/1.59  thf('182', plain, ((v1_funct_1 @ sk_C)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('183', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 1.40/1.59      inference('demod', [status(thm)], ['180', '181', '182'])).
% 1.40/1.59  thf('184', plain, ((v1_relat_1 @ sk_C)),
% 1.40/1.59      inference('sup-', [status(thm)], ['154', '155'])).
% 1.40/1.59  thf('185', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 1.40/1.59            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.40/1.59          | ~ (v1_relat_1 @ X0))),
% 1.40/1.59      inference('demod', [status(thm)], ['177', '183', '184'])).
% 1.40/1.59  thf('186', plain,
% 1.40/1.59      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D)
% 1.40/1.59          = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 1.40/1.59        | ~ (v1_relat_1 @ sk_D))),
% 1.40/1.59      inference('sup+', [status(thm)], ['138', '185'])).
% 1.40/1.59  thf('187', plain,
% 1.40/1.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('188', plain,
% 1.40/1.59      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.40/1.59         (((X50) = (k1_xboole_0))
% 1.40/1.59          | ~ (v1_funct_1 @ X51)
% 1.40/1.59          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.40/1.59          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.40/1.59          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_relat_1 @ X52))
% 1.40/1.59          | ~ (v2_funct_1 @ X51)
% 1.40/1.59          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.40/1.59      inference('demod', [status(thm)], ['1', '2'])).
% 1.40/1.59  thf('189', plain,
% 1.40/1.59      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.40/1.59        | ~ (v2_funct_1 @ sk_C)
% 1.40/1.59        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.40/1.59        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.40/1.59        | ~ (v1_funct_1 @ sk_C)
% 1.40/1.59        | ((sk_B) = (k1_xboole_0)))),
% 1.40/1.59      inference('sup-', [status(thm)], ['187', '188'])).
% 1.40/1.59  thf('190', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('191', plain, ((v2_funct_1 @ sk_C)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('192', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.40/1.59      inference('demod', [status(thm)], ['160', '165', '166', '167', '168'])).
% 1.40/1.59  thf('193', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('194', plain, ((v1_funct_1 @ sk_C)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('195', plain,
% 1.40/1.59      ((((sk_B) != (sk_B))
% 1.40/1.59        | ((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.40/1.59        | ((sk_B) = (k1_xboole_0)))),
% 1.40/1.59      inference('demod', [status(thm)],
% 1.40/1.59                ['189', '190', '191', '192', '193', '194'])).
% 1.40/1.59  thf('196', plain,
% 1.40/1.59      ((((sk_B) = (k1_xboole_0))
% 1.40/1.59        | ((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 1.40/1.59      inference('simplify', [status(thm)], ['195'])).
% 1.40/1.59  thf('197', plain, (((sk_B) != (k1_xboole_0))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('198', plain,
% 1.40/1.59      (((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 1.40/1.59      inference('simplify_reflect-', [status(thm)], ['196', '197'])).
% 1.40/1.59  thf('199', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 1.40/1.59            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.40/1.59          | ~ (v1_relat_1 @ X0))),
% 1.40/1.59      inference('demod', [status(thm)], ['177', '183', '184'])).
% 1.40/1.59  thf('200', plain,
% 1.40/1.59      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k4_relat_1 @ sk_C))
% 1.40/1.59          = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 1.40/1.59        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.40/1.59      inference('sup+', [status(thm)], ['198', '199'])).
% 1.40/1.59  thf('201', plain,
% 1.40/1.59      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k4_relat_1 @ sk_C))
% 1.40/1.59         = (k4_relat_1 @ sk_C))),
% 1.40/1.59      inference('demod', [status(thm)], ['163', '164'])).
% 1.40/1.59  thf('202', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 1.40/1.59      inference('demod', [status(thm)], ['180', '181', '182'])).
% 1.40/1.59  thf('203', plain,
% 1.40/1.59      (((k4_relat_1 @ sk_C)
% 1.40/1.59         = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ sk_A)))),
% 1.40/1.59      inference('demod', [status(thm)], ['200', '201', '202'])).
% 1.40/1.59  thf('204', plain, ((v1_relat_1 @ sk_D)),
% 1.40/1.59      inference('sup-', [status(thm)], ['108', '109'])).
% 1.40/1.59  thf('205', plain,
% 1.40/1.59      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (k4_relat_1 @ sk_C))),
% 1.40/1.59      inference('demod', [status(thm)], ['186', '203', '204'])).
% 1.40/1.59  thf('206', plain, ((v1_relat_1 @ sk_D)),
% 1.40/1.59      inference('sup-', [status(thm)], ['108', '109'])).
% 1.40/1.59  thf('207', plain, (((k4_relat_1 @ sk_C) = (sk_D))),
% 1.40/1.59      inference('demod', [status(thm)], ['137', '205', '206'])).
% 1.40/1.59  thf('208', plain,
% 1.40/1.59      (![X8 : $i]:
% 1.40/1.59         (~ (v2_funct_1 @ X8)
% 1.40/1.59          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 1.40/1.59          | ~ (v1_funct_1 @ X8)
% 1.40/1.59          | ~ (v1_relat_1 @ X8))),
% 1.40/1.59      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.40/1.59  thf('209', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('210', plain,
% 1.40/1.59      ((((sk_D) != (k4_relat_1 @ sk_C))
% 1.40/1.59        | ~ (v1_relat_1 @ sk_C)
% 1.40/1.59        | ~ (v1_funct_1 @ sk_C)
% 1.40/1.59        | ~ (v2_funct_1 @ sk_C))),
% 1.40/1.59      inference('sup-', [status(thm)], ['208', '209'])).
% 1.40/1.59  thf('211', plain, ((v1_relat_1 @ sk_C)),
% 1.40/1.59      inference('sup-', [status(thm)], ['154', '155'])).
% 1.40/1.59  thf('212', plain, ((v1_funct_1 @ sk_C)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('213', plain, ((v2_funct_1 @ sk_C)),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf('214', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 1.40/1.59      inference('demod', [status(thm)], ['210', '211', '212', '213'])).
% 1.40/1.59  thf('215', plain, ($false),
% 1.40/1.59      inference('simplify_reflect-', [status(thm)], ['207', '214'])).
% 1.40/1.59  
% 1.40/1.59  % SZS output end Refutation
% 1.40/1.59  
% 1.40/1.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
