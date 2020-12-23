%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hLAeLEa4VX

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:17 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  265 (1423 expanded)
%              Number of leaves         :   50 ( 430 expanded)
%              Depth                    :   29
%              Number of atoms          : 2457 (37729 expanded)
%              Number of equality atoms :  169 (2546 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X52 ) ) )
      | ( ( k5_relat_1 @ X53 @ ( k2_funct_1 @ X53 ) )
        = ( k6_partfun1 @ X54 ) )
      | ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X54 @ X52 @ X53 )
       != X52 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( r2_relset_1 @ X40 @ X40 @ ( k1_partfun1 @ X40 @ X41 @ X41 @ X40 @ X39 @ X42 ) @ ( k6_partfun1 @ X40 ) )
      | ( ( k2_relset_1 @ X41 @ X40 @ X42 )
        = X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('24',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','25','26','27','28'])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['5','29'])).

thf('31',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','30','31','32'])).

thf('34',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('38',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

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
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
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
    inference(demod,[status(thm)],['12','13'])).

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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X21 = X24 )
      | ~ ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 ) ) ),
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

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('52',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('53',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['37','55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( zip_tseitin_0 @ X47 @ X50 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X51 @ X48 @ X48 @ X49 @ X50 @ X47 ) )
      | ( zip_tseitin_1 @ X49 @ X48 )
      | ( ( k2_relset_1 @ X51 @ X48 @ X50 )
       != X48 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X48 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('59',plain,(
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
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
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
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('64',plain,(
    ! [X14: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('65',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('66',plain,(
    ! [X14: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['63','66','67','68','69','70'])).

thf('72',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('74',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X43: $i,X44: $i] :
      ( ( v2_funct_1 @ X44 )
      | ~ ( zip_tseitin_0 @ X44 @ X43 ) ) ),
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
    = ( k6_partfun1 @ sk_A ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X16
        = ( k2_funct_1 @ X17 ) )
      | ( ( k5_relat_1 @ X16 @ X17 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X17 ) ) )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('82',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('83',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X16
        = ( k2_funct_1 @ X17 ) )
      | ( ( k5_relat_1 @ X16 @ X17 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
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
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','25','26','27','28'])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('87',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('89',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('90',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('94',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['84','85','90','91','96','97','102'])).

thf('104',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','77'])).

thf('106',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('107',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('108',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','78'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('109',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('110',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('111',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('112',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ X15 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('114',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['113'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('115',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['111','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('124',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['109','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['108','128'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('130',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('131',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('132',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['88','89'])).

thf('134',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','77'])).

thf('136',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['129','132','133','134','135'])).

thf('137',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['107','136'])).

thf('138',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['88','89'])).

thf('139',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','77'])).

thf('141',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['106','141'])).

thf('143',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['79','143'])).

thf('145',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X16
        = ( k2_funct_1 @ X17 ) )
      | ( ( k5_relat_1 @ X16 @ X17 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('146',plain,
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
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['94','95'])).

thf('148',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('149',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','25','26','27','28'])).

thf('152',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('153',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('154',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ X15 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('155',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('156',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['94','95'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('158',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('160',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['158','159','160','161'])).

thf('163',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('164',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['155','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('167',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('170',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['154','170'])).

thf('172',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['94','95'])).

thf('173',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['113'])).

thf('174',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('175',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['171','172','173','174','175','176'])).

thf('178',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['94','95'])).

thf('179',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['177','182'])).

thf('184',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['113'])).

thf('185',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['153','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('188',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X52 ) ) )
      | ( ( k5_relat_1 @ X53 @ ( k2_funct_1 @ X53 ) )
        = ( k6_partfun1 @ X54 ) )
      | ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X54 @ X52 @ X53 )
       != X52 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('192',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['192','193','194','195','196'])).

thf('198',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('202',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['189','200','201'])).

thf('203',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['152','202'])).

thf('204',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('205',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['203','204','205','206'])).

thf('208',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['88','89'])).

thf('210',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['146','147','148','149','150','151','207','208','209'])).

thf('211',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['211','212'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hLAeLEa4VX
% 0.14/0.37  % Computer   : n020.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 16:48:52 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 1.65/1.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.88  % Solved by: fo/fo7.sh
% 1.65/1.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.88  % done 1429 iterations in 1.397s
% 1.65/1.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.88  % SZS output start Refutation
% 1.65/1.88  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.65/1.88  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.65/1.88  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.65/1.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.65/1.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.88  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.65/1.88  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.65/1.88  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.65/1.88  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.65/1.88  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.88  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.65/1.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.65/1.88  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.65/1.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.65/1.88  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.65/1.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.65/1.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.65/1.88  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.65/1.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.65/1.88  thf(sk_D_type, type, sk_D: $i).
% 1.65/1.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.65/1.88  thf(sk_C_type, type, sk_C: $i).
% 1.65/1.88  thf(t36_funct_2, conjecture,
% 1.65/1.88    (![A:$i,B:$i,C:$i]:
% 1.65/1.88     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.88       ( ![D:$i]:
% 1.65/1.88         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.65/1.88             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.65/1.88           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.65/1.88               ( r2_relset_1 @
% 1.65/1.88                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.65/1.88                 ( k6_partfun1 @ A ) ) & 
% 1.65/1.88               ( v2_funct_1 @ C ) ) =>
% 1.65/1.88             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.65/1.88               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.65/1.88  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.88    (~( ![A:$i,B:$i,C:$i]:
% 1.65/1.88        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.88            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.88          ( ![D:$i]:
% 1.65/1.88            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.65/1.88                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.65/1.88              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.65/1.88                  ( r2_relset_1 @
% 1.65/1.88                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.65/1.88                    ( k6_partfun1 @ A ) ) & 
% 1.65/1.88                  ( v2_funct_1 @ C ) ) =>
% 1.65/1.88                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.65/1.88                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.65/1.88    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.65/1.88  thf('0', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf(t35_funct_2, axiom,
% 1.65/1.88    (![A:$i,B:$i,C:$i]:
% 1.65/1.88     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.88       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.65/1.88         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.65/1.88           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.65/1.88             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.65/1.88  thf('1', plain,
% 1.65/1.88      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.65/1.88         (((X52) = (k1_xboole_0))
% 1.65/1.88          | ~ (v1_funct_1 @ X53)
% 1.65/1.88          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 1.65/1.88          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 1.65/1.88          | ((k5_relat_1 @ X53 @ (k2_funct_1 @ X53)) = (k6_partfun1 @ X54))
% 1.65/1.88          | ~ (v2_funct_1 @ X53)
% 1.65/1.88          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 1.65/1.88      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.65/1.88  thf('2', plain,
% 1.65/1.88      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.65/1.88        | ~ (v2_funct_1 @ sk_D)
% 1.65/1.88        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.65/1.88        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.65/1.88        | ~ (v1_funct_1 @ sk_D)
% 1.65/1.88        | ((sk_A) = (k1_xboole_0)))),
% 1.65/1.88      inference('sup-', [status(thm)], ['0', '1'])).
% 1.65/1.88  thf('3', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf(redefinition_k2_relset_1, axiom,
% 1.65/1.88    (![A:$i,B:$i,C:$i]:
% 1.65/1.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.88       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.65/1.88  thf('4', plain,
% 1.65/1.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.65/1.88         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 1.65/1.88          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.65/1.88      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.65/1.88  thf('5', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.65/1.88      inference('sup-', [status(thm)], ['3', '4'])).
% 1.65/1.88  thf('6', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('7', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf(redefinition_k1_partfun1, axiom,
% 1.65/1.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.65/1.88     ( ( ( v1_funct_1 @ E ) & 
% 1.65/1.88         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.88         ( v1_funct_1 @ F ) & 
% 1.65/1.88         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.65/1.88       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.65/1.88  thf('8', plain,
% 1.65/1.88      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.65/1.88         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.65/1.88          | ~ (v1_funct_1 @ X32)
% 1.65/1.88          | ~ (v1_funct_1 @ X35)
% 1.65/1.88          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.65/1.88          | ((k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 1.65/1.88              = (k5_relat_1 @ X32 @ X35)))),
% 1.65/1.88      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.65/1.88  thf('9', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.65/1.88            = (k5_relat_1 @ sk_C @ X0))
% 1.65/1.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.65/1.88          | ~ (v1_funct_1 @ X0)
% 1.65/1.88          | ~ (v1_funct_1 @ sk_C))),
% 1.65/1.88      inference('sup-', [status(thm)], ['7', '8'])).
% 1.65/1.88  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('11', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.65/1.88            = (k5_relat_1 @ sk_C @ X0))
% 1.65/1.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.65/1.88          | ~ (v1_funct_1 @ X0))),
% 1.65/1.88      inference('demod', [status(thm)], ['9', '10'])).
% 1.65/1.88  thf('12', plain,
% 1.65/1.88      ((~ (v1_funct_1 @ sk_D)
% 1.65/1.88        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.65/1.88            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.65/1.88      inference('sup-', [status(thm)], ['6', '11'])).
% 1.65/1.88  thf('13', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('14', plain,
% 1.65/1.88      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.65/1.88         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.65/1.88      inference('demod', [status(thm)], ['12', '13'])).
% 1.65/1.88  thf('15', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf(t24_funct_2, axiom,
% 1.65/1.88    (![A:$i,B:$i,C:$i]:
% 1.65/1.88     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.88       ( ![D:$i]:
% 1.65/1.88         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.65/1.88             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.65/1.88           ( ( r2_relset_1 @
% 1.65/1.88               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.65/1.88               ( k6_partfun1 @ B ) ) =>
% 1.65/1.88             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.65/1.88  thf('16', plain,
% 1.65/1.88      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.65/1.88         (~ (v1_funct_1 @ X39)
% 1.65/1.88          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 1.65/1.88          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.65/1.88          | ~ (r2_relset_1 @ X40 @ X40 @ 
% 1.65/1.88               (k1_partfun1 @ X40 @ X41 @ X41 @ X40 @ X39 @ X42) @ 
% 1.65/1.88               (k6_partfun1 @ X40))
% 1.65/1.88          | ((k2_relset_1 @ X41 @ X40 @ X42) = (X40))
% 1.65/1.88          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 1.65/1.88          | ~ (v1_funct_2 @ X42 @ X41 @ X40)
% 1.65/1.88          | ~ (v1_funct_1 @ X42))),
% 1.65/1.88      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.65/1.88  thf('17', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (v1_funct_1 @ X0)
% 1.65/1.88          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.65/1.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.65/1.88          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.65/1.88          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.88               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.65/1.88               (k6_partfun1 @ sk_A))
% 1.65/1.88          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.65/1.89          | ~ (v1_funct_1 @ sk_C))),
% 1.65/1.89      inference('sup-', [status(thm)], ['15', '16'])).
% 1.65/1.89  thf('18', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('20', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.65/1.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.65/1.89          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.65/1.89          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.89               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.65/1.89               (k6_partfun1 @ sk_A)))),
% 1.65/1.89      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.65/1.89  thf('21', plain,
% 1.65/1.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.65/1.89           (k6_partfun1 @ sk_A))
% 1.65/1.89        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.65/1.89        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.65/1.89        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.65/1.89        | ~ (v1_funct_1 @ sk_D))),
% 1.65/1.89      inference('sup-', [status(thm)], ['14', '20'])).
% 1.65/1.89  thf('22', plain,
% 1.65/1.89      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.89        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.65/1.89        (k6_partfun1 @ sk_A))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('23', plain,
% 1.65/1.89      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.65/1.89         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.65/1.89      inference('demod', [status(thm)], ['12', '13'])).
% 1.65/1.89  thf('24', plain,
% 1.65/1.89      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.65/1.89        (k6_partfun1 @ sk_A))),
% 1.65/1.89      inference('demod', [status(thm)], ['22', '23'])).
% 1.65/1.89  thf('25', plain,
% 1.65/1.89      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.65/1.89      inference('sup-', [status(thm)], ['3', '4'])).
% 1.65/1.89  thf('26', plain,
% 1.65/1.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('27', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('29', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.65/1.89      inference('demod', [status(thm)], ['21', '24', '25', '26', '27', '28'])).
% 1.65/1.89  thf('30', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 1.65/1.89      inference('demod', [status(thm)], ['5', '29'])).
% 1.65/1.89  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('33', plain,
% 1.65/1.89      ((((sk_A) != (sk_A))
% 1.65/1.89        | ~ (v2_funct_1 @ sk_D)
% 1.65/1.89        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.65/1.89        | ((sk_A) = (k1_xboole_0)))),
% 1.65/1.89      inference('demod', [status(thm)], ['2', '30', '31', '32'])).
% 1.65/1.89  thf('34', plain,
% 1.65/1.89      ((((sk_A) = (k1_xboole_0))
% 1.65/1.89        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.65/1.89        | ~ (v2_funct_1 @ sk_D))),
% 1.65/1.89      inference('simplify', [status(thm)], ['33'])).
% 1.65/1.89  thf('35', plain, (((sk_A) != (k1_xboole_0))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('36', plain,
% 1.65/1.89      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.65/1.89        | ~ (v2_funct_1 @ sk_D))),
% 1.65/1.89      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 1.65/1.89  thf('37', plain,
% 1.65/1.89      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.65/1.89         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.65/1.89      inference('demod', [status(thm)], ['12', '13'])).
% 1.65/1.89  thf('38', plain,
% 1.65/1.89      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.65/1.89        (k6_partfun1 @ sk_A))),
% 1.65/1.89      inference('demod', [status(thm)], ['22', '23'])).
% 1.65/1.89  thf('39', plain,
% 1.65/1.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('40', plain,
% 1.65/1.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf(dt_k1_partfun1, axiom,
% 1.65/1.89    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.65/1.89     ( ( ( v1_funct_1 @ E ) & 
% 1.65/1.89         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.89         ( v1_funct_1 @ F ) & 
% 1.65/1.89         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.65/1.89       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.65/1.89         ( m1_subset_1 @
% 1.65/1.89           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.65/1.89           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.65/1.89  thf('41', plain,
% 1.65/1.89      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.65/1.89         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.65/1.89          | ~ (v1_funct_1 @ X26)
% 1.65/1.89          | ~ (v1_funct_1 @ X29)
% 1.65/1.89          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.65/1.89          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 1.65/1.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 1.65/1.89      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.65/1.89  thf('42', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.89         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.65/1.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.65/1.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.65/1.89          | ~ (v1_funct_1 @ X1)
% 1.65/1.89          | ~ (v1_funct_1 @ sk_C))),
% 1.65/1.89      inference('sup-', [status(thm)], ['40', '41'])).
% 1.65/1.89  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('44', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.89         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.65/1.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.65/1.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.65/1.89          | ~ (v1_funct_1 @ X1))),
% 1.65/1.89      inference('demod', [status(thm)], ['42', '43'])).
% 1.65/1.89  thf('45', plain,
% 1.65/1.89      ((~ (v1_funct_1 @ sk_D)
% 1.65/1.89        | (m1_subset_1 @ 
% 1.65/1.89           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.65/1.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.65/1.89      inference('sup-', [status(thm)], ['39', '44'])).
% 1.65/1.89  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('47', plain,
% 1.65/1.89      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.65/1.89         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.65/1.89      inference('demod', [status(thm)], ['12', '13'])).
% 1.65/1.89  thf('48', plain,
% 1.65/1.89      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.65/1.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.65/1.89      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.65/1.89  thf(redefinition_r2_relset_1, axiom,
% 1.65/1.89    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.89     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.89       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.65/1.89  thf('49', plain,
% 1.65/1.89      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.65/1.89         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.65/1.89          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.65/1.89          | ((X21) = (X24))
% 1.65/1.89          | ~ (r2_relset_1 @ X22 @ X23 @ X21 @ X24))),
% 1.65/1.89      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.65/1.89  thf('50', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.65/1.89          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.65/1.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.65/1.89      inference('sup-', [status(thm)], ['48', '49'])).
% 1.65/1.89  thf('51', plain,
% 1.65/1.89      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.65/1.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.65/1.89        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.65/1.89      inference('sup-', [status(thm)], ['38', '50'])).
% 1.65/1.89  thf(t29_relset_1, axiom,
% 1.65/1.89    (![A:$i]:
% 1.65/1.89     ( m1_subset_1 @
% 1.65/1.89       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.65/1.89  thf('52', plain,
% 1.65/1.89      (![X25 : $i]:
% 1.65/1.89         (m1_subset_1 @ (k6_relat_1 @ X25) @ 
% 1.65/1.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 1.65/1.89      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.65/1.89  thf(redefinition_k6_partfun1, axiom,
% 1.65/1.89    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.65/1.89  thf('53', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 1.65/1.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.89  thf('54', plain,
% 1.65/1.89      (![X25 : $i]:
% 1.65/1.89         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 1.65/1.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 1.65/1.89      inference('demod', [status(thm)], ['52', '53'])).
% 1.65/1.89  thf('55', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.65/1.89      inference('demod', [status(thm)], ['51', '54'])).
% 1.65/1.89  thf('56', plain,
% 1.65/1.89      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.65/1.89         = (k6_partfun1 @ sk_A))),
% 1.65/1.89      inference('demod', [status(thm)], ['37', '55'])).
% 1.65/1.89  thf('57', plain,
% 1.65/1.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf(t30_funct_2, axiom,
% 1.65/1.89    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.89     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.89         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.65/1.89       ( ![E:$i]:
% 1.65/1.89         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.65/1.89             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.65/1.89           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.65/1.89               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.65/1.89             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.65/1.89               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.65/1.89  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.65/1.89  thf(zf_stmt_2, axiom,
% 1.65/1.89    (![C:$i,B:$i]:
% 1.65/1.89     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.65/1.89       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.65/1.89  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.65/1.89  thf(zf_stmt_4, axiom,
% 1.65/1.89    (![E:$i,D:$i]:
% 1.65/1.89     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.65/1.89  thf(zf_stmt_5, axiom,
% 1.65/1.89    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.89     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.65/1.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.89       ( ![E:$i]:
% 1.65/1.89         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.65/1.89             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.65/1.89           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.65/1.89               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.65/1.89             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.65/1.89  thf('58', plain,
% 1.65/1.89      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.65/1.89         (~ (v1_funct_1 @ X47)
% 1.65/1.89          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 1.65/1.89          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 1.65/1.89          | (zip_tseitin_0 @ X47 @ X50)
% 1.65/1.89          | ~ (v2_funct_1 @ (k1_partfun1 @ X51 @ X48 @ X48 @ X49 @ X50 @ X47))
% 1.65/1.89          | (zip_tseitin_1 @ X49 @ X48)
% 1.65/1.89          | ((k2_relset_1 @ X51 @ X48 @ X50) != (X48))
% 1.65/1.89          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X48)))
% 1.65/1.89          | ~ (v1_funct_2 @ X50 @ X51 @ X48)
% 1.65/1.89          | ~ (v1_funct_1 @ X50))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.65/1.89  thf('59', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]:
% 1.65/1.89         (~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.65/1.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.65/1.89          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.65/1.89          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.65/1.89          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.65/1.89          | (zip_tseitin_0 @ sk_D @ X0)
% 1.65/1.89          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.65/1.89          | ~ (v1_funct_1 @ sk_D))),
% 1.65/1.89      inference('sup-', [status(thm)], ['57', '58'])).
% 1.65/1.89  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('62', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]:
% 1.65/1.89         (~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.65/1.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.65/1.89          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.65/1.89          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.65/1.89          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.65/1.89          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.65/1.89      inference('demod', [status(thm)], ['59', '60', '61'])).
% 1.65/1.89  thf('63', plain,
% 1.65/1.89      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.65/1.89        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.65/1.89        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.65/1.89        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.65/1.89        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.65/1.89        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.65/1.89        | ~ (v1_funct_1 @ sk_C))),
% 1.65/1.89      inference('sup-', [status(thm)], ['56', '62'])).
% 1.65/1.89  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.65/1.89  thf('64', plain, (![X14 : $i]: (v2_funct_1 @ (k6_relat_1 @ X14))),
% 1.65/1.89      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.65/1.89  thf('65', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 1.65/1.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.89  thf('66', plain, (![X14 : $i]: (v2_funct_1 @ (k6_partfun1 @ X14))),
% 1.65/1.89      inference('demod', [status(thm)], ['64', '65'])).
% 1.65/1.89  thf('67', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('68', plain,
% 1.65/1.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('69', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('71', plain,
% 1.65/1.89      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.65/1.89        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.65/1.89        | ((sk_B) != (sk_B)))),
% 1.65/1.89      inference('demod', [status(thm)], ['63', '66', '67', '68', '69', '70'])).
% 1.65/1.89  thf('72', plain,
% 1.65/1.89      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.65/1.89      inference('simplify', [status(thm)], ['71'])).
% 1.65/1.89  thf('73', plain,
% 1.65/1.89      (![X45 : $i, X46 : $i]:
% 1.65/1.89         (((X45) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X45 @ X46))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.65/1.89  thf('74', plain,
% 1.65/1.89      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.65/1.89      inference('sup-', [status(thm)], ['72', '73'])).
% 1.65/1.89  thf('75', plain, (((sk_A) != (k1_xboole_0))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('76', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.65/1.89      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 1.65/1.89  thf('77', plain,
% 1.65/1.89      (![X43 : $i, X44 : $i]:
% 1.65/1.89         ((v2_funct_1 @ X44) | ~ (zip_tseitin_0 @ X44 @ X43))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.65/1.89  thf('78', plain, ((v2_funct_1 @ sk_D)),
% 1.65/1.89      inference('sup-', [status(thm)], ['76', '77'])).
% 1.65/1.89  thf('79', plain,
% 1.65/1.89      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.65/1.89      inference('demod', [status(thm)], ['36', '78'])).
% 1.65/1.89  thf('80', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.65/1.89      inference('demod', [status(thm)], ['51', '54'])).
% 1.65/1.89  thf(t64_funct_1, axiom,
% 1.65/1.89    (![A:$i]:
% 1.65/1.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.89       ( ![B:$i]:
% 1.65/1.89         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.65/1.89           ( ( ( v2_funct_1 @ A ) & 
% 1.65/1.89               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.65/1.89               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.65/1.89             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.65/1.89  thf('81', plain,
% 1.65/1.89      (![X16 : $i, X17 : $i]:
% 1.65/1.89         (~ (v1_relat_1 @ X16)
% 1.65/1.89          | ~ (v1_funct_1 @ X16)
% 1.65/1.89          | ((X16) = (k2_funct_1 @ X17))
% 1.65/1.89          | ((k5_relat_1 @ X16 @ X17) != (k6_relat_1 @ (k2_relat_1 @ X17)))
% 1.65/1.89          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X17))
% 1.65/1.89          | ~ (v2_funct_1 @ X17)
% 1.65/1.89          | ~ (v1_funct_1 @ X17)
% 1.65/1.89          | ~ (v1_relat_1 @ X17))),
% 1.65/1.89      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.65/1.89  thf('82', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 1.65/1.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.89  thf('83', plain,
% 1.65/1.89      (![X16 : $i, X17 : $i]:
% 1.65/1.89         (~ (v1_relat_1 @ X16)
% 1.65/1.89          | ~ (v1_funct_1 @ X16)
% 1.65/1.89          | ((X16) = (k2_funct_1 @ X17))
% 1.65/1.89          | ((k5_relat_1 @ X16 @ X17) != (k6_partfun1 @ (k2_relat_1 @ X17)))
% 1.65/1.89          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X17))
% 1.65/1.89          | ~ (v2_funct_1 @ X17)
% 1.65/1.89          | ~ (v1_funct_1 @ X17)
% 1.65/1.89          | ~ (v1_relat_1 @ X17))),
% 1.65/1.89      inference('demod', [status(thm)], ['81', '82'])).
% 1.65/1.89  thf('84', plain,
% 1.65/1.89      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.65/1.89        | ~ (v1_relat_1 @ sk_D)
% 1.65/1.89        | ~ (v1_funct_1 @ sk_D)
% 1.65/1.89        | ~ (v2_funct_1 @ sk_D)
% 1.65/1.89        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.65/1.89        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.65/1.89        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.89        | ~ (v1_relat_1 @ sk_C))),
% 1.65/1.89      inference('sup-', [status(thm)], ['80', '83'])).
% 1.65/1.89  thf('85', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.65/1.89      inference('demod', [status(thm)], ['21', '24', '25', '26', '27', '28'])).
% 1.65/1.89  thf('86', plain,
% 1.65/1.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf(cc2_relat_1, axiom,
% 1.65/1.89    (![A:$i]:
% 1.65/1.89     ( ( v1_relat_1 @ A ) =>
% 1.65/1.89       ( ![B:$i]:
% 1.65/1.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.65/1.89  thf('87', plain,
% 1.65/1.89      (![X3 : $i, X4 : $i]:
% 1.65/1.89         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.65/1.89          | (v1_relat_1 @ X3)
% 1.65/1.89          | ~ (v1_relat_1 @ X4))),
% 1.65/1.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.65/1.89  thf('88', plain,
% 1.65/1.89      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.65/1.89      inference('sup-', [status(thm)], ['86', '87'])).
% 1.65/1.89  thf(fc6_relat_1, axiom,
% 1.65/1.89    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.65/1.89  thf('89', plain,
% 1.65/1.89      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.65/1.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.65/1.89  thf('90', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.89      inference('demod', [status(thm)], ['88', '89'])).
% 1.65/1.89  thf('91', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('92', plain,
% 1.65/1.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('93', plain,
% 1.65/1.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.65/1.89         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 1.65/1.89          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.65/1.89      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.65/1.89  thf('94', plain,
% 1.65/1.89      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.65/1.89      inference('sup-', [status(thm)], ['92', '93'])).
% 1.65/1.89  thf('95', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('96', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.89      inference('sup+', [status(thm)], ['94', '95'])).
% 1.65/1.89  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('98', plain,
% 1.65/1.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('99', plain,
% 1.65/1.89      (![X3 : $i, X4 : $i]:
% 1.65/1.89         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.65/1.89          | (v1_relat_1 @ X3)
% 1.65/1.89          | ~ (v1_relat_1 @ X4))),
% 1.65/1.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.65/1.89  thf('100', plain,
% 1.65/1.89      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.65/1.89      inference('sup-', [status(thm)], ['98', '99'])).
% 1.65/1.89  thf('101', plain,
% 1.65/1.89      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.65/1.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.65/1.89  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.89      inference('demod', [status(thm)], ['100', '101'])).
% 1.65/1.89  thf('103', plain,
% 1.65/1.89      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 1.65/1.89        | ~ (v2_funct_1 @ sk_D)
% 1.65/1.89        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.65/1.89        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.65/1.89      inference('demod', [status(thm)],
% 1.65/1.89                ['84', '85', '90', '91', '96', '97', '102'])).
% 1.65/1.89  thf('104', plain,
% 1.65/1.89      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.65/1.89        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.65/1.89        | ~ (v2_funct_1 @ sk_D))),
% 1.65/1.89      inference('simplify', [status(thm)], ['103'])).
% 1.65/1.89  thf('105', plain, ((v2_funct_1 @ sk_D)),
% 1.65/1.89      inference('sup-', [status(thm)], ['76', '77'])).
% 1.65/1.89  thf('106', plain,
% 1.65/1.89      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 1.65/1.89      inference('demod', [status(thm)], ['104', '105'])).
% 1.65/1.89  thf(t55_funct_1, axiom,
% 1.65/1.89    (![A:$i]:
% 1.65/1.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.89       ( ( v2_funct_1 @ A ) =>
% 1.65/1.89         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.65/1.89           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.65/1.89  thf('107', plain,
% 1.65/1.89      (![X15 : $i]:
% 1.65/1.89         (~ (v2_funct_1 @ X15)
% 1.65/1.89          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 1.65/1.89          | ~ (v1_funct_1 @ X15)
% 1.65/1.89          | ~ (v1_relat_1 @ X15))),
% 1.65/1.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.89  thf('108', plain,
% 1.65/1.89      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.65/1.89      inference('demod', [status(thm)], ['36', '78'])).
% 1.65/1.89  thf(dt_k2_funct_1, axiom,
% 1.65/1.89    (![A:$i]:
% 1.65/1.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.89       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.65/1.89         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.65/1.89  thf('109', plain,
% 1.65/1.89      (![X13 : $i]:
% 1.65/1.89         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 1.65/1.89          | ~ (v1_funct_1 @ X13)
% 1.65/1.89          | ~ (v1_relat_1 @ X13))),
% 1.65/1.89      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.89  thf('110', plain,
% 1.65/1.89      (![X13 : $i]:
% 1.65/1.89         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 1.65/1.89          | ~ (v1_funct_1 @ X13)
% 1.65/1.89          | ~ (v1_relat_1 @ X13))),
% 1.65/1.89      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.89  thf('111', plain,
% 1.65/1.89      (![X13 : $i]:
% 1.65/1.89         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 1.65/1.89          | ~ (v1_funct_1 @ X13)
% 1.65/1.89          | ~ (v1_relat_1 @ X13))),
% 1.65/1.89      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.89  thf('112', plain,
% 1.65/1.89      (![X15 : $i]:
% 1.65/1.89         (~ (v2_funct_1 @ X15)
% 1.65/1.89          | ((k2_relat_1 @ X15) = (k1_relat_1 @ (k2_funct_1 @ X15)))
% 1.65/1.89          | ~ (v1_funct_1 @ X15)
% 1.65/1.89          | ~ (v1_relat_1 @ X15))),
% 1.65/1.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.89  thf(d10_xboole_0, axiom,
% 1.65/1.89    (![A:$i,B:$i]:
% 1.65/1.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.65/1.89  thf('113', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.65/1.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.65/1.89  thf('114', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.65/1.89      inference('simplify', [status(thm)], ['113'])).
% 1.65/1.89  thf(d18_relat_1, axiom,
% 1.65/1.89    (![A:$i,B:$i]:
% 1.65/1.89     ( ( v1_relat_1 @ B ) =>
% 1.65/1.89       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.65/1.89  thf('115', plain,
% 1.65/1.89      (![X5 : $i, X6 : $i]:
% 1.65/1.89         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.65/1.89          | (v4_relat_1 @ X5 @ X6)
% 1.65/1.89          | ~ (v1_relat_1 @ X5))),
% 1.65/1.89      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.89  thf('116', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.65/1.89      inference('sup-', [status(thm)], ['114', '115'])).
% 1.65/1.89  thf('117', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.65/1.89          | ~ (v1_relat_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v2_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.65/1.89      inference('sup+', [status(thm)], ['112', '116'])).
% 1.65/1.89  thf('118', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (~ (v1_relat_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v2_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_relat_1 @ X0)
% 1.65/1.89          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.65/1.89      inference('sup-', [status(thm)], ['111', '117'])).
% 1.65/1.89  thf('119', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.65/1.89          | ~ (v2_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_relat_1 @ X0))),
% 1.65/1.89      inference('simplify', [status(thm)], ['118'])).
% 1.65/1.89  thf('120', plain,
% 1.65/1.89      (![X5 : $i, X6 : $i]:
% 1.65/1.89         (~ (v4_relat_1 @ X5 @ X6)
% 1.65/1.89          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.65/1.89          | ~ (v1_relat_1 @ X5))),
% 1.65/1.89      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.89  thf('121', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (~ (v1_relat_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v2_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.65/1.89          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 1.65/1.89      inference('sup-', [status(thm)], ['119', '120'])).
% 1.65/1.89  thf('122', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (~ (v1_relat_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_1 @ X0)
% 1.65/1.89          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 1.65/1.89          | ~ (v2_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_relat_1 @ X0))),
% 1.65/1.89      inference('sup-', [status(thm)], ['110', '121'])).
% 1.65/1.89  thf('123', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (~ (v2_funct_1 @ X0)
% 1.65/1.89          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 1.65/1.89          | ~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_relat_1 @ X0))),
% 1.65/1.89      inference('simplify', [status(thm)], ['122'])).
% 1.65/1.89  thf(t47_relat_1, axiom,
% 1.65/1.89    (![A:$i]:
% 1.65/1.89     ( ( v1_relat_1 @ A ) =>
% 1.65/1.89       ( ![B:$i]:
% 1.65/1.89         ( ( v1_relat_1 @ B ) =>
% 1.65/1.89           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 1.65/1.89             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.65/1.89  thf('124', plain,
% 1.65/1.89      (![X9 : $i, X10 : $i]:
% 1.65/1.89         (~ (v1_relat_1 @ X9)
% 1.65/1.89          | ((k2_relat_1 @ (k5_relat_1 @ X9 @ X10)) = (k2_relat_1 @ X10))
% 1.65/1.89          | ~ (r1_tarski @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X9))
% 1.65/1.89          | ~ (v1_relat_1 @ X10))),
% 1.65/1.89      inference('cnf', [status(esa)], [t47_relat_1])).
% 1.65/1.89  thf('125', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (~ (v1_relat_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v2_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.65/1.89          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 1.65/1.89              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.89          | ~ (v1_relat_1 @ X0))),
% 1.65/1.89      inference('sup-', [status(thm)], ['123', '124'])).
% 1.65/1.89  thf('126', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 1.65/1.89            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.65/1.89          | ~ (v2_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_relat_1 @ X0))),
% 1.65/1.89      inference('simplify', [status(thm)], ['125'])).
% 1.65/1.89  thf('127', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (~ (v1_relat_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_relat_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v2_funct_1 @ X0)
% 1.65/1.89          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 1.65/1.89              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.65/1.89      inference('sup-', [status(thm)], ['109', '126'])).
% 1.65/1.89  thf('128', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 1.65/1.89            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.89          | ~ (v2_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_relat_1 @ X0))),
% 1.65/1.89      inference('simplify', [status(thm)], ['127'])).
% 1.65/1.89  thf('129', plain,
% 1.65/1.89      ((((k2_relat_1 @ (k6_partfun1 @ sk_B))
% 1.65/1.89          = (k2_relat_1 @ (k2_funct_1 @ sk_D)))
% 1.65/1.89        | ~ (v1_relat_1 @ sk_D)
% 1.65/1.89        | ~ (v1_funct_1 @ sk_D)
% 1.65/1.89        | ~ (v2_funct_1 @ sk_D))),
% 1.65/1.89      inference('sup+', [status(thm)], ['108', '128'])).
% 1.65/1.89  thf(t71_relat_1, axiom,
% 1.65/1.89    (![A:$i]:
% 1.65/1.89     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.65/1.89       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.65/1.89  thf('130', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 1.65/1.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.65/1.89  thf('131', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 1.65/1.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.89  thf('132', plain,
% 1.65/1.89      (![X12 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 1.65/1.89      inference('demod', [status(thm)], ['130', '131'])).
% 1.65/1.89  thf('133', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.89      inference('demod', [status(thm)], ['88', '89'])).
% 1.65/1.89  thf('134', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('135', plain, ((v2_funct_1 @ sk_D)),
% 1.65/1.89      inference('sup-', [status(thm)], ['76', '77'])).
% 1.65/1.89  thf('136', plain, (((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_D)))),
% 1.65/1.89      inference('demod', [status(thm)], ['129', '132', '133', '134', '135'])).
% 1.65/1.89  thf('137', plain,
% 1.65/1.89      ((((sk_B) = (k1_relat_1 @ sk_D))
% 1.65/1.89        | ~ (v1_relat_1 @ sk_D)
% 1.65/1.89        | ~ (v1_funct_1 @ sk_D)
% 1.65/1.89        | ~ (v2_funct_1 @ sk_D))),
% 1.65/1.89      inference('sup+', [status(thm)], ['107', '136'])).
% 1.65/1.89  thf('138', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.89      inference('demod', [status(thm)], ['88', '89'])).
% 1.65/1.89  thf('139', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('140', plain, ((v2_funct_1 @ sk_D)),
% 1.65/1.89      inference('sup-', [status(thm)], ['76', '77'])).
% 1.65/1.89  thf('141', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.65/1.89      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 1.65/1.89  thf('142', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 1.65/1.89      inference('demod', [status(thm)], ['106', '141'])).
% 1.65/1.89  thf('143', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.65/1.89      inference('simplify', [status(thm)], ['142'])).
% 1.65/1.89  thf('144', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.65/1.89      inference('demod', [status(thm)], ['79', '143'])).
% 1.65/1.89  thf('145', plain,
% 1.65/1.89      (![X16 : $i, X17 : $i]:
% 1.65/1.89         (~ (v1_relat_1 @ X16)
% 1.65/1.89          | ~ (v1_funct_1 @ X16)
% 1.65/1.89          | ((X16) = (k2_funct_1 @ X17))
% 1.65/1.89          | ((k5_relat_1 @ X16 @ X17) != (k6_partfun1 @ (k2_relat_1 @ X17)))
% 1.65/1.89          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X17))
% 1.65/1.89          | ~ (v2_funct_1 @ X17)
% 1.65/1.89          | ~ (v1_funct_1 @ X17)
% 1.65/1.89          | ~ (v1_relat_1 @ X17))),
% 1.65/1.89      inference('demod', [status(thm)], ['81', '82'])).
% 1.65/1.89  thf('146', plain,
% 1.65/1.89      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.65/1.89        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.89        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.89        | ~ (v2_funct_1 @ sk_C)
% 1.65/1.89        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 1.65/1.89        | ((sk_D) = (k2_funct_1 @ sk_C))
% 1.65/1.89        | ~ (v1_funct_1 @ sk_D)
% 1.65/1.89        | ~ (v1_relat_1 @ sk_D))),
% 1.65/1.89      inference('sup-', [status(thm)], ['144', '145'])).
% 1.65/1.89  thf('147', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.89      inference('sup+', [status(thm)], ['94', '95'])).
% 1.65/1.89  thf('148', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.89      inference('demod', [status(thm)], ['100', '101'])).
% 1.65/1.89  thf('149', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('150', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('151', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.65/1.89      inference('demod', [status(thm)], ['21', '24', '25', '26', '27', '28'])).
% 1.65/1.89  thf('152', plain,
% 1.65/1.89      (![X15 : $i]:
% 1.65/1.89         (~ (v2_funct_1 @ X15)
% 1.65/1.89          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 1.65/1.89          | ~ (v1_funct_1 @ X15)
% 1.65/1.89          | ~ (v1_relat_1 @ X15))),
% 1.65/1.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.89  thf('153', plain,
% 1.65/1.89      (![X13 : $i]:
% 1.65/1.89         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 1.65/1.89          | ~ (v1_funct_1 @ X13)
% 1.65/1.89          | ~ (v1_relat_1 @ X13))),
% 1.65/1.89      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.89  thf('154', plain,
% 1.65/1.89      (![X15 : $i]:
% 1.65/1.89         (~ (v2_funct_1 @ X15)
% 1.65/1.89          | ((k2_relat_1 @ X15) = (k1_relat_1 @ (k2_funct_1 @ X15)))
% 1.65/1.89          | ~ (v1_funct_1 @ X15)
% 1.65/1.89          | ~ (v1_relat_1 @ X15))),
% 1.65/1.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.89  thf('155', plain,
% 1.65/1.89      (![X13 : $i]:
% 1.65/1.89         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 1.65/1.89          | ~ (v1_funct_1 @ X13)
% 1.65/1.89          | ~ (v1_relat_1 @ X13))),
% 1.65/1.89      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.89  thf('156', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.89      inference('sup+', [status(thm)], ['94', '95'])).
% 1.65/1.89  thf('157', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.65/1.89          | ~ (v2_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_funct_1 @ X0)
% 1.65/1.89          | ~ (v1_relat_1 @ X0))),
% 1.65/1.89      inference('simplify', [status(thm)], ['118'])).
% 1.65/1.89  thf('158', plain,
% 1.65/1.89      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.65/1.89        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.89        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.89        | ~ (v2_funct_1 @ sk_C))),
% 1.65/1.89      inference('sup+', [status(thm)], ['156', '157'])).
% 1.65/1.89  thf('159', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.89      inference('demod', [status(thm)], ['100', '101'])).
% 1.65/1.89  thf('160', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('161', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('162', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.65/1.89      inference('demod', [status(thm)], ['158', '159', '160', '161'])).
% 1.65/1.89  thf('163', plain,
% 1.65/1.89      (![X5 : $i, X6 : $i]:
% 1.65/1.89         (~ (v4_relat_1 @ X5 @ X6)
% 1.65/1.89          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.65/1.89          | ~ (v1_relat_1 @ X5))),
% 1.65/1.89      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.89  thf('164', plain,
% 1.65/1.89      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.65/1.89        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.65/1.89      inference('sup-', [status(thm)], ['162', '163'])).
% 1.65/1.89  thf('165', plain,
% 1.65/1.89      ((~ (v1_relat_1 @ sk_C)
% 1.65/1.89        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.89        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.65/1.89      inference('sup-', [status(thm)], ['155', '164'])).
% 1.65/1.89  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.89      inference('demod', [status(thm)], ['100', '101'])).
% 1.65/1.89  thf('167', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('168', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.65/1.89      inference('demod', [status(thm)], ['165', '166', '167'])).
% 1.65/1.89  thf('169', plain,
% 1.65/1.89      (![X0 : $i, X2 : $i]:
% 1.65/1.89         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.65/1.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.65/1.89  thf('170', plain,
% 1.65/1.89      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.65/1.89        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.65/1.89      inference('sup-', [status(thm)], ['168', '169'])).
% 1.65/1.89  thf('171', plain,
% 1.65/1.89      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.65/1.89        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.89        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.89        | ~ (v2_funct_1 @ sk_C)
% 1.65/1.89        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.65/1.89      inference('sup-', [status(thm)], ['154', '170'])).
% 1.65/1.89  thf('172', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.89      inference('sup+', [status(thm)], ['94', '95'])).
% 1.65/1.89  thf('173', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.65/1.89      inference('simplify', [status(thm)], ['113'])).
% 1.65/1.89  thf('174', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.89      inference('demod', [status(thm)], ['100', '101'])).
% 1.65/1.89  thf('175', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('176', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('177', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.89      inference('demod', [status(thm)],
% 1.65/1.89                ['171', '172', '173', '174', '175', '176'])).
% 1.65/1.89  thf('178', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.89      inference('sup+', [status(thm)], ['94', '95'])).
% 1.65/1.89  thf('179', plain,
% 1.65/1.89      (![X9 : $i, X10 : $i]:
% 1.65/1.89         (~ (v1_relat_1 @ X9)
% 1.65/1.89          | ((k2_relat_1 @ (k5_relat_1 @ X9 @ X10)) = (k2_relat_1 @ X10))
% 1.65/1.89          | ~ (r1_tarski @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X9))
% 1.65/1.89          | ~ (v1_relat_1 @ X10))),
% 1.65/1.89      inference('cnf', [status(esa)], [t47_relat_1])).
% 1.65/1.89  thf('180', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 1.65/1.89          | ~ (v1_relat_1 @ X0)
% 1.65/1.89          | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ X0)) = (k2_relat_1 @ X0))
% 1.65/1.89          | ~ (v1_relat_1 @ sk_C))),
% 1.65/1.89      inference('sup-', [status(thm)], ['178', '179'])).
% 1.65/1.89  thf('181', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.89      inference('demod', [status(thm)], ['100', '101'])).
% 1.65/1.89  thf('182', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 1.65/1.89          | ~ (v1_relat_1 @ X0)
% 1.65/1.89          | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ X0)) = (k2_relat_1 @ X0)))),
% 1.65/1.89      inference('demod', [status(thm)], ['180', '181'])).
% 1.65/1.89  thf('183', plain,
% 1.65/1.89      ((~ (r1_tarski @ sk_B @ sk_B)
% 1.65/1.89        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 1.65/1.89            = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.65/1.89        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.89      inference('sup-', [status(thm)], ['177', '182'])).
% 1.65/1.89  thf('184', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.65/1.89      inference('simplify', [status(thm)], ['113'])).
% 1.65/1.89  thf('185', plain,
% 1.65/1.89      ((((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 1.65/1.89          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.65/1.89        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.89      inference('demod', [status(thm)], ['183', '184'])).
% 1.65/1.89  thf('186', plain,
% 1.65/1.89      ((~ (v1_relat_1 @ sk_C)
% 1.65/1.89        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.89        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 1.65/1.89            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.65/1.89      inference('sup-', [status(thm)], ['153', '185'])).
% 1.65/1.89  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.89      inference('demod', [status(thm)], ['100', '101'])).
% 1.65/1.89  thf('188', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('189', plain,
% 1.65/1.89      (((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 1.65/1.89         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.89      inference('demod', [status(thm)], ['186', '187', '188'])).
% 1.65/1.89  thf('190', plain,
% 1.65/1.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('191', plain,
% 1.65/1.89      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.65/1.89         (((X52) = (k1_xboole_0))
% 1.65/1.89          | ~ (v1_funct_1 @ X53)
% 1.65/1.89          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 1.65/1.89          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 1.65/1.89          | ((k5_relat_1 @ X53 @ (k2_funct_1 @ X53)) = (k6_partfun1 @ X54))
% 1.65/1.89          | ~ (v2_funct_1 @ X53)
% 1.65/1.89          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 1.65/1.89      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.65/1.89  thf('192', plain,
% 1.65/1.89      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.65/1.89        | ~ (v2_funct_1 @ sk_C)
% 1.65/1.89        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.65/1.89        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.65/1.89        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.89        | ((sk_B) = (k1_xboole_0)))),
% 1.65/1.89      inference('sup-', [status(thm)], ['190', '191'])).
% 1.65/1.89  thf('193', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('194', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('195', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('196', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('197', plain,
% 1.65/1.89      ((((sk_B) != (sk_B))
% 1.65/1.89        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.65/1.89        | ((sk_B) = (k1_xboole_0)))),
% 1.65/1.89      inference('demod', [status(thm)], ['192', '193', '194', '195', '196'])).
% 1.65/1.89  thf('198', plain,
% 1.65/1.89      ((((sk_B) = (k1_xboole_0))
% 1.65/1.89        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 1.65/1.89      inference('simplify', [status(thm)], ['197'])).
% 1.65/1.89  thf('199', plain, (((sk_B) != (k1_xboole_0))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('200', plain,
% 1.65/1.89      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.65/1.89      inference('simplify_reflect-', [status(thm)], ['198', '199'])).
% 1.65/1.89  thf('201', plain,
% 1.65/1.89      (![X12 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 1.65/1.89      inference('demod', [status(thm)], ['130', '131'])).
% 1.65/1.89  thf('202', plain, (((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.89      inference('demod', [status(thm)], ['189', '200', '201'])).
% 1.65/1.89  thf('203', plain,
% 1.65/1.89      ((((sk_A) = (k1_relat_1 @ sk_C))
% 1.65/1.89        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.89        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.89        | ~ (v2_funct_1 @ sk_C))),
% 1.65/1.89      inference('sup+', [status(thm)], ['152', '202'])).
% 1.65/1.89  thf('204', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.89      inference('demod', [status(thm)], ['100', '101'])).
% 1.65/1.89  thf('205', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('206', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('207', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.65/1.89      inference('demod', [status(thm)], ['203', '204', '205', '206'])).
% 1.65/1.89  thf('208', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('209', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.89      inference('demod', [status(thm)], ['88', '89'])).
% 1.65/1.89  thf('210', plain,
% 1.65/1.89      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 1.65/1.89        | ((sk_A) != (sk_A))
% 1.65/1.89        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.65/1.89      inference('demod', [status(thm)],
% 1.65/1.89                ['146', '147', '148', '149', '150', '151', '207', '208', '209'])).
% 1.65/1.89  thf('211', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.65/1.89      inference('simplify', [status(thm)], ['210'])).
% 1.65/1.89  thf('212', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('213', plain, ($false),
% 1.65/1.89      inference('simplify_reflect-', [status(thm)], ['211', '212'])).
% 1.65/1.89  
% 1.65/1.89  % SZS output end Refutation
% 1.65/1.89  
% 1.65/1.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
