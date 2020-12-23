%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dKUxKDZa1Z

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:06 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  273 (1267 expanded)
%              Number of leaves         :   49 ( 394 expanded)
%              Depth                    :   25
%              Number of atoms          : 2641 (26415 expanded)
%              Number of equality atoms :  188 (1855 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

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
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_partfun1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','14','15','16'])).

thf('18',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('32',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('42',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('43',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','44'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('46',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('47',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('48',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','49'])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( zip_tseitin_0 @ X43 @ X46 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43 ) )
      | ( zip_tseitin_1 @ X45 @ X44 )
      | ( ( k2_relset_1 @ X47 @ X44 @ X46 )
       != X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('53',plain,(
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
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('58',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('59',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('60',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['57','60','61','62','63','64'])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('68',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v2_funct_1 @ X40 )
      | ~ ( zip_tseitin_0 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('72',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['20','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('75',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('76',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('77',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('78',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('80',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('82',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('84',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('85',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('86',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('87',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('91',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('92',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('93',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('101',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('102',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('103',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('105',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('108',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('109',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['103','111'])).

thf('113',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['78','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('121',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('122',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('123',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
      = ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('126',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('128',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( k4_relat_1 @ sk_D )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['119','126','127','128'])).

thf('130',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('131',plain,
    ( ( k4_relat_1 @ sk_D )
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['73','131'])).

thf('133',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf('134',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X13 @ ( k2_funct_1 @ X13 ) ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['132','136'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('138',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('139',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('140',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('142',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('144',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['137','140','141','142','143'])).

thf('145',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('146',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('148',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X49 ) @ X49 )
        = ( k6_partfun1 @ X48 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('150',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('155',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('157',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('159',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('161',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('162',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('163',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['160','163'])).

thf('165',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['153','154'])).

thf('166',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['153','154'])).

thf('168',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['159','166','167','168','169'])).

thf('171',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['150','151','152','170','171','172'])).

thf('174',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['159','166','167','168','169'])).

thf('180',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('181',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['153','154'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['153','154'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['178','184','185'])).

thf('187',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['147','186'])).

thf('188',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('189',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['159','166','167','168','169'])).

thf('190',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X13 @ ( k2_funct_1 @ X13 ) ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('191',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['153','154'])).

thf('193',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('196',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('198',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['159','166','167','168','169'])).

thf('202',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['198','199','200','201','202','203'])).

thf('205',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('209',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['195','207','208'])).

thf('210',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['188','209'])).

thf('211',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('212',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['187','210','211'])).

thf('213',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('214',plain,
    ( ( k4_relat_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['146','212','213'])).

thf('215',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('216',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( sk_D
     != ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['153','154'])).

thf('219',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['217','218','219','220'])).

thf('222',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['214','221'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dKUxKDZa1Z
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:21:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.72/1.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.72/1.91  % Solved by: fo/fo7.sh
% 1.72/1.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.72/1.91  % done 1527 iterations in 1.421s
% 1.72/1.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.72/1.91  % SZS output start Refutation
% 1.72/1.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.72/1.91  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.72/1.91  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.72/1.91  thf(sk_B_type, type, sk_B: $i).
% 1.72/1.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.72/1.91  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.72/1.91  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.72/1.91  thf(sk_D_type, type, sk_D: $i).
% 1.72/1.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.72/1.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.72/1.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.72/1.91  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.72/1.91  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.72/1.91  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.72/1.91  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.72/1.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.72/1.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.72/1.91  thf(sk_A_type, type, sk_A: $i).
% 1.72/1.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.72/1.91  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.72/1.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.72/1.91  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.72/1.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.72/1.91  thf(sk_C_type, type, sk_C: $i).
% 1.72/1.91  thf(t36_funct_2, conjecture,
% 1.72/1.91    (![A:$i,B:$i,C:$i]:
% 1.72/1.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.72/1.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.91       ( ![D:$i]:
% 1.72/1.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.72/1.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.72/1.91           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.72/1.91               ( r2_relset_1 @
% 1.72/1.91                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.72/1.91                 ( k6_partfun1 @ A ) ) & 
% 1.72/1.91               ( v2_funct_1 @ C ) ) =>
% 1.72/1.91             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.72/1.91               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.72/1.91  thf(zf_stmt_0, negated_conjecture,
% 1.72/1.91    (~( ![A:$i,B:$i,C:$i]:
% 1.72/1.91        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.72/1.91            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.91          ( ![D:$i]:
% 1.72/1.91            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.72/1.91                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.72/1.91              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.72/1.91                  ( r2_relset_1 @
% 1.72/1.91                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.72/1.91                    ( k6_partfun1 @ A ) ) & 
% 1.72/1.91                  ( v2_funct_1 @ C ) ) =>
% 1.72/1.91                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.72/1.91                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.72/1.91    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.72/1.91  thf('0', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf(t35_funct_2, axiom,
% 1.72/1.91    (![A:$i,B:$i,C:$i]:
% 1.72/1.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.72/1.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.91       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.72/1.91         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.72/1.91           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.72/1.91             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.72/1.91  thf('1', plain,
% 1.72/1.91      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.72/1.91         (((X48) = (k1_xboole_0))
% 1.72/1.91          | ~ (v1_funct_1 @ X49)
% 1.72/1.91          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 1.72/1.91          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 1.72/1.91          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_partfun1 @ X50))
% 1.72/1.91          | ~ (v2_funct_1 @ X49)
% 1.72/1.91          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 1.72/1.91      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.72/1.91  thf('2', plain,
% 1.72/1.91      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.72/1.91        | ~ (v2_funct_1 @ sk_D)
% 1.72/1.91        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.72/1.91        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.72/1.91        | ~ (v1_funct_1 @ sk_D)
% 1.72/1.91        | ((sk_A) = (k1_xboole_0)))),
% 1.72/1.91      inference('sup-', [status(thm)], ['0', '1'])).
% 1.72/1.91  thf('3', plain,
% 1.72/1.91      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.72/1.91        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.72/1.91        (k6_partfun1 @ sk_A))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('4', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf(t24_funct_2, axiom,
% 1.72/1.91    (![A:$i,B:$i,C:$i]:
% 1.72/1.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.72/1.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.91       ( ![D:$i]:
% 1.72/1.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.72/1.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.72/1.91           ( ( r2_relset_1 @
% 1.72/1.91               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.72/1.91               ( k6_partfun1 @ B ) ) =>
% 1.72/1.91             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.72/1.91  thf('5', plain,
% 1.72/1.91      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.72/1.91         (~ (v1_funct_1 @ X35)
% 1.72/1.91          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 1.72/1.91          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.72/1.91          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 1.72/1.91               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 1.72/1.91               (k6_partfun1 @ X36))
% 1.72/1.91          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 1.72/1.91          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 1.72/1.91          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 1.72/1.91          | ~ (v1_funct_1 @ X38))),
% 1.72/1.91      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.72/1.91  thf('6', plain,
% 1.72/1.91      (![X0 : $i]:
% 1.72/1.91         (~ (v1_funct_1 @ X0)
% 1.72/1.91          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.72/1.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.72/1.91          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.72/1.91          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.72/1.91               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.72/1.91               (k6_partfun1 @ sk_A))
% 1.72/1.91          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.72/1.91          | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.91      inference('sup-', [status(thm)], ['4', '5'])).
% 1.72/1.91  thf('7', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('9', plain,
% 1.72/1.91      (![X0 : $i]:
% 1.72/1.91         (~ (v1_funct_1 @ X0)
% 1.72/1.91          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.72/1.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.72/1.91          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.72/1.91          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.72/1.91               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.72/1.91               (k6_partfun1 @ sk_A)))),
% 1.72/1.91      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.72/1.91  thf('10', plain,
% 1.72/1.91      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.72/1.91        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.72/1.91        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.72/1.91        | ~ (v1_funct_1 @ sk_D))),
% 1.72/1.91      inference('sup-', [status(thm)], ['3', '9'])).
% 1.72/1.91  thf('11', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('12', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('13', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('14', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 1.72/1.91      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 1.72/1.91  thf('15', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('17', plain,
% 1.72/1.91      ((((sk_A) != (sk_A))
% 1.72/1.91        | ~ (v2_funct_1 @ sk_D)
% 1.72/1.91        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.72/1.91        | ((sk_A) = (k1_xboole_0)))),
% 1.72/1.91      inference('demod', [status(thm)], ['2', '14', '15', '16'])).
% 1.72/1.91  thf('18', plain,
% 1.72/1.91      ((((sk_A) = (k1_xboole_0))
% 1.72/1.91        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.72/1.91        | ~ (v2_funct_1 @ sk_D))),
% 1.72/1.91      inference('simplify', [status(thm)], ['17'])).
% 1.72/1.91  thf('19', plain, (((sk_A) != (k1_xboole_0))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('20', plain,
% 1.72/1.91      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.72/1.91        | ~ (v2_funct_1 @ sk_D))),
% 1.72/1.91      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 1.72/1.91  thf('21', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('22', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf(redefinition_k1_partfun1, axiom,
% 1.72/1.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.72/1.91     ( ( ( v1_funct_1 @ E ) & 
% 1.72/1.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.72/1.91         ( v1_funct_1 @ F ) & 
% 1.72/1.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.72/1.91       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.72/1.91  thf('23', plain,
% 1.72/1.91      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.72/1.91         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.72/1.91          | ~ (v1_funct_1 @ X28)
% 1.72/1.91          | ~ (v1_funct_1 @ X31)
% 1.72/1.91          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.72/1.91          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 1.72/1.91              = (k5_relat_1 @ X28 @ X31)))),
% 1.72/1.91      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.72/1.91  thf('24', plain,
% 1.72/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.91         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.72/1.91            = (k5_relat_1 @ sk_C @ X0))
% 1.72/1.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.72/1.91          | ~ (v1_funct_1 @ X0)
% 1.72/1.91          | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.91      inference('sup-', [status(thm)], ['22', '23'])).
% 1.72/1.91  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('26', plain,
% 1.72/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.91         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.72/1.91            = (k5_relat_1 @ sk_C @ X0))
% 1.72/1.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.72/1.91          | ~ (v1_funct_1 @ X0))),
% 1.72/1.91      inference('demod', [status(thm)], ['24', '25'])).
% 1.72/1.91  thf('27', plain,
% 1.72/1.91      ((~ (v1_funct_1 @ sk_D)
% 1.72/1.91        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.72/1.91            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.72/1.91      inference('sup-', [status(thm)], ['21', '26'])).
% 1.72/1.91  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('29', plain,
% 1.72/1.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.72/1.91         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.72/1.91      inference('demod', [status(thm)], ['27', '28'])).
% 1.72/1.91  thf('30', plain,
% 1.72/1.91      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.72/1.91        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.72/1.91        (k6_partfun1 @ sk_A))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('31', plain,
% 1.72/1.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.72/1.91         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.72/1.91      inference('demod', [status(thm)], ['27', '28'])).
% 1.72/1.91  thf('32', plain,
% 1.72/1.91      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.72/1.91        (k6_partfun1 @ sk_A))),
% 1.72/1.91      inference('demod', [status(thm)], ['30', '31'])).
% 1.72/1.91  thf('33', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('34', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf(dt_k1_partfun1, axiom,
% 1.72/1.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.72/1.91     ( ( ( v1_funct_1 @ E ) & 
% 1.72/1.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.72/1.91         ( v1_funct_1 @ F ) & 
% 1.72/1.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.72/1.91       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.72/1.91         ( m1_subset_1 @
% 1.72/1.91           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.72/1.91           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.72/1.91  thf('35', plain,
% 1.72/1.91      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.72/1.91         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.72/1.91          | ~ (v1_funct_1 @ X22)
% 1.72/1.91          | ~ (v1_funct_1 @ X25)
% 1.72/1.91          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.72/1.91          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 1.72/1.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 1.72/1.91      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.72/1.91  thf('36', plain,
% 1.72/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.72/1.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.72/1.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.72/1.91          | ~ (v1_funct_1 @ X1)
% 1.72/1.91          | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.91      inference('sup-', [status(thm)], ['34', '35'])).
% 1.72/1.91  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('38', plain,
% 1.72/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.72/1.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.72/1.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.72/1.91          | ~ (v1_funct_1 @ X1))),
% 1.72/1.91      inference('demod', [status(thm)], ['36', '37'])).
% 1.72/1.91  thf('39', plain,
% 1.72/1.91      ((~ (v1_funct_1 @ sk_D)
% 1.72/1.91        | (m1_subset_1 @ 
% 1.72/1.91           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.72/1.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.72/1.91      inference('sup-', [status(thm)], ['33', '38'])).
% 1.72/1.91  thf('40', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('41', plain,
% 1.72/1.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.72/1.91         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.72/1.91      inference('demod', [status(thm)], ['27', '28'])).
% 1.72/1.91  thf('42', plain,
% 1.72/1.91      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.72/1.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.72/1.91      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.72/1.91  thf(redefinition_r2_relset_1, axiom,
% 1.72/1.91    (![A:$i,B:$i,C:$i,D:$i]:
% 1.72/1.91     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.72/1.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.91       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.72/1.91  thf('43', plain,
% 1.72/1.91      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.72/1.91         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.72/1.91          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.72/1.91          | ((X17) = (X20))
% 1.72/1.91          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 1.72/1.91      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.72/1.91  thf('44', plain,
% 1.72/1.91      (![X0 : $i]:
% 1.72/1.91         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.72/1.91          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.72/1.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.72/1.91      inference('sup-', [status(thm)], ['42', '43'])).
% 1.72/1.91  thf('45', plain,
% 1.72/1.91      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.72/1.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.72/1.91        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.72/1.91      inference('sup-', [status(thm)], ['32', '44'])).
% 1.72/1.91  thf(t29_relset_1, axiom,
% 1.72/1.91    (![A:$i]:
% 1.72/1.91     ( m1_subset_1 @
% 1.72/1.91       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.72/1.91  thf('46', plain,
% 1.72/1.91      (![X21 : $i]:
% 1.72/1.91         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 1.72/1.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.72/1.91      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.72/1.91  thf(redefinition_k6_partfun1, axiom,
% 1.72/1.91    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.72/1.91  thf('47', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 1.72/1.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.72/1.91  thf('48', plain,
% 1.72/1.91      (![X21 : $i]:
% 1.72/1.91         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 1.72/1.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.72/1.91      inference('demod', [status(thm)], ['46', '47'])).
% 1.72/1.91  thf('49', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.72/1.91      inference('demod', [status(thm)], ['45', '48'])).
% 1.72/1.91  thf('50', plain,
% 1.72/1.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.72/1.91         = (k6_partfun1 @ sk_A))),
% 1.72/1.91      inference('demod', [status(thm)], ['29', '49'])).
% 1.72/1.91  thf('51', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf(t30_funct_2, axiom,
% 1.72/1.91    (![A:$i,B:$i,C:$i,D:$i]:
% 1.72/1.91     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.72/1.91         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.72/1.91       ( ![E:$i]:
% 1.72/1.91         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.72/1.91             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.72/1.91           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.72/1.91               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.72/1.91             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.72/1.91               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.72/1.91  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.72/1.91  thf(zf_stmt_2, axiom,
% 1.72/1.91    (![C:$i,B:$i]:
% 1.72/1.91     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.72/1.91       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.72/1.91  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.72/1.91  thf(zf_stmt_4, axiom,
% 1.72/1.91    (![E:$i,D:$i]:
% 1.72/1.91     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.72/1.91  thf(zf_stmt_5, axiom,
% 1.72/1.91    (![A:$i,B:$i,C:$i,D:$i]:
% 1.72/1.91     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.72/1.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.91       ( ![E:$i]:
% 1.72/1.91         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.72/1.91             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.72/1.91           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.72/1.91               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.72/1.91             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.72/1.91  thf('52', plain,
% 1.72/1.91      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.72/1.91         (~ (v1_funct_1 @ X43)
% 1.72/1.91          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 1.72/1.91          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 1.72/1.91          | (zip_tseitin_0 @ X43 @ X46)
% 1.72/1.91          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43))
% 1.72/1.91          | (zip_tseitin_1 @ X45 @ X44)
% 1.72/1.91          | ((k2_relset_1 @ X47 @ X44 @ X46) != (X44))
% 1.72/1.91          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X44)))
% 1.72/1.91          | ~ (v1_funct_2 @ X46 @ X47 @ X44)
% 1.72/1.91          | ~ (v1_funct_1 @ X46))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.72/1.91  thf('53', plain,
% 1.72/1.91      (![X0 : $i, X1 : $i]:
% 1.72/1.91         (~ (v1_funct_1 @ X0)
% 1.72/1.91          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.72/1.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.72/1.91          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.72/1.91          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.72/1.91          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.72/1.91          | (zip_tseitin_0 @ sk_D @ X0)
% 1.72/1.91          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.72/1.91          | ~ (v1_funct_1 @ sk_D))),
% 1.72/1.91      inference('sup-', [status(thm)], ['51', '52'])).
% 1.72/1.91  thf('54', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('56', plain,
% 1.72/1.91      (![X0 : $i, X1 : $i]:
% 1.72/1.91         (~ (v1_funct_1 @ X0)
% 1.72/1.91          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.72/1.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.72/1.91          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.72/1.91          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.72/1.91          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.72/1.91          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.72/1.91      inference('demod', [status(thm)], ['53', '54', '55'])).
% 1.72/1.91  thf('57', plain,
% 1.72/1.91      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.72/1.91        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.72/1.91        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.72/1.91        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.72/1.91        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.72/1.91        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.72/1.91        | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.91      inference('sup-', [status(thm)], ['50', '56'])).
% 1.72/1.91  thf(fc4_funct_1, axiom,
% 1.72/1.91    (![A:$i]:
% 1.72/1.91     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.72/1.91       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.72/1.91  thf('58', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 1.72/1.91      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.72/1.91  thf('59', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 1.72/1.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.72/1.91  thf('60', plain, (![X12 : $i]: (v2_funct_1 @ (k6_partfun1 @ X12))),
% 1.72/1.91      inference('demod', [status(thm)], ['58', '59'])).
% 1.72/1.91  thf('61', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('62', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('63', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('65', plain,
% 1.72/1.91      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.72/1.91        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.72/1.91        | ((sk_B) != (sk_B)))),
% 1.72/1.91      inference('demod', [status(thm)], ['57', '60', '61', '62', '63', '64'])).
% 1.72/1.91  thf('66', plain,
% 1.72/1.91      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.72/1.91      inference('simplify', [status(thm)], ['65'])).
% 1.72/1.91  thf('67', plain,
% 1.72/1.91      (![X41 : $i, X42 : $i]:
% 1.72/1.91         (((X41) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X41 @ X42))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.72/1.91  thf('68', plain,
% 1.72/1.91      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.72/1.91      inference('sup-', [status(thm)], ['66', '67'])).
% 1.72/1.91  thf('69', plain, (((sk_A) != (k1_xboole_0))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('70', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.72/1.91      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 1.72/1.91  thf('71', plain,
% 1.72/1.91      (![X39 : $i, X40 : $i]:
% 1.72/1.91         ((v2_funct_1 @ X40) | ~ (zip_tseitin_0 @ X40 @ X39))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.72/1.91  thf('72', plain, ((v2_funct_1 @ sk_D)),
% 1.72/1.91      inference('sup-', [status(thm)], ['70', '71'])).
% 1.72/1.91  thf('73', plain,
% 1.72/1.91      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.72/1.91      inference('demod', [status(thm)], ['20', '72'])).
% 1.72/1.91  thf('74', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf(cc1_relset_1, axiom,
% 1.72/1.91    (![A:$i,B:$i,C:$i]:
% 1.72/1.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.72/1.91       ( v1_relat_1 @ C ) ))).
% 1.72/1.91  thf('75', plain,
% 1.72/1.91      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.72/1.91         ((v1_relat_1 @ X14)
% 1.72/1.91          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.72/1.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.72/1.91  thf('76', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.91      inference('sup-', [status(thm)], ['74', '75'])).
% 1.72/1.91  thf(t37_relat_1, axiom,
% 1.72/1.91    (![A:$i]:
% 1.72/1.91     ( ( v1_relat_1 @ A ) =>
% 1.72/1.91       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.72/1.91         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.72/1.91  thf('77', plain,
% 1.72/1.91      (![X1 : $i]:
% 1.72/1.91         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 1.72/1.91          | ~ (v1_relat_1 @ X1))),
% 1.72/1.91      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.72/1.91  thf('78', plain,
% 1.72/1.91      (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 1.72/1.91      inference('sup-', [status(thm)], ['76', '77'])).
% 1.72/1.91  thf(dt_k4_relat_1, axiom,
% 1.72/1.91    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 1.72/1.91  thf('79', plain,
% 1.72/1.91      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 1.72/1.91      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.72/1.91  thf(d9_funct_1, axiom,
% 1.72/1.91    (![A:$i]:
% 1.72/1.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.72/1.91       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.72/1.91  thf('80', plain,
% 1.72/1.91      (![X9 : $i]:
% 1.72/1.91         (~ (v2_funct_1 @ X9)
% 1.72/1.91          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 1.72/1.91          | ~ (v1_funct_1 @ X9)
% 1.72/1.91          | ~ (v1_relat_1 @ X9))),
% 1.72/1.91      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.72/1.91  thf('81', plain,
% 1.72/1.91      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 1.72/1.91      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.72/1.91  thf('82', plain,
% 1.72/1.91      (![X1 : $i]:
% 1.72/1.91         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 1.72/1.91          | ~ (v1_relat_1 @ X1))),
% 1.72/1.91      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.72/1.91  thf('83', plain,
% 1.72/1.91      (![X0 : $i]:
% 1.72/1.91         (~ (v1_relat_1 @ X0)
% 1.72/1.91          | ((k1_relat_1 @ (k4_relat_1 @ X0))
% 1.72/1.91              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 1.72/1.91      inference('sup-', [status(thm)], ['81', '82'])).
% 1.72/1.91  thf(dt_k2_funct_1, axiom,
% 1.72/1.91    (![A:$i]:
% 1.72/1.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.72/1.91       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.72/1.91         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.72/1.91  thf('84', plain,
% 1.72/1.91      (![X10 : $i]:
% 1.72/1.91         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 1.72/1.91          | ~ (v1_funct_1 @ X10)
% 1.72/1.91          | ~ (v1_relat_1 @ X10))),
% 1.72/1.91      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.72/1.91  thf('85', plain,
% 1.72/1.91      (![X9 : $i]:
% 1.72/1.91         (~ (v2_funct_1 @ X9)
% 1.72/1.91          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 1.72/1.91          | ~ (v1_funct_1 @ X9)
% 1.72/1.91          | ~ (v1_relat_1 @ X9))),
% 1.72/1.91      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.72/1.91  thf('86', plain,
% 1.72/1.91      (![X10 : $i]:
% 1.72/1.92         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 1.72/1.92          | ~ (v1_funct_1 @ X10)
% 1.72/1.92          | ~ (v1_relat_1 @ X10))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.72/1.92  thf('87', plain,
% 1.72/1.92      (![X1 : $i]:
% 1.72/1.92         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 1.72/1.92          | ~ (v1_relat_1 @ X1))),
% 1.72/1.92      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.72/1.92  thf('88', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 1.72/1.92              = (k2_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.72/1.92      inference('sup-', [status(thm)], ['86', '87'])).
% 1.72/1.92  thf('89', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 1.72/1.92            = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0))),
% 1.72/1.92      inference('sup+', [status(thm)], ['85', '88'])).
% 1.72/1.92  thf('90', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 1.72/1.92              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 1.72/1.92      inference('simplify', [status(thm)], ['89'])).
% 1.72/1.92  thf(t78_relat_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ A ) =>
% 1.72/1.92       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.72/1.92  thf('91', plain,
% 1.72/1.92      (![X7 : $i]:
% 1.72/1.92         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 1.72/1.92          | ~ (v1_relat_1 @ X7))),
% 1.72/1.92      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.72/1.92  thf('92', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 1.72/1.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.72/1.92  thf('93', plain,
% 1.72/1.92      (![X7 : $i]:
% 1.72/1.92         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 1.72/1.92          | ~ (v1_relat_1 @ X7))),
% 1.72/1.92      inference('demod', [status(thm)], ['91', '92'])).
% 1.72/1.92  thf('94', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k5_relat_1 @ 
% 1.72/1.92            (k6_partfun1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))) @ 
% 1.72/1.92            (k2_funct_1 @ X0)) = (k2_funct_1 @ X0))
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['90', '93'])).
% 1.72/1.92  thf('95', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ((k5_relat_1 @ 
% 1.72/1.92              (k6_partfun1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))) @ 
% 1.72/1.92              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['84', '94'])).
% 1.72/1.92  thf('96', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k5_relat_1 @ 
% 1.72/1.92            (k6_partfun1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))) @ 
% 1.72/1.92            (k2_funct_1 @ X0)) = (k2_funct_1 @ X0))
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0))),
% 1.72/1.92      inference('simplify', [status(thm)], ['95'])).
% 1.72/1.92  thf('97', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k4_relat_1 @ X0))) @ 
% 1.72/1.92            (k2_funct_1 @ X0)) = (k2_funct_1 @ X0))
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0))),
% 1.72/1.92      inference('sup+', [status(thm)], ['83', '96'])).
% 1.72/1.92  thf('98', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k4_relat_1 @ X0))) @ 
% 1.72/1.92              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 1.72/1.92      inference('simplify', [status(thm)], ['97'])).
% 1.72/1.92  thf('99', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k4_relat_1 @ X0))) @ 
% 1.72/1.92            (k4_relat_1 @ X0)) = (k2_funct_1 @ X0))
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0))),
% 1.72/1.92      inference('sup+', [status(thm)], ['80', '98'])).
% 1.72/1.92  thf('100', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k4_relat_1 @ X0))) @ 
% 1.72/1.92              (k4_relat_1 @ X0)) = (k2_funct_1 @ X0)))),
% 1.72/1.92      inference('simplify', [status(thm)], ['99'])).
% 1.72/1.92  thf(t80_relat_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ A ) =>
% 1.72/1.92       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.72/1.92  thf('101', plain,
% 1.72/1.92      (![X8 : $i]:
% 1.72/1.92         (((k5_relat_1 @ X8 @ (k6_relat_1 @ (k2_relat_1 @ X8))) = (X8))
% 1.72/1.92          | ~ (v1_relat_1 @ X8))),
% 1.72/1.92      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.72/1.92  thf('102', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 1.72/1.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.72/1.92  thf('103', plain,
% 1.72/1.92      (![X8 : $i]:
% 1.72/1.92         (((k5_relat_1 @ X8 @ (k6_partfun1 @ (k2_relat_1 @ X8))) = (X8))
% 1.72/1.92          | ~ (v1_relat_1 @ X8))),
% 1.72/1.92      inference('demod', [status(thm)], ['101', '102'])).
% 1.72/1.92  thf('104', plain,
% 1.72/1.92      (![X7 : $i]:
% 1.72/1.92         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 1.72/1.92          | ~ (v1_relat_1 @ X7))),
% 1.72/1.92      inference('demod', [status(thm)], ['91', '92'])).
% 1.72/1.92  thf(t55_relat_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ A ) =>
% 1.72/1.92       ( ![B:$i]:
% 1.72/1.92         ( ( v1_relat_1 @ B ) =>
% 1.72/1.92           ( ![C:$i]:
% 1.72/1.92             ( ( v1_relat_1 @ C ) =>
% 1.72/1.92               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.72/1.92                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.72/1.92  thf('105', plain,
% 1.72/1.92      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X2)
% 1.72/1.92          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 1.72/1.92              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 1.72/1.92          | ~ (v1_relat_1 @ X4)
% 1.72/1.92          | ~ (v1_relat_1 @ X3))),
% 1.72/1.92      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.72/1.92  thf('106', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         (((k5_relat_1 @ X0 @ X1)
% 1.72/1.92            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.72/1.92               (k5_relat_1 @ X0 @ X1)))
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.72/1.92          | ~ (v1_relat_1 @ X1)
% 1.72/1.92          | ~ (v1_relat_1 @ X0))),
% 1.72/1.92      inference('sup+', [status(thm)], ['104', '105'])).
% 1.72/1.92  thf('107', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.72/1.92      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.72/1.92  thf('108', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 1.72/1.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.72/1.92  thf('109', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 1.72/1.92      inference('demod', [status(thm)], ['107', '108'])).
% 1.72/1.92  thf('110', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         (((k5_relat_1 @ X0 @ X1)
% 1.72/1.92            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.72/1.92               (k5_relat_1 @ X0 @ X1)))
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X1)
% 1.72/1.92          | ~ (v1_relat_1 @ X0))),
% 1.72/1.92      inference('demod', [status(thm)], ['106', '109'])).
% 1.72/1.92  thf('111', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X1)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ((k5_relat_1 @ X0 @ X1)
% 1.72/1.92              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.72/1.92                 (k5_relat_1 @ X0 @ X1))))),
% 1.72/1.92      inference('simplify', [status(thm)], ['110'])).
% 1.72/1.92  thf('112', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.72/1.92            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 1.72/1.92      inference('sup+', [status(thm)], ['103', '111'])).
% 1.72/1.92  thf('113', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 1.72/1.92      inference('demod', [status(thm)], ['107', '108'])).
% 1.72/1.92  thf('114', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.72/1.92            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0))),
% 1.72/1.92      inference('demod', [status(thm)], ['112', '113'])).
% 1.72/1.92  thf('115', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X0)
% 1.72/1.92          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.72/1.92              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 1.72/1.92      inference('simplify', [status(thm)], ['114'])).
% 1.72/1.92  thf('116', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 1.72/1.92            (k6_partfun1 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 1.72/1.92            = (k2_funct_1 @ X0))
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['100', '115'])).
% 1.72/1.92  thf('117', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ((k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 1.72/1.92              (k6_partfun1 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 1.72/1.92              = (k2_funct_1 @ X0)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['79', '116'])).
% 1.72/1.92  thf('118', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 1.72/1.92            (k6_partfun1 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 1.72/1.92            = (k2_funct_1 @ X0))
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0))),
% 1.72/1.92      inference('simplify', [status(thm)], ['117'])).
% 1.72/1.92  thf('119', plain,
% 1.72/1.92      ((((k5_relat_1 @ (k4_relat_1 @ sk_D) @ 
% 1.72/1.92          (k6_partfun1 @ (k1_relat_1 @ sk_D))) = (k2_funct_1 @ sk_D))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_D)
% 1.72/1.92        | ~ (v2_funct_1 @ sk_D)
% 1.72/1.92        | ~ (v1_funct_1 @ sk_D))),
% 1.72/1.92      inference('sup+', [status(thm)], ['78', '118'])).
% 1.72/1.92  thf('120', plain,
% 1.72/1.92      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.72/1.92  thf('121', plain,
% 1.72/1.92      (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['76', '77'])).
% 1.72/1.92  thf('122', plain,
% 1.72/1.92      (![X8 : $i]:
% 1.72/1.92         (((k5_relat_1 @ X8 @ (k6_partfun1 @ (k2_relat_1 @ X8))) = (X8))
% 1.72/1.92          | ~ (v1_relat_1 @ X8))),
% 1.72/1.92      inference('demod', [status(thm)], ['101', '102'])).
% 1.72/1.92  thf('123', plain,
% 1.72/1.92      ((((k5_relat_1 @ (k4_relat_1 @ sk_D) @ 
% 1.72/1.92          (k6_partfun1 @ (k1_relat_1 @ sk_D))) = (k4_relat_1 @ sk_D))
% 1.72/1.92        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['121', '122'])).
% 1.72/1.92  thf('124', plain,
% 1.72/1.92      ((~ (v1_relat_1 @ sk_D)
% 1.72/1.92        | ((k5_relat_1 @ (k4_relat_1 @ sk_D) @ 
% 1.72/1.92            (k6_partfun1 @ (k1_relat_1 @ sk_D))) = (k4_relat_1 @ sk_D)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['120', '123'])).
% 1.72/1.92  thf('125', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.92      inference('sup-', [status(thm)], ['74', '75'])).
% 1.72/1.92  thf('126', plain,
% 1.72/1.92      (((k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_partfun1 @ (k1_relat_1 @ sk_D)))
% 1.72/1.92         = (k4_relat_1 @ sk_D))),
% 1.72/1.92      inference('demod', [status(thm)], ['124', '125'])).
% 1.72/1.92  thf('127', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.92      inference('sup-', [status(thm)], ['74', '75'])).
% 1.72/1.92  thf('128', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('129', plain,
% 1.72/1.92      ((((k4_relat_1 @ sk_D) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.72/1.92      inference('demod', [status(thm)], ['119', '126', '127', '128'])).
% 1.72/1.92  thf('130', plain, ((v2_funct_1 @ sk_D)),
% 1.72/1.92      inference('sup-', [status(thm)], ['70', '71'])).
% 1.72/1.92  thf('131', plain, (((k4_relat_1 @ sk_D) = (k2_funct_1 @ sk_D))),
% 1.72/1.92      inference('demod', [status(thm)], ['129', '130'])).
% 1.72/1.92  thf('132', plain,
% 1.72/1.92      (((k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.72/1.92      inference('demod', [status(thm)], ['73', '131'])).
% 1.72/1.92  thf('133', plain,
% 1.72/1.92      (![X9 : $i]:
% 1.72/1.92         (~ (v2_funct_1 @ X9)
% 1.72/1.92          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 1.72/1.92          | ~ (v1_funct_1 @ X9)
% 1.72/1.92          | ~ (v1_relat_1 @ X9))),
% 1.72/1.92      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.72/1.92  thf(t58_funct_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.72/1.92       ( ( v2_funct_1 @ A ) =>
% 1.72/1.92         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.72/1.92             ( k1_relat_1 @ A ) ) & 
% 1.72/1.92           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.72/1.92             ( k1_relat_1 @ A ) ) ) ) ))).
% 1.72/1.92  thf('134', plain,
% 1.72/1.92      (![X13 : $i]:
% 1.72/1.92         (~ (v2_funct_1 @ X13)
% 1.72/1.92          | ((k2_relat_1 @ (k5_relat_1 @ X13 @ (k2_funct_1 @ X13)))
% 1.72/1.92              = (k1_relat_1 @ X13))
% 1.72/1.92          | ~ (v1_funct_1 @ X13)
% 1.72/1.92          | ~ (v1_relat_1 @ X13))),
% 1.72/1.92      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.72/1.92  thf('135', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 1.72/1.92            = (k1_relat_1 @ X0))
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0))),
% 1.72/1.92      inference('sup+', [status(thm)], ['133', '134'])).
% 1.72/1.92  thf('136', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 1.72/1.92              = (k1_relat_1 @ X0)))),
% 1.72/1.92      inference('simplify', [status(thm)], ['135'])).
% 1.72/1.92  thf('137', plain,
% 1.72/1.92      ((((k2_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_D)
% 1.72/1.92        | ~ (v1_funct_1 @ sk_D)
% 1.72/1.92        | ~ (v2_funct_1 @ sk_D))),
% 1.72/1.92      inference('sup+', [status(thm)], ['132', '136'])).
% 1.72/1.92  thf(t71_relat_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.72/1.92       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.72/1.92  thf('138', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 1.72/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.72/1.92  thf('139', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 1.72/1.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.72/1.92  thf('140', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X6)) = (X6))),
% 1.72/1.92      inference('demod', [status(thm)], ['138', '139'])).
% 1.72/1.92  thf('141', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.92      inference('sup-', [status(thm)], ['74', '75'])).
% 1.72/1.92  thf('142', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('143', plain, ((v2_funct_1 @ sk_D)),
% 1.72/1.92      inference('sup-', [status(thm)], ['70', '71'])).
% 1.72/1.92  thf('144', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.72/1.92      inference('demod', [status(thm)], ['137', '140', '141', '142', '143'])).
% 1.72/1.92  thf('145', plain,
% 1.72/1.92      (![X7 : $i]:
% 1.72/1.92         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 1.72/1.92          | ~ (v1_relat_1 @ X7))),
% 1.72/1.92      inference('demod', [status(thm)], ['91', '92'])).
% 1.72/1.92  thf('146', plain,
% 1.72/1.92      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_D))),
% 1.72/1.92      inference('sup+', [status(thm)], ['144', '145'])).
% 1.72/1.92  thf('147', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.72/1.92      inference('demod', [status(thm)], ['45', '48'])).
% 1.72/1.92  thf('148', plain,
% 1.72/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('149', plain,
% 1.72/1.92      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.72/1.92         (((X48) = (k1_xboole_0))
% 1.72/1.92          | ~ (v1_funct_1 @ X49)
% 1.72/1.92          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 1.72/1.92          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 1.72/1.92          | ((k5_relat_1 @ (k2_funct_1 @ X49) @ X49) = (k6_partfun1 @ X48))
% 1.72/1.92          | ~ (v2_funct_1 @ X49)
% 1.72/1.92          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 1.72/1.92      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.72/1.92  thf('150', plain,
% 1.72/1.92      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.72/1.92        | ~ (v2_funct_1 @ sk_C)
% 1.72/1.92        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.72/1.92        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.72/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.72/1.92        | ((sk_B) = (k1_xboole_0)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['148', '149'])).
% 1.72/1.92  thf('151', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('152', plain, ((v2_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('153', plain,
% 1.72/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('154', plain,
% 1.72/1.92      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.72/1.92         ((v1_relat_1 @ X14)
% 1.72/1.92          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.72/1.92      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.72/1.92  thf('155', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['153', '154'])).
% 1.72/1.92  thf('156', plain,
% 1.72/1.92      (![X1 : $i]:
% 1.72/1.92         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 1.72/1.92          | ~ (v1_relat_1 @ X1))),
% 1.72/1.92      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.72/1.92  thf('157', plain,
% 1.72/1.92      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['155', '156'])).
% 1.72/1.92  thf('158', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 1.72/1.92            (k6_partfun1 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 1.72/1.92            = (k2_funct_1 @ X0))
% 1.72/1.92          | ~ (v1_funct_1 @ X0)
% 1.72/1.92          | ~ (v2_funct_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ X0))),
% 1.72/1.92      inference('simplify', [status(thm)], ['117'])).
% 1.72/1.92  thf('159', plain,
% 1.72/1.92      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 1.72/1.92          (k6_partfun1 @ (k1_relat_1 @ sk_C))) = (k2_funct_1 @ sk_C))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_C)
% 1.72/1.92        | ~ (v2_funct_1 @ sk_C)
% 1.72/1.92        | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.92      inference('sup+', [status(thm)], ['157', '158'])).
% 1.72/1.92  thf('160', plain,
% 1.72/1.92      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.72/1.92  thf('161', plain,
% 1.72/1.92      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['155', '156'])).
% 1.72/1.92  thf('162', plain,
% 1.72/1.92      (![X8 : $i]:
% 1.72/1.92         (((k5_relat_1 @ X8 @ (k6_partfun1 @ (k2_relat_1 @ X8))) = (X8))
% 1.72/1.92          | ~ (v1_relat_1 @ X8))),
% 1.72/1.92      inference('demod', [status(thm)], ['101', '102'])).
% 1.72/1.92  thf('163', plain,
% 1.72/1.92      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 1.72/1.92          (k6_partfun1 @ (k1_relat_1 @ sk_C))) = (k4_relat_1 @ sk_C))
% 1.72/1.92        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['161', '162'])).
% 1.72/1.92  thf('164', plain,
% 1.72/1.92      ((~ (v1_relat_1 @ sk_C)
% 1.72/1.92        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 1.72/1.92            (k6_partfun1 @ (k1_relat_1 @ sk_C))) = (k4_relat_1 @ sk_C)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['160', '163'])).
% 1.72/1.92  thf('165', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['153', '154'])).
% 1.72/1.92  thf('166', plain,
% 1.72/1.92      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.72/1.92         = (k4_relat_1 @ sk_C))),
% 1.72/1.92      inference('demod', [status(thm)], ['164', '165'])).
% 1.72/1.92  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['153', '154'])).
% 1.72/1.92  thf('168', plain, ((v2_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('169', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('170', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.72/1.92      inference('demod', [status(thm)], ['159', '166', '167', '168', '169'])).
% 1.72/1.92  thf('171', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('173', plain,
% 1.72/1.92      ((((sk_B) != (sk_B))
% 1.72/1.92        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.72/1.92        | ((sk_B) = (k1_xboole_0)))),
% 1.72/1.92      inference('demod', [status(thm)],
% 1.72/1.92                ['150', '151', '152', '170', '171', '172'])).
% 1.72/1.92  thf('174', plain,
% 1.72/1.92      ((((sk_B) = (k1_xboole_0))
% 1.72/1.92        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.72/1.92      inference('simplify', [status(thm)], ['173'])).
% 1.72/1.92  thf('175', plain, (((sk_B) != (k1_xboole_0))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('176', plain,
% 1.72/1.92      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.72/1.92      inference('simplify_reflect-', [status(thm)], ['174', '175'])).
% 1.72/1.92  thf('177', plain,
% 1.72/1.92      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X2)
% 1.72/1.92          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 1.72/1.92              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 1.72/1.92          | ~ (v1_relat_1 @ X4)
% 1.72/1.92          | ~ (v1_relat_1 @ X3))),
% 1.72/1.92      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.72/1.92  thf('178', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.72/1.92            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.72/1.92          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.72/1.92          | ~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (v1_relat_1 @ sk_C))),
% 1.72/1.92      inference('sup+', [status(thm)], ['176', '177'])).
% 1.72/1.92  thf('179', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.72/1.92      inference('demod', [status(thm)], ['159', '166', '167', '168', '169'])).
% 1.72/1.92  thf('180', plain,
% 1.72/1.92      (![X10 : $i]:
% 1.72/1.92         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 1.72/1.92          | ~ (v1_funct_1 @ X10)
% 1.72/1.92          | ~ (v1_relat_1 @ X10))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.72/1.92  thf('181', plain,
% 1.72/1.92      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_C)
% 1.72/1.92        | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.92      inference('sup+', [status(thm)], ['179', '180'])).
% 1.72/1.92  thf('182', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['153', '154'])).
% 1.72/1.92  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('184', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 1.72/1.92      inference('demod', [status(thm)], ['181', '182', '183'])).
% 1.72/1.92  thf('185', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['153', '154'])).
% 1.72/1.92  thf('186', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.72/1.92            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.72/1.92          | ~ (v1_relat_1 @ X0))),
% 1.72/1.92      inference('demod', [status(thm)], ['178', '184', '185'])).
% 1.72/1.92  thf('187', plain,
% 1.72/1.92      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.72/1.92          = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_D))),
% 1.72/1.92      inference('sup+', [status(thm)], ['147', '186'])).
% 1.72/1.92  thf('188', plain,
% 1.72/1.92      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.72/1.92         = (k4_relat_1 @ sk_C))),
% 1.72/1.92      inference('demod', [status(thm)], ['164', '165'])).
% 1.72/1.92  thf('189', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.72/1.92      inference('demod', [status(thm)], ['159', '166', '167', '168', '169'])).
% 1.72/1.92  thf('190', plain,
% 1.72/1.92      (![X13 : $i]:
% 1.72/1.92         (~ (v2_funct_1 @ X13)
% 1.72/1.92          | ((k2_relat_1 @ (k5_relat_1 @ X13 @ (k2_funct_1 @ X13)))
% 1.72/1.92              = (k1_relat_1 @ X13))
% 1.72/1.92          | ~ (v1_funct_1 @ X13)
% 1.72/1.92          | ~ (v1_relat_1 @ X13))),
% 1.72/1.92      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.72/1.92  thf('191', plain,
% 1.72/1.92      ((((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)))
% 1.72/1.92          = (k1_relat_1 @ sk_C))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_C)
% 1.72/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.72/1.92        | ~ (v2_funct_1 @ sk_C))),
% 1.72/1.92      inference('sup+', [status(thm)], ['189', '190'])).
% 1.72/1.92  thf('192', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['153', '154'])).
% 1.72/1.92  thf('193', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('194', plain, ((v2_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('195', plain,
% 1.72/1.92      (((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)))
% 1.72/1.92         = (k1_relat_1 @ sk_C))),
% 1.72/1.92      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 1.72/1.92  thf('196', plain,
% 1.72/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('197', plain,
% 1.72/1.92      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.72/1.92         (((X48) = (k1_xboole_0))
% 1.72/1.92          | ~ (v1_funct_1 @ X49)
% 1.72/1.92          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 1.72/1.92          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 1.72/1.92          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_partfun1 @ X50))
% 1.72/1.92          | ~ (v2_funct_1 @ X49)
% 1.72/1.92          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 1.72/1.92      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.72/1.92  thf('198', plain,
% 1.72/1.92      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.72/1.92        | ~ (v2_funct_1 @ sk_C)
% 1.72/1.92        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.72/1.92        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.72/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.72/1.92        | ((sk_B) = (k1_xboole_0)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['196', '197'])).
% 1.72/1.92  thf('199', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('200', plain, ((v2_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('201', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.72/1.92      inference('demod', [status(thm)], ['159', '166', '167', '168', '169'])).
% 1.72/1.92  thf('202', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('203', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('204', plain,
% 1.72/1.92      ((((sk_B) != (sk_B))
% 1.72/1.92        | ((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.72/1.92        | ((sk_B) = (k1_xboole_0)))),
% 1.72/1.92      inference('demod', [status(thm)],
% 1.72/1.92                ['198', '199', '200', '201', '202', '203'])).
% 1.72/1.92  thf('205', plain,
% 1.72/1.92      ((((sk_B) = (k1_xboole_0))
% 1.72/1.92        | ((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 1.72/1.92      inference('simplify', [status(thm)], ['204'])).
% 1.72/1.92  thf('206', plain, (((sk_B) != (k1_xboole_0))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('207', plain,
% 1.72/1.92      (((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.72/1.92      inference('simplify_reflect-', [status(thm)], ['205', '206'])).
% 1.72/1.92  thf('208', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X6)) = (X6))),
% 1.72/1.92      inference('demod', [status(thm)], ['138', '139'])).
% 1.72/1.92  thf('209', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.72/1.92      inference('demod', [status(thm)], ['195', '207', '208'])).
% 1.72/1.92  thf('210', plain,
% 1.72/1.92      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.72/1.92         = (k4_relat_1 @ sk_C))),
% 1.72/1.92      inference('demod', [status(thm)], ['188', '209'])).
% 1.72/1.92  thf('211', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.92      inference('sup-', [status(thm)], ['74', '75'])).
% 1.72/1.92  thf('212', plain,
% 1.72/1.92      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k4_relat_1 @ sk_C))),
% 1.72/1.92      inference('demod', [status(thm)], ['187', '210', '211'])).
% 1.72/1.92  thf('213', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.92      inference('sup-', [status(thm)], ['74', '75'])).
% 1.72/1.92  thf('214', plain, (((k4_relat_1 @ sk_C) = (sk_D))),
% 1.72/1.92      inference('demod', [status(thm)], ['146', '212', '213'])).
% 1.72/1.92  thf('215', plain,
% 1.72/1.92      (![X9 : $i]:
% 1.72/1.92         (~ (v2_funct_1 @ X9)
% 1.72/1.92          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 1.72/1.92          | ~ (v1_funct_1 @ X9)
% 1.72/1.92          | ~ (v1_relat_1 @ X9))),
% 1.72/1.92      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.72/1.92  thf('216', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('217', plain,
% 1.72/1.92      ((((sk_D) != (k4_relat_1 @ sk_C))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_C)
% 1.72/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.72/1.92        | ~ (v2_funct_1 @ sk_C))),
% 1.72/1.92      inference('sup-', [status(thm)], ['215', '216'])).
% 1.72/1.92  thf('218', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.92      inference('sup-', [status(thm)], ['153', '154'])).
% 1.72/1.92  thf('219', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('220', plain, ((v2_funct_1 @ sk_C)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('221', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 1.72/1.92      inference('demod', [status(thm)], ['217', '218', '219', '220'])).
% 1.72/1.92  thf('222', plain, ($false),
% 1.72/1.92      inference('simplify_reflect-', [status(thm)], ['214', '221'])).
% 1.72/1.92  
% 1.72/1.92  % SZS output end Refutation
% 1.72/1.92  
% 1.72/1.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
