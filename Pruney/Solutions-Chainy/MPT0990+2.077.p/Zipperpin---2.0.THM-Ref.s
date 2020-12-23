%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EPWGIq5c0L

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:07 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  293 (1812 expanded)
%              Number of leaves         :   47 ( 546 expanded)
%              Depth                    :   24
%              Number of atoms          : 2940 (51652 expanded)
%              Number of equality atoms :  206 (3566 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

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
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
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
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 )
        = ( k5_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( r2_relset_1 @ X35 @ X35 @ ( k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37 ) @ ( k6_partfun1 @ X35 ) )
      | ( ( k2_relset_1 @ X36 @ X35 @ X37 )
        = X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('24',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( r2_relset_1 @ X35 @ X35 @ ( k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37 ) @ ( k6_relat_1 @ X35 ) )
      | ( ( k2_relset_1 @ X36 @ X35 @ X37 )
        = X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('33',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('35',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['30','35','36','37','38','39'])).

thf('41',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','40'])).

thf('42',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('44',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

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
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X24 ) ) ) ) ),
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
    inference(demod,[status(thm)],['19','20'])).

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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
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
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('59',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('60',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( zip_tseitin_0 @ X42 @ X45 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X46 @ X43 @ X43 @ X44 @ X45 @ X42 ) )
      | ( zip_tseitin_1 @ X44 @ X43 )
      | ( ( k2_relset_1 @ X46 @ X43 @ X45 )
       != X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
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

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('70',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
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

thf('73',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf(t46_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( v2_funct_1 @ B ) )
           => ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) ) )).

thf('82',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t46_funct_1])).

thf('83',plain,
    ( ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('85',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('86',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
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

thf('90',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relset_1 @ X49 @ X48 @ X47 )
       != X48 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X49 @ X48 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('91',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relset_1 @ X49 @ X48 @ X47 )
       != X48 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X47 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X49 @ X48 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('100',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf('106',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('108',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','86','87','88','97','108'])).

thf('110',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['84','85'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['69','114','115','116','117','118'])).

thf('120',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('122',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v2_funct_1 @ X39 )
      | ~ ( zip_tseitin_0 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('126',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['42','126'])).

thf('128',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['57','60'])).

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

thf('129',plain,(
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

thf('130',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['30','35','36','37','38','39'])).

thf('132',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('134',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('138',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['84','85'])).

thf('143',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['130','131','134','135','140','141','142'])).

thf('144',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['124','125'])).

thf('146',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['42','126'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('148',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) ) )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('149',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
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

thf('152',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('153',plain,(
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
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['150','153'])).

thf('155',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['154','155','156','157','158'])).

thf('160',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['160','161'])).

thf(t59_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('163',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 ) )
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('164',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['138','139'])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['84','85'])).

thf('167',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['164','165','166','167','168'])).

thf('170',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['132','133'])).

thf('171',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['124','125'])).

thf('173',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['149','169','170','171','172'])).

thf('174',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['146','173'])).

thf('175',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['127','175'])).

thf('177',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['30','35','36','37','38','39'])).

thf('178',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['138','139'])).

thf('179',plain,(
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

thf('180',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_C )
       != ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['84','85'])).

thf('182',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_C )
       != ( k6_relat_1 @ sk_B ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['180','181','182','183'])).

thf('185',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['177','184'])).

thf('186',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['132','133'])).

thf('187',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['188','189'])).

thf('191',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('192',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('193',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['96'])).

thf('195',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('197',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('199',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
      = sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('201',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('202',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['200','202'])).

thf('204',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('205',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('206',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) ) )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('208',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('209',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('210',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X8 ) )
        = X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('211',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 ) )
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['210','211'])).

thf('213',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['209','212'])).

thf('214',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['96'])).

thf('215',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['84','85'])).

thf('218',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['213','214','215','216','217'])).

thf('219',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['208','218'])).

thf('220',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['84','85'])).

thf('221',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['219','220','221','222'])).

thf('224',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['207','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['84','85'])).

thf('226',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['224','225','226','227'])).

thf('229',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['206','228'])).

thf('230',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('231',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relset_1 @ X49 @ X48 @ X47 )
       != X48 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X47 ) @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X49 @ X48 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('233',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['233','234','235','236','237'])).

thf('239',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['96'])).

thf('241',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['199','203','229','230','239','240'])).

thf('242',plain,
    ( ( sk_A != sk_A )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['190','241'])).

thf('243',plain,(
    ( k5_relat_1 @ sk_D @ sk_C )
 != ( k6_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['242'])).

thf('244',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['176','243'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EPWGIq5c0L
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:11:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.67/0.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.91  % Solved by: fo/fo7.sh
% 0.67/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.91  % done 817 iterations in 0.447s
% 0.67/0.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.91  % SZS output start Refutation
% 0.67/0.91  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.67/0.91  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.67/0.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.67/0.91  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.67/0.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.67/0.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.67/0.91  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.67/0.91  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.67/0.91  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.67/0.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.67/0.91  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.67/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.91  thf(sk_D_type, type, sk_D: $i).
% 0.67/0.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.67/0.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.67/0.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.67/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.91  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.91  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.67/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.91  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.67/0.91  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.67/0.91  thf(t36_funct_2, conjecture,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.67/0.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.91       ( ![D:$i]:
% 0.67/0.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.67/0.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.67/0.91           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.67/0.91               ( r2_relset_1 @
% 0.67/0.91                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.67/0.91                 ( k6_partfun1 @ A ) ) & 
% 0.67/0.91               ( v2_funct_1 @ C ) ) =>
% 0.67/0.91             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.67/0.91               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.67/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.91    (~( ![A:$i,B:$i,C:$i]:
% 0.67/0.91        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.67/0.91            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.91          ( ![D:$i]:
% 0.67/0.91            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.67/0.91                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.67/0.91              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.67/0.91                  ( r2_relset_1 @
% 0.67/0.91                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.67/0.91                    ( k6_partfun1 @ A ) ) & 
% 0.67/0.91                  ( v2_funct_1 @ C ) ) =>
% 0.67/0.91                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.67/0.91                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.67/0.91    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.67/0.91  thf('0', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(t35_funct_2, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.67/0.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.91       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.67/0.91         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.67/0.91           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.67/0.91             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.67/0.91  thf('1', plain,
% 0.67/0.91      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.67/0.91         (((X50) = (k1_xboole_0))
% 0.67/0.91          | ~ (v1_funct_1 @ X51)
% 0.67/0.91          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 0.67/0.91          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 0.67/0.91          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_partfun1 @ X52))
% 0.67/0.91          | ~ (v2_funct_1 @ X51)
% 0.67/0.91          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 0.67/0.91      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.67/0.91  thf(redefinition_k6_partfun1, axiom,
% 0.67/0.91    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.67/0.91  thf('2', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.67/0.91  thf('3', plain,
% 0.67/0.91      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.67/0.91         (((X50) = (k1_xboole_0))
% 0.67/0.91          | ~ (v1_funct_1 @ X51)
% 0.67/0.91          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 0.67/0.91          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 0.67/0.91          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_relat_1 @ X52))
% 0.67/0.91          | ~ (v2_funct_1 @ X51)
% 0.67/0.91          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 0.67/0.91      inference('demod', [status(thm)], ['1', '2'])).
% 0.67/0.91  thf('4', plain,
% 0.67/0.91      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.67/0.91        | ~ (v2_funct_1 @ sk_D)
% 0.67/0.91        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.67/0.91        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.67/0.91        | ~ (v1_funct_1 @ sk_D)
% 0.67/0.91        | ((sk_A) = (k1_xboole_0)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['0', '3'])).
% 0.67/0.91  thf('5', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(redefinition_k2_relset_1, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.91       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.67/0.91  thf('6', plain,
% 0.67/0.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.91         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.67/0.91          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.67/0.91  thf('7', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.67/0.91      inference('sup-', [status(thm)], ['5', '6'])).
% 0.67/0.91  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('10', plain,
% 0.67/0.91      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.67/0.91        | ~ (v2_funct_1 @ sk_D)
% 0.67/0.91        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.67/0.91        | ((sk_A) = (k1_xboole_0)))),
% 0.67/0.91      inference('demod', [status(thm)], ['4', '7', '8', '9'])).
% 0.67/0.91  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('12', plain,
% 0.67/0.91      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.67/0.91        | ~ (v2_funct_1 @ sk_D)
% 0.67/0.91        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 0.67/0.91      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.67/0.91  thf('13', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('14', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(redefinition_k1_partfun1, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.67/0.91     ( ( ( v1_funct_1 @ E ) & 
% 0.67/0.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.67/0.91         ( v1_funct_1 @ F ) & 
% 0.67/0.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.67/0.91       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.67/0.91  thf('15', plain,
% 0.67/0.91      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.67/0.91         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.67/0.91          | ~ (v1_funct_1 @ X27)
% 0.67/0.91          | ~ (v1_funct_1 @ X30)
% 0.67/0.91          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.67/0.91          | ((k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30)
% 0.67/0.91              = (k5_relat_1 @ X27 @ X30)))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.67/0.91  thf('16', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.91         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.67/0.91            = (k5_relat_1 @ sk_C @ X0))
% 0.67/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.67/0.91          | ~ (v1_funct_1 @ X0)
% 0.67/0.91          | ~ (v1_funct_1 @ sk_C))),
% 0.67/0.91      inference('sup-', [status(thm)], ['14', '15'])).
% 0.67/0.91  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('18', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.91         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.67/0.91            = (k5_relat_1 @ sk_C @ X0))
% 0.67/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.67/0.91          | ~ (v1_funct_1 @ X0))),
% 0.67/0.91      inference('demod', [status(thm)], ['16', '17'])).
% 0.67/0.91  thf('19', plain,
% 0.67/0.91      ((~ (v1_funct_1 @ sk_D)
% 0.67/0.91        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.67/0.91            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['13', '18'])).
% 0.67/0.91  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('21', plain,
% 0.67/0.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.67/0.91         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.67/0.91      inference('demod', [status(thm)], ['19', '20'])).
% 0.67/0.91  thf('22', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(t24_funct_2, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.67/0.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.91       ( ![D:$i]:
% 0.67/0.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.67/0.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.67/0.91           ( ( r2_relset_1 @
% 0.67/0.91               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.67/0.91               ( k6_partfun1 @ B ) ) =>
% 0.67/0.91             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.67/0.91  thf('23', plain,
% 0.67/0.91      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.67/0.91         (~ (v1_funct_1 @ X34)
% 0.67/0.91          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 0.67/0.91          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.67/0.91          | ~ (r2_relset_1 @ X35 @ X35 @ 
% 0.67/0.91               (k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37) @ 
% 0.67/0.91               (k6_partfun1 @ X35))
% 0.67/0.91          | ((k2_relset_1 @ X36 @ X35 @ X37) = (X35))
% 0.67/0.91          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.67/0.91          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 0.67/0.91          | ~ (v1_funct_1 @ X37))),
% 0.67/0.91      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.67/0.91  thf('24', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.67/0.91  thf('25', plain,
% 0.67/0.91      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.67/0.91         (~ (v1_funct_1 @ X34)
% 0.67/0.91          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 0.67/0.91          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.67/0.91          | ~ (r2_relset_1 @ X35 @ X35 @ 
% 0.67/0.91               (k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37) @ 
% 0.67/0.91               (k6_relat_1 @ X35))
% 0.67/0.91          | ((k2_relset_1 @ X36 @ X35 @ X37) = (X35))
% 0.67/0.91          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.67/0.91          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 0.67/0.91          | ~ (v1_funct_1 @ X37))),
% 0.67/0.91      inference('demod', [status(thm)], ['23', '24'])).
% 0.67/0.91  thf('26', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (v1_funct_1 @ X0)
% 0.67/0.91          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.67/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.67/0.91          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.67/0.91          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.67/0.91               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.67/0.91               (k6_relat_1 @ sk_A))
% 0.67/0.91          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.67/0.91          | ~ (v1_funct_1 @ sk_C))),
% 0.67/0.91      inference('sup-', [status(thm)], ['22', '25'])).
% 0.67/0.91  thf('27', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('29', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (v1_funct_1 @ X0)
% 0.67/0.91          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.67/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.67/0.91          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.67/0.91          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.67/0.91               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.67/0.91               (k6_relat_1 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.67/0.91  thf('30', plain,
% 0.67/0.91      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.67/0.91           (k6_relat_1 @ sk_A))
% 0.67/0.91        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.67/0.91        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.67/0.91        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.67/0.91        | ~ (v1_funct_1 @ sk_D))),
% 0.67/0.91      inference('sup-', [status(thm)], ['21', '29'])).
% 0.67/0.91  thf('31', plain,
% 0.67/0.91      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.67/0.91        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.67/0.91        (k6_partfun1 @ sk_A))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('32', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.67/0.91  thf('33', plain,
% 0.67/0.91      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.67/0.91        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.67/0.91        (k6_relat_1 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['31', '32'])).
% 0.67/0.91  thf('34', plain,
% 0.67/0.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.67/0.91         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.67/0.91      inference('demod', [status(thm)], ['19', '20'])).
% 0.67/0.91  thf('35', plain,
% 0.67/0.91      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.67/0.91        (k6_relat_1 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['33', '34'])).
% 0.67/0.91  thf('36', plain,
% 0.67/0.91      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.67/0.91      inference('sup-', [status(thm)], ['5', '6'])).
% 0.67/0.91  thf('37', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('38', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('39', plain, ((v1_funct_1 @ sk_D)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('40', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['30', '35', '36', '37', '38', '39'])).
% 0.67/0.91  thf('41', plain,
% 0.67/0.91      ((((sk_A) != (sk_A))
% 0.67/0.91        | ~ (v2_funct_1 @ sk_D)
% 0.67/0.91        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 0.67/0.91      inference('demod', [status(thm)], ['12', '40'])).
% 0.67/0.91  thf('42', plain,
% 0.67/0.91      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.67/0.91        | ~ (v2_funct_1 @ sk_D))),
% 0.67/0.91      inference('simplify', [status(thm)], ['41'])).
% 0.67/0.91  thf('43', plain,
% 0.67/0.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.67/0.91         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.67/0.91      inference('demod', [status(thm)], ['19', '20'])).
% 0.67/0.91  thf('44', plain,
% 0.67/0.91      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.67/0.91        (k6_relat_1 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['33', '34'])).
% 0.67/0.91  thf('45', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('46', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(dt_k1_partfun1, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.67/0.91     ( ( ( v1_funct_1 @ E ) & 
% 0.67/0.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.67/0.91         ( v1_funct_1 @ F ) & 
% 0.67/0.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.67/0.91       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.67/0.91         ( m1_subset_1 @
% 0.67/0.91           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.67/0.91           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.67/0.91  thf('47', plain,
% 0.67/0.91      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.67/0.91         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.67/0.91          | ~ (v1_funct_1 @ X19)
% 0.67/0.91          | ~ (v1_funct_1 @ X22)
% 0.67/0.91          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.67/0.91          | (m1_subset_1 @ (k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22) @ 
% 0.67/0.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X24))))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.67/0.91  thf('48', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.67/0.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.67/0.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.67/0.91          | ~ (v1_funct_1 @ X1)
% 0.67/0.91          | ~ (v1_funct_1 @ sk_C))),
% 0.67/0.91      inference('sup-', [status(thm)], ['46', '47'])).
% 0.67/0.91  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('50', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.67/0.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.67/0.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.67/0.91          | ~ (v1_funct_1 @ X1))),
% 0.67/0.91      inference('demod', [status(thm)], ['48', '49'])).
% 0.67/0.91  thf('51', plain,
% 0.67/0.91      ((~ (v1_funct_1 @ sk_D)
% 0.67/0.91        | (m1_subset_1 @ 
% 0.67/0.91           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.67/0.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.67/0.91      inference('sup-', [status(thm)], ['45', '50'])).
% 0.67/0.91  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('53', plain,
% 0.67/0.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.67/0.91         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.67/0.91      inference('demod', [status(thm)], ['19', '20'])).
% 0.67/0.91  thf('54', plain,
% 0.67/0.91      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.67/0.91  thf(redefinition_r2_relset_1, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.91     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.67/0.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.91       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.67/0.91  thf('55', plain,
% 0.67/0.91      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.67/0.91         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.67/0.91          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.67/0.91          | ((X15) = (X18))
% 0.67/0.91          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.67/0.91  thf('56', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.67/0.91          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.67/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.67/0.91      inference('sup-', [status(thm)], ['54', '55'])).
% 0.67/0.91  thf('57', plain,
% 0.67/0.91      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.67/0.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.67/0.91        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['44', '56'])).
% 0.67/0.91  thf(dt_k6_partfun1, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( m1_subset_1 @
% 0.67/0.91         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.67/0.91       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.67/0.91  thf('58', plain,
% 0.67/0.91      (![X26 : $i]:
% 0.67/0.91         (m1_subset_1 @ (k6_partfun1 @ X26) @ 
% 0.67/0.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.67/0.91  thf('59', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.67/0.91  thf('60', plain,
% 0.67/0.91      (![X26 : $i]:
% 0.67/0.91         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 0.67/0.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 0.67/0.91      inference('demod', [status(thm)], ['58', '59'])).
% 0.67/0.91  thf('61', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['57', '60'])).
% 0.67/0.91  thf('62', plain,
% 0.67/0.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.67/0.91         = (k6_relat_1 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['43', '61'])).
% 0.67/0.91  thf('63', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(t30_funct_2, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.91     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.67/0.91         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.67/0.91       ( ![E:$i]:
% 0.67/0.91         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.67/0.91             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.67/0.91           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.67/0.91               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.67/0.91             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.67/0.91               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.67/0.91  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.67/0.91  thf(zf_stmt_2, axiom,
% 0.67/0.91    (![C:$i,B:$i]:
% 0.67/0.91     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.67/0.91       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.67/0.91  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.67/0.91  thf(zf_stmt_4, axiom,
% 0.67/0.91    (![E:$i,D:$i]:
% 0.67/0.91     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.67/0.91  thf(zf_stmt_5, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.91     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.67/0.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.91       ( ![E:$i]:
% 0.67/0.91         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.67/0.91             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.67/0.91           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.67/0.91               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.67/0.91             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.67/0.91  thf('64', plain,
% 0.67/0.91      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.67/0.91         (~ (v1_funct_1 @ X42)
% 0.67/0.91          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 0.67/0.91          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.67/0.91          | (zip_tseitin_0 @ X42 @ X45)
% 0.67/0.91          | ~ (v2_funct_1 @ (k1_partfun1 @ X46 @ X43 @ X43 @ X44 @ X45 @ X42))
% 0.67/0.91          | (zip_tseitin_1 @ X44 @ X43)
% 0.67/0.91          | ((k2_relset_1 @ X46 @ X43 @ X45) != (X43))
% 0.67/0.91          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X43)))
% 0.67/0.91          | ~ (v1_funct_2 @ X45 @ X46 @ X43)
% 0.67/0.91          | ~ (v1_funct_1 @ X45))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.67/0.91  thf('65', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i]:
% 0.67/0.91         (~ (v1_funct_1 @ X0)
% 0.67/0.91          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.67/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.67/0.91          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.67/0.91          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.67/0.91          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.67/0.91          | (zip_tseitin_0 @ sk_D @ X0)
% 0.67/0.91          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.67/0.91          | ~ (v1_funct_1 @ sk_D))),
% 0.67/0.91      inference('sup-', [status(thm)], ['63', '64'])).
% 0.67/0.91  thf('66', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('67', plain, ((v1_funct_1 @ sk_D)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('68', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i]:
% 0.67/0.91         (~ (v1_funct_1 @ X0)
% 0.67/0.91          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.67/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.67/0.91          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.67/0.91          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.67/0.91          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.67/0.91          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.67/0.91      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.67/0.91  thf('69', plain,
% 0.67/0.91      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.67/0.91        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.67/0.91        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.67/0.91        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.67/0.91        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.67/0.91        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.67/0.91        | ~ (v1_funct_1 @ sk_C))),
% 0.67/0.91      inference('sup-', [status(thm)], ['62', '68'])).
% 0.67/0.91  thf(fc6_funct_1, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.67/0.91       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.67/0.91         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.67/0.91         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.67/0.91  thf('70', plain,
% 0.67/0.91      (![X1 : $i]:
% 0.67/0.91         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 0.67/0.91          | ~ (v2_funct_1 @ X1)
% 0.67/0.91          | ~ (v1_funct_1 @ X1)
% 0.67/0.91          | ~ (v1_relat_1 @ X1))),
% 0.67/0.91      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.67/0.91  thf('71', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('72', plain,
% 0.67/0.91      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.67/0.91         (((X50) = (k1_xboole_0))
% 0.67/0.91          | ~ (v1_funct_1 @ X51)
% 0.67/0.91          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 0.67/0.91          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 0.67/0.91          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_relat_1 @ X52))
% 0.67/0.91          | ~ (v2_funct_1 @ X51)
% 0.67/0.91          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 0.67/0.91      inference('demod', [status(thm)], ['1', '2'])).
% 0.67/0.91  thf('73', plain,
% 0.67/0.91      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.67/0.91        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.91        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 0.67/0.91        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.67/0.91        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.91        | ((sk_B) = (k1_xboole_0)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['71', '72'])).
% 0.67/0.91  thf('74', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('75', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('76', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('78', plain,
% 0.67/0.91      ((((sk_B) != (sk_B))
% 0.67/0.91        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 0.67/0.91        | ((sk_B) = (k1_xboole_0)))),
% 0.67/0.91      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 0.67/0.91  thf('79', plain,
% 0.67/0.91      ((((sk_B) = (k1_xboole_0))
% 0.67/0.91        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 0.67/0.91      inference('simplify', [status(thm)], ['78'])).
% 0.67/0.91  thf('80', plain, (((sk_B) != (k1_xboole_0))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('81', plain,
% 0.67/0.91      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 0.67/0.91      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 0.67/0.91  thf(t46_funct_1, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.91       ( ![B:$i]:
% 0.67/0.91         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.67/0.91           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 0.67/0.91             ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) ) ))).
% 0.67/0.91  thf('82', plain,
% 0.67/0.91      (![X2 : $i, X3 : $i]:
% 0.67/0.91         (~ (v1_relat_1 @ X2)
% 0.67/0.91          | ~ (v1_funct_1 @ X2)
% 0.67/0.91          | (v2_funct_1 @ (k5_relat_1 @ X3 @ X2))
% 0.67/0.91          | ~ (v2_funct_1 @ X2)
% 0.67/0.91          | ~ (v2_funct_1 @ X3)
% 0.67/0.91          | ~ (v1_funct_1 @ X3)
% 0.67/0.91          | ~ (v1_relat_1 @ X3))),
% 0.67/0.91      inference('cnf', [status(esa)], [t46_funct_1])).
% 0.67/0.91  thf('83', plain,
% 0.67/0.91      (((v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.67/0.91        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.91        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.91        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.91        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.91        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.91      inference('sup+', [status(thm)], ['81', '82'])).
% 0.67/0.91  thf('84', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(cc1_relset_1, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.91       ( v1_relat_1 @ C ) ))).
% 0.67/0.91  thf('85', plain,
% 0.67/0.91      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.67/0.91         ((v1_relat_1 @ X9)
% 0.67/0.91          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.67/0.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.67/0.91  thf('86', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.91      inference('sup-', [status(thm)], ['84', '85'])).
% 0.67/0.91  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('89', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(t31_funct_2, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.67/0.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.91       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.67/0.91         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.67/0.91           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.67/0.91           ( m1_subset_1 @
% 0.67/0.91             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.67/0.91  thf('90', plain,
% 0.67/0.91      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.67/0.91         (~ (v2_funct_1 @ X47)
% 0.67/0.91          | ((k2_relset_1 @ X49 @ X48 @ X47) != (X48))
% 0.67/0.91          | (v1_funct_1 @ (k2_funct_1 @ X47))
% 0.67/0.91          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 0.67/0.91          | ~ (v1_funct_2 @ X47 @ X49 @ X48)
% 0.67/0.91          | ~ (v1_funct_1 @ X47))),
% 0.67/0.91      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.67/0.91  thf('91', plain,
% 0.67/0.91      ((~ (v1_funct_1 @ sk_C)
% 0.67/0.91        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.67/0.91        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.91        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.67/0.91        | ~ (v2_funct_1 @ sk_C))),
% 0.67/0.91      inference('sup-', [status(thm)], ['89', '90'])).
% 0.67/0.91  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('93', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('94', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('96', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 0.67/0.91      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.67/0.91  thf('97', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.91      inference('simplify', [status(thm)], ['96'])).
% 0.67/0.91  thf('98', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('99', plain,
% 0.67/0.91      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.67/0.91         (~ (v2_funct_1 @ X47)
% 0.67/0.91          | ((k2_relset_1 @ X49 @ X48 @ X47) != (X48))
% 0.67/0.91          | (m1_subset_1 @ (k2_funct_1 @ X47) @ 
% 0.67/0.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.67/0.91          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 0.67/0.91          | ~ (v1_funct_2 @ X47 @ X49 @ X48)
% 0.67/0.91          | ~ (v1_funct_1 @ X47))),
% 0.67/0.91      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.67/0.91  thf('100', plain,
% 0.67/0.91      ((~ (v1_funct_1 @ sk_C)
% 0.67/0.91        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.67/0.91        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.67/0.91        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.67/0.91        | ~ (v2_funct_1 @ sk_C))),
% 0.67/0.91      inference('sup-', [status(thm)], ['98', '99'])).
% 0.67/0.91  thf('101', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('102', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('103', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('104', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('105', plain,
% 0.67/0.91      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.91         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.67/0.91        | ((sk_B) != (sk_B)))),
% 0.67/0.91      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 0.67/0.91  thf('106', plain,
% 0.67/0.91      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.67/0.91      inference('simplify', [status(thm)], ['105'])).
% 0.67/0.91  thf('107', plain,
% 0.67/0.91      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.67/0.91         ((v1_relat_1 @ X9)
% 0.67/0.91          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.67/0.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.67/0.91  thf('108', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.91      inference('sup-', [status(thm)], ['106', '107'])).
% 0.67/0.91  thf('109', plain,
% 0.67/0.91      (((v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.67/0.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.91      inference('demod', [status(thm)], ['83', '86', '87', '88', '97', '108'])).
% 0.67/0.91  thf('110', plain,
% 0.67/0.91      ((~ (v1_relat_1 @ sk_C)
% 0.67/0.91        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.91        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.91        | (v2_funct_1 @ (k6_relat_1 @ sk_A)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['70', '109'])).
% 0.67/0.91  thf('111', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.91      inference('sup-', [status(thm)], ['84', '85'])).
% 0.67/0.91  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('113', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('114', plain, ((v2_funct_1 @ (k6_relat_1 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 0.67/0.91  thf('115', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('116', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('117', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('118', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('119', plain,
% 0.67/0.91      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.67/0.91        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.67/0.91        | ((sk_B) != (sk_B)))),
% 0.67/0.91      inference('demod', [status(thm)],
% 0.67/0.91                ['69', '114', '115', '116', '117', '118'])).
% 0.67/0.91  thf('120', plain,
% 0.67/0.91      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.67/0.91      inference('simplify', [status(thm)], ['119'])).
% 0.67/0.91  thf('121', plain,
% 0.67/0.91      (![X40 : $i, X41 : $i]:
% 0.67/0.91         (((X40) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X40 @ X41))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.67/0.91  thf('122', plain,
% 0.67/0.91      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['120', '121'])).
% 0.67/0.91  thf('123', plain, (((sk_A) != (k1_xboole_0))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('124', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.67/0.91      inference('simplify_reflect-', [status(thm)], ['122', '123'])).
% 0.67/0.91  thf('125', plain,
% 0.67/0.91      (![X38 : $i, X39 : $i]:
% 0.67/0.91         ((v2_funct_1 @ X39) | ~ (zip_tseitin_0 @ X39 @ X38))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.67/0.91  thf('126', plain, ((v2_funct_1 @ sk_D)),
% 0.67/0.91      inference('sup-', [status(thm)], ['124', '125'])).
% 0.67/0.91  thf('127', plain,
% 0.67/0.91      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['42', '126'])).
% 0.67/0.91  thf('128', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['57', '60'])).
% 0.67/0.91  thf(t64_funct_1, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.91       ( ![B:$i]:
% 0.67/0.91         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.67/0.91           ( ( ( v2_funct_1 @ A ) & 
% 0.67/0.91               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.67/0.91               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.67/0.91             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.67/0.91  thf('129', plain,
% 0.67/0.91      (![X6 : $i, X7 : $i]:
% 0.67/0.91         (~ (v1_relat_1 @ X6)
% 0.67/0.91          | ~ (v1_funct_1 @ X6)
% 0.67/0.91          | ((X6) = (k2_funct_1 @ X7))
% 0.67/0.91          | ((k5_relat_1 @ X6 @ X7) != (k6_relat_1 @ (k2_relat_1 @ X7)))
% 0.67/0.91          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 0.67/0.91          | ~ (v2_funct_1 @ X7)
% 0.67/0.91          | ~ (v1_funct_1 @ X7)
% 0.67/0.91          | ~ (v1_relat_1 @ X7))),
% 0.67/0.91      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.67/0.91  thf('130', plain,
% 0.67/0.91      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 0.67/0.91        | ~ (v1_relat_1 @ sk_D)
% 0.67/0.91        | ~ (v1_funct_1 @ sk_D)
% 0.67/0.91        | ~ (v2_funct_1 @ sk_D)
% 0.67/0.91        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.67/0.91        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.67/0.91        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.91        | ~ (v1_relat_1 @ sk_C))),
% 0.67/0.91      inference('sup-', [status(thm)], ['128', '129'])).
% 0.67/0.91  thf('131', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['30', '35', '36', '37', '38', '39'])).
% 0.67/0.91  thf('132', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('133', plain,
% 0.67/0.91      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.67/0.91         ((v1_relat_1 @ X9)
% 0.67/0.91          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.67/0.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.67/0.91  thf('134', plain, ((v1_relat_1 @ sk_D)),
% 0.67/0.91      inference('sup-', [status(thm)], ['132', '133'])).
% 0.67/0.91  thf('135', plain, ((v1_funct_1 @ sk_D)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('136', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('137', plain,
% 0.67/0.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.91         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.67/0.91          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.67/0.91  thf('138', plain,
% 0.67/0.91      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.67/0.91      inference('sup-', [status(thm)], ['136', '137'])).
% 0.67/0.91  thf('139', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('140', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.67/0.91      inference('sup+', [status(thm)], ['138', '139'])).
% 0.67/0.91  thf('141', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('142', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.91      inference('sup-', [status(thm)], ['84', '85'])).
% 0.67/0.91  thf('143', plain,
% 0.67/0.91      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 0.67/0.91        | ~ (v2_funct_1 @ sk_D)
% 0.67/0.91        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.67/0.91        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.67/0.91      inference('demod', [status(thm)],
% 0.67/0.91                ['130', '131', '134', '135', '140', '141', '142'])).
% 0.67/0.91  thf('144', plain,
% 0.67/0.91      ((((sk_C) = (k2_funct_1 @ sk_D))
% 0.67/0.91        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.67/0.91        | ~ (v2_funct_1 @ sk_D))),
% 0.67/0.91      inference('simplify', [status(thm)], ['143'])).
% 0.67/0.91  thf('145', plain, ((v2_funct_1 @ sk_D)),
% 0.67/0.91      inference('sup-', [status(thm)], ['124', '125'])).
% 0.67/0.91  thf('146', plain,
% 0.67/0.91      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 0.67/0.91      inference('demod', [status(thm)], ['144', '145'])).
% 0.67/0.91  thf('147', plain,
% 0.67/0.91      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['42', '126'])).
% 0.67/0.91  thf(t58_funct_1, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.91       ( ( v2_funct_1 @ A ) =>
% 0.67/0.91         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.67/0.91             ( k1_relat_1 @ A ) ) & 
% 0.67/0.91           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.67/0.91             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.67/0.91  thf('148', plain,
% 0.67/0.91      (![X4 : $i]:
% 0.67/0.91         (~ (v2_funct_1 @ X4)
% 0.67/0.91          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ (k2_funct_1 @ X4)))
% 0.67/0.91              = (k1_relat_1 @ X4))
% 0.67/0.91          | ~ (v1_funct_1 @ X4)
% 0.67/0.91          | ~ (v1_relat_1 @ X4))),
% 0.67/0.91      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.67/0.91  thf('149', plain,
% 0.67/0.91      ((((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 0.67/0.91        | ~ (v1_relat_1 @ sk_D)
% 0.67/0.91        | ~ (v1_funct_1 @ sk_D)
% 0.67/0.91        | ~ (v2_funct_1 @ sk_D))),
% 0.67/0.91      inference('sup+', [status(thm)], ['147', '148'])).
% 0.67/0.91  thf('150', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('151', plain,
% 0.67/0.91      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.67/0.91         (((X50) = (k1_xboole_0))
% 0.67/0.91          | ~ (v1_funct_1 @ X51)
% 0.67/0.91          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 0.67/0.91          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 0.67/0.91          | ((k5_relat_1 @ (k2_funct_1 @ X51) @ X51) = (k6_partfun1 @ X50))
% 0.67/0.91          | ~ (v2_funct_1 @ X51)
% 0.67/0.91          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 0.67/0.91      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.67/0.91  thf('152', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.67/0.91  thf('153', plain,
% 0.67/0.91      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.67/0.91         (((X50) = (k1_xboole_0))
% 0.67/0.91          | ~ (v1_funct_1 @ X51)
% 0.67/0.91          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 0.67/0.91          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 0.67/0.91          | ((k5_relat_1 @ (k2_funct_1 @ X51) @ X51) = (k6_relat_1 @ X50))
% 0.67/0.91          | ~ (v2_funct_1 @ X51)
% 0.67/0.91          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 0.67/0.91      inference('demod', [status(thm)], ['151', '152'])).
% 0.67/0.91  thf('154', plain,
% 0.67/0.91      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.67/0.91        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.91        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 0.67/0.91        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.67/0.91        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.91        | ((sk_B) = (k1_xboole_0)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['150', '153'])).
% 0.67/0.91  thf('155', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('157', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('159', plain,
% 0.67/0.91      ((((sk_B) != (sk_B))
% 0.67/0.91        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 0.67/0.91        | ((sk_B) = (k1_xboole_0)))),
% 0.67/0.91      inference('demod', [status(thm)], ['154', '155', '156', '157', '158'])).
% 0.67/0.91  thf('160', plain,
% 0.67/0.91      ((((sk_B) = (k1_xboole_0))
% 0.67/0.91        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 0.67/0.91      inference('simplify', [status(thm)], ['159'])).
% 0.67/0.91  thf('161', plain, (((sk_B) != (k1_xboole_0))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('162', plain,
% 0.67/0.91      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.67/0.91      inference('simplify_reflect-', [status(thm)], ['160', '161'])).
% 0.67/0.91  thf(t59_funct_1, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.91       ( ( v2_funct_1 @ A ) =>
% 0.67/0.91         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.67/0.91             ( k2_relat_1 @ A ) ) & 
% 0.67/0.91           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.67/0.91             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.67/0.91  thf('163', plain,
% 0.67/0.91      (![X5 : $i]:
% 0.67/0.91         (~ (v2_funct_1 @ X5)
% 0.67/0.91          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X5) @ X5))
% 0.67/0.91              = (k2_relat_1 @ X5))
% 0.67/0.91          | ~ (v1_funct_1 @ X5)
% 0.67/0.91          | ~ (v1_relat_1 @ X5))),
% 0.67/0.91      inference('cnf', [status(esa)], [t59_funct_1])).
% 0.67/0.91  thf('164', plain,
% 0.67/0.91      ((((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (k2_relat_1 @ sk_C))
% 0.67/0.91        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.91        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.91        | ~ (v2_funct_1 @ sk_C))),
% 0.67/0.91      inference('sup+', [status(thm)], ['162', '163'])).
% 0.67/0.91  thf('165', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.67/0.91      inference('sup+', [status(thm)], ['138', '139'])).
% 0.67/0.91  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.91      inference('sup-', [status(thm)], ['84', '85'])).
% 0.67/0.91  thf('167', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('168', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('169', plain, (((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['164', '165', '166', '167', '168'])).
% 0.67/0.91  thf('170', plain, ((v1_relat_1 @ sk_D)),
% 0.67/0.91      inference('sup-', [status(thm)], ['132', '133'])).
% 0.67/0.91  thf('171', plain, ((v1_funct_1 @ sk_D)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('172', plain, ((v2_funct_1 @ sk_D)),
% 0.67/0.91      inference('sup-', [status(thm)], ['124', '125'])).
% 0.67/0.91  thf('173', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.67/0.91      inference('demod', [status(thm)], ['149', '169', '170', '171', '172'])).
% 0.67/0.91  thf('174', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 0.67/0.91      inference('demod', [status(thm)], ['146', '173'])).
% 0.67/0.91  thf('175', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.67/0.91      inference('simplify', [status(thm)], ['174'])).
% 0.67/0.91  thf('176', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['127', '175'])).
% 0.67/0.91  thf('177', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['30', '35', '36', '37', '38', '39'])).
% 0.67/0.91  thf('178', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.67/0.91      inference('sup+', [status(thm)], ['138', '139'])).
% 0.67/0.91  thf('179', plain,
% 0.67/0.91      (![X6 : $i, X7 : $i]:
% 0.67/0.91         (~ (v1_relat_1 @ X6)
% 0.67/0.91          | ~ (v1_funct_1 @ X6)
% 0.67/0.91          | ((X6) = (k2_funct_1 @ X7))
% 0.67/0.91          | ((k5_relat_1 @ X6 @ X7) != (k6_relat_1 @ (k2_relat_1 @ X7)))
% 0.67/0.91          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 0.67/0.91          | ~ (v2_funct_1 @ X7)
% 0.67/0.91          | ~ (v1_funct_1 @ X7)
% 0.67/0.91          | ~ (v1_relat_1 @ X7))),
% 0.67/0.91      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.67/0.91  thf('180', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (((k5_relat_1 @ X0 @ sk_C) != (k6_relat_1 @ sk_B))
% 0.67/0.91          | ~ (v1_relat_1 @ sk_C)
% 0.67/0.91          | ~ (v1_funct_1 @ sk_C)
% 0.67/0.91          | ~ (v2_funct_1 @ sk_C)
% 0.67/0.91          | ((k2_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.67/0.91          | ((X0) = (k2_funct_1 @ sk_C))
% 0.67/0.91          | ~ (v1_funct_1 @ X0)
% 0.67/0.91          | ~ (v1_relat_1 @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['178', '179'])).
% 0.67/0.91  thf('181', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.91      inference('sup-', [status(thm)], ['84', '85'])).
% 0.67/0.91  thf('182', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('183', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('184', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (((k5_relat_1 @ X0 @ sk_C) != (k6_relat_1 @ sk_B))
% 0.67/0.91          | ((k2_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.67/0.91          | ((X0) = (k2_funct_1 @ sk_C))
% 0.67/0.91          | ~ (v1_funct_1 @ X0)
% 0.67/0.91          | ~ (v1_relat_1 @ X0))),
% 0.67/0.91      inference('demod', [status(thm)], ['180', '181', '182', '183'])).
% 0.67/0.91  thf('185', plain,
% 0.67/0.91      ((((sk_A) != (k1_relat_1 @ sk_C))
% 0.67/0.91        | ~ (v1_relat_1 @ sk_D)
% 0.67/0.91        | ~ (v1_funct_1 @ sk_D)
% 0.67/0.91        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.67/0.91        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_relat_1 @ sk_B)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['177', '184'])).
% 0.67/0.91  thf('186', plain, ((v1_relat_1 @ sk_D)),
% 0.67/0.91      inference('sup-', [status(thm)], ['132', '133'])).
% 0.67/0.91  thf('187', plain, ((v1_funct_1 @ sk_D)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('188', plain,
% 0.67/0.91      ((((sk_A) != (k1_relat_1 @ sk_C))
% 0.67/0.91        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.67/0.91        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_relat_1 @ sk_B)))),
% 0.67/0.91      inference('demod', [status(thm)], ['185', '186', '187'])).
% 0.67/0.91  thf('189', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('190', plain,
% 0.67/0.91      ((((sk_A) != (k1_relat_1 @ sk_C))
% 0.67/0.91        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_relat_1 @ sk_B)))),
% 0.67/0.91      inference('simplify_reflect-', [status(thm)], ['188', '189'])).
% 0.67/0.91  thf('191', plain,
% 0.67/0.91      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.67/0.91      inference('simplify', [status(thm)], ['105'])).
% 0.67/0.91  thf('192', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.91         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.67/0.91            = (k5_relat_1 @ sk_C @ X0))
% 0.67/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.67/0.91          | ~ (v1_funct_1 @ X0))),
% 0.67/0.91      inference('demod', [status(thm)], ['16', '17'])).
% 0.67/0.91  thf('193', plain,
% 0.67/0.91      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.91        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 0.67/0.91            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 0.67/0.91      inference('sup-', [status(thm)], ['191', '192'])).
% 0.67/0.91  thf('194', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.91      inference('simplify', [status(thm)], ['96'])).
% 0.67/0.91  thf('195', plain,
% 0.67/0.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 0.67/0.92         = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 0.67/0.92      inference('demod', [status(thm)], ['193', '194'])).
% 0.67/0.92  thf('196', plain,
% 0.67/0.92      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 0.67/0.92      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 0.67/0.92  thf('197', plain,
% 0.67/0.92      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 0.67/0.92         = (k6_relat_1 @ sk_A))),
% 0.67/0.92      inference('demod', [status(thm)], ['195', '196'])).
% 0.67/0.92  thf('198', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (~ (v1_funct_1 @ X0)
% 0.67/0.92          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.67/0.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.67/0.92          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.67/0.92          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.67/0.92               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.67/0.92               (k6_relat_1 @ sk_A)))),
% 0.67/0.92      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.67/0.92  thf('199', plain,
% 0.67/0.92      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.67/0.92           (k6_relat_1 @ sk_A))
% 0.67/0.92        | ((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) = (sk_A))
% 0.67/0.92        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.92             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.67/0.92        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.67/0.92        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.92      inference('sup-', [status(thm)], ['197', '198'])).
% 0.67/0.92  thf('200', plain,
% 0.67/0.92      (![X26 : $i]:
% 0.67/0.92         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 0.67/0.92          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 0.67/0.92      inference('demod', [status(thm)], ['58', '59'])).
% 0.67/0.92  thf('201', plain,
% 0.67/0.92      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.67/0.92         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.67/0.92          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.67/0.92          | (r2_relset_1 @ X16 @ X17 @ X15 @ X18)
% 0.67/0.92          | ((X15) != (X18)))),
% 0.67/0.92      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.67/0.92  thf('202', plain,
% 0.67/0.92      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.67/0.92         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 0.67/0.92          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.67/0.92      inference('simplify', [status(thm)], ['201'])).
% 0.67/0.92  thf('203', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.67/0.92      inference('sup-', [status(thm)], ['200', '202'])).
% 0.67/0.92  thf('204', plain,
% 0.67/0.92      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.67/0.92      inference('simplify', [status(thm)], ['105'])).
% 0.67/0.92  thf('205', plain,
% 0.67/0.92      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.92         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.67/0.92          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.67/0.92      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.67/0.92  thf('206', plain,
% 0.67/0.92      (((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C))
% 0.67/0.92         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.92      inference('sup-', [status(thm)], ['204', '205'])).
% 0.67/0.92  thf('207', plain,
% 0.67/0.92      (![X4 : $i]:
% 0.67/0.92         (~ (v2_funct_1 @ X4)
% 0.67/0.92          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ (k2_funct_1 @ X4)))
% 0.67/0.92              = (k1_relat_1 @ X4))
% 0.67/0.92          | ~ (v1_funct_1 @ X4)
% 0.67/0.92          | ~ (v1_relat_1 @ X4))),
% 0.67/0.92      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.67/0.92  thf('208', plain,
% 0.67/0.92      (![X1 : $i]:
% 0.67/0.92         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 0.67/0.92          | ~ (v2_funct_1 @ X1)
% 0.67/0.92          | ~ (v1_funct_1 @ X1)
% 0.67/0.92          | ~ (v1_relat_1 @ X1))),
% 0.67/0.92      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.67/0.92  thf('209', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.92      inference('sup-', [status(thm)], ['106', '107'])).
% 0.67/0.92  thf(t65_funct_1, axiom,
% 0.67/0.92    (![A:$i]:
% 0.67/0.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.92       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.67/0.92  thf('210', plain,
% 0.67/0.92      (![X8 : $i]:
% 0.67/0.92         (~ (v2_funct_1 @ X8)
% 0.67/0.92          | ((k2_funct_1 @ (k2_funct_1 @ X8)) = (X8))
% 0.67/0.92          | ~ (v1_funct_1 @ X8)
% 0.67/0.92          | ~ (v1_relat_1 @ X8))),
% 0.67/0.92      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.67/0.92  thf('211', plain,
% 0.67/0.92      (![X5 : $i]:
% 0.67/0.92         (~ (v2_funct_1 @ X5)
% 0.67/0.92          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X5) @ X5))
% 0.67/0.92              = (k2_relat_1 @ X5))
% 0.67/0.92          | ~ (v1_funct_1 @ X5)
% 0.67/0.92          | ~ (v1_relat_1 @ X5))),
% 0.67/0.92      inference('cnf', [status(esa)], [t59_funct_1])).
% 0.67/0.92  thf('212', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.67/0.92            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.67/0.92          | ~ (v1_relat_1 @ X0)
% 0.67/0.92          | ~ (v1_funct_1 @ X0)
% 0.67/0.92          | ~ (v2_funct_1 @ X0)
% 0.67/0.92          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.67/0.92          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.92          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['210', '211'])).
% 0.67/0.92  thf('213', plain,
% 0.67/0.92      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.92        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.92        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.92        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.92        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.92        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 0.67/0.92            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.67/0.92      inference('sup-', [status(thm)], ['209', '212'])).
% 0.67/0.92  thf('214', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.92      inference('simplify', [status(thm)], ['96'])).
% 0.67/0.92  thf('215', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('216', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('217', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.92      inference('sup-', [status(thm)], ['84', '85'])).
% 0.67/0.92  thf('218', plain,
% 0.67/0.92      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.92        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 0.67/0.92            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.67/0.92      inference('demod', [status(thm)], ['213', '214', '215', '216', '217'])).
% 0.67/0.92  thf('219', plain,
% 0.67/0.92      ((~ (v1_relat_1 @ sk_C)
% 0.67/0.92        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.92        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.92        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 0.67/0.92            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.67/0.92      inference('sup-', [status(thm)], ['208', '218'])).
% 0.67/0.92  thf('220', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.92      inference('sup-', [status(thm)], ['84', '85'])).
% 0.67/0.92  thf('221', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('222', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('223', plain,
% 0.67/0.92      (((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 0.67/0.92         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.92      inference('demod', [status(thm)], ['219', '220', '221', '222'])).
% 0.67/0.92  thf('224', plain,
% 0.67/0.92      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.92        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.92        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.92        | ~ (v2_funct_1 @ sk_C))),
% 0.67/0.92      inference('sup+', [status(thm)], ['207', '223'])).
% 0.67/0.92  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.92      inference('sup-', [status(thm)], ['84', '85'])).
% 0.67/0.92  thf('226', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('227', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('228', plain,
% 0.67/0.92      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.92      inference('demod', [status(thm)], ['224', '225', '226', '227'])).
% 0.67/0.92  thf('229', plain,
% 0.67/0.92      (((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.67/0.92      inference('demod', [status(thm)], ['206', '228'])).
% 0.67/0.92  thf('230', plain,
% 0.67/0.92      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.67/0.92      inference('simplify', [status(thm)], ['105'])).
% 0.67/0.92  thf('231', plain,
% 0.67/0.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('232', plain,
% 0.67/0.92      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.67/0.92         (~ (v2_funct_1 @ X47)
% 0.67/0.92          | ((k2_relset_1 @ X49 @ X48 @ X47) != (X48))
% 0.67/0.92          | (v1_funct_2 @ (k2_funct_1 @ X47) @ X48 @ X49)
% 0.67/0.92          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 0.67/0.92          | ~ (v1_funct_2 @ X47 @ X49 @ X48)
% 0.67/0.92          | ~ (v1_funct_1 @ X47))),
% 0.67/0.92      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.67/0.92  thf('233', plain,
% 0.67/0.92      ((~ (v1_funct_1 @ sk_C)
% 0.67/0.92        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.67/0.92        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.67/0.92        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.67/0.92        | ~ (v2_funct_1 @ sk_C))),
% 0.67/0.92      inference('sup-', [status(thm)], ['231', '232'])).
% 0.67/0.92  thf('234', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('235', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('236', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('237', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('238', plain,
% 0.67/0.92      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.67/0.92      inference('demod', [status(thm)], ['233', '234', '235', '236', '237'])).
% 0.67/0.92  thf('239', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.67/0.92      inference('simplify', [status(thm)], ['238'])).
% 0.67/0.92  thf('240', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.92      inference('simplify', [status(thm)], ['96'])).
% 0.67/0.92  thf('241', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.67/0.92      inference('demod', [status(thm)],
% 0.67/0.92                ['199', '203', '229', '230', '239', '240'])).
% 0.67/0.92  thf('242', plain,
% 0.67/0.92      ((((sk_A) != (sk_A))
% 0.67/0.92        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_relat_1 @ sk_B)))),
% 0.67/0.92      inference('demod', [status(thm)], ['190', '241'])).
% 0.67/0.92  thf('243', plain, (((k5_relat_1 @ sk_D @ sk_C) != (k6_relat_1 @ sk_B))),
% 0.67/0.92      inference('simplify', [status(thm)], ['242'])).
% 0.67/0.92  thf('244', plain, ($false),
% 0.67/0.92      inference('simplify_reflect-', [status(thm)], ['176', '243'])).
% 0.67/0.92  
% 0.67/0.92  % SZS output end Refutation
% 0.67/0.92  
% 0.67/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
