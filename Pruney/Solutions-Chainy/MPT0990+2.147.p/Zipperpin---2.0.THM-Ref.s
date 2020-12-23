%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e6B98XmL9F

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:20 EST 2020

% Result     : Theorem 4.19s
% Output     : Refutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :  269 ( 704 expanded)
%              Number of leaves         :   59 ( 245 expanded)
%              Depth                    :   23
%              Number of atoms          : 2279 (12403 expanded)
%              Number of equality atoms :  154 ( 899 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

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
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ( ( k1_partfun1 @ X53 @ X54 @ X56 @ X57 @ X52 @ X55 )
        = ( k5_relat_1 @ X52 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
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
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( X30 = X33 )
      | ~ ( r2_relset_1 @ X31 @ X32 @ X30 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('24',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('28',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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

thf('29',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('30',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('40',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('41',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('42',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['37','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','51','52','53'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('57',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('58',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('59',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['31','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('67',plain,(
    ! [X22: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X22 ) )
      = ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('68',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('69',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('70',plain,(
    ! [X22: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X22 ) )
      = ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X22: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X22 ) )
      = ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('74',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
        = ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('77',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('78',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('79',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('80',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('81',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('82',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','79','82'])).

thf('84',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('85',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('86',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['72','83','84','85','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('92',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66','87','88','89','90','91'])).

thf('93',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('94',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66','87','88','89','90','91'])).

thf('95',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['35','36'])).

thf('97',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['92','100'])).

thf('102',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A_1 ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['27','109'])).

thf('111',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
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

thf('113',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_funct_2 @ X59 @ X60 @ X61 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ~ ( r2_relset_1 @ X60 @ X60 @ ( k1_partfun1 @ X60 @ X61 @ X61 @ X60 @ X59 @ X62 ) @ ( k6_partfun1 @ X60 ) )
      | ( ( k2_relset_1 @ X61 @ X60 @ X62 )
        = X60 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X60 ) ) )
      | ~ ( v1_funct_2 @ X62 @ X61 @ X60 )
      | ~ ( v1_funct_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A_1 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
      = sk_A_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['111','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('121',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['118','121','122','123','124'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('126',plain,(
    ! [X7: $i] :
      ( ( ( k10_relat_1 @ X7 @ ( k2_relat_1 @ X7 ) )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('127',plain,
    ( ( ( k10_relat_1 @ sk_D @ sk_A_1 )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('129',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k8_relset_1 @ X35 @ X36 @ X37 @ X36 )
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('130',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A_1 @ sk_D @ sk_A_1 )
    = ( k1_relset_1 @ sk_B @ sk_A_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('132',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k8_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k10_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A_1 @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
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

thf('135',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('136',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A_1 @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('138',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('139',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A_1 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('141',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_A_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X1: $i] :
      ( ( zip_tseitin_0 @ sk_A_1 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('146',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('147',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('149',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X1: $i] :
      ( zip_tseitin_0 @ sk_A_1 @ X1 ) ),
    inference('simplify_reflect+',[status(thm)],['145','150'])).

thf('152',plain,(
    zip_tseitin_1 @ sk_D @ sk_A_1 @ sk_B ),
    inference(demod,[status(thm)],['139','151'])).

thf('153',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A_1 @ sk_D ) ),
    inference(demod,[status(thm)],['136','152'])).

thf('154',plain,
    ( ( k10_relat_1 @ sk_D @ sk_A_1 )
    = sk_B ),
    inference(demod,[status(thm)],['130','133','153'])).

thf('155',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('157',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('159',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['127','154','159'])).

thf('161',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('162',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['157','158'])).

thf('164',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k8_relset_1 @ X35 @ X36 @ X37 @ X36 )
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('167',plain,
    ( ( k8_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_B )
    = ( k1_relset_1 @ sk_A_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k8_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k10_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A_1 @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('173',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relset_1 @ sk_A_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('176',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('178',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['146','149'])).

thf('182',plain,(
    ! [X1: $i] :
      ( zip_tseitin_0 @ sk_B @ X1 ) ),
    inference('simplify_reflect+',[status(thm)],['180','181'])).

thf('183',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 ),
    inference(demod,[status(thm)],['176','182'])).

thf('184',plain,
    ( sk_A_1
    = ( k1_relset_1 @ sk_A_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['173','183'])).

thf('185',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = sk_A_1 ),
    inference(demod,[status(thm)],['167','170','184'])).

thf('186',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['35','36'])).

thf('187',plain,(
    ! [X7: $i] :
      ( ( ( k10_relat_1 @ X7 @ ( k2_relat_1 @ X7 ) )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('188',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('190',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( sk_A_1
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['185','190'])).

thf('192',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('193',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('194',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('195',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('196',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['193','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['192','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A_1 ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['191','199'])).

thf('201',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A_1 ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['200','201','202','203'])).

thf('205',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['157','158'])).

thf('206',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','164','204','205'])).

thf('207',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['206','207'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e6B98XmL9F
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:32:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.19/4.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.19/4.42  % Solved by: fo/fo7.sh
% 4.19/4.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.19/4.42  % done 2038 iterations in 3.953s
% 4.19/4.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.19/4.42  % SZS output start Refutation
% 4.19/4.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.19/4.42  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.19/4.42  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.19/4.42  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.19/4.42  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.19/4.42  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.19/4.42  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.19/4.42  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 4.19/4.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.19/4.42  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.19/4.42  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 4.19/4.42  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.19/4.42  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.19/4.42  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.19/4.42  thf(sk_A_1_type, type, sk_A_1: $i).
% 4.19/4.42  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.19/4.42  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.19/4.42  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 4.19/4.42  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.19/4.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.19/4.42  thf(sk_D_type, type, sk_D: $i).
% 4.19/4.42  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.19/4.42  thf(sk_C_type, type, sk_C: $i).
% 4.19/4.42  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.19/4.42  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 4.19/4.42  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.19/4.42  thf(sk_B_type, type, sk_B: $i).
% 4.19/4.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.19/4.42  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.19/4.42  thf(t36_funct_2, conjecture,
% 4.19/4.42    (![A:$i,B:$i,C:$i]:
% 4.19/4.42     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.19/4.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.19/4.42       ( ![D:$i]:
% 4.19/4.42         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.19/4.42             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.19/4.42           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 4.19/4.42               ( r2_relset_1 @
% 4.19/4.42                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.19/4.42                 ( k6_partfun1 @ A ) ) & 
% 4.19/4.42               ( v2_funct_1 @ C ) ) =>
% 4.19/4.42             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.19/4.42               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 4.19/4.42  thf(zf_stmt_0, negated_conjecture,
% 4.19/4.42    (~( ![A:$i,B:$i,C:$i]:
% 4.19/4.42        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.19/4.42            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.19/4.42          ( ![D:$i]:
% 4.19/4.42            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.19/4.42                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.19/4.42              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 4.19/4.42                  ( r2_relset_1 @
% 4.19/4.42                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.19/4.42                    ( k6_partfun1 @ A ) ) & 
% 4.19/4.42                  ( v2_funct_1 @ C ) ) =>
% 4.19/4.42                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.19/4.42                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 4.19/4.42    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 4.19/4.42  thf('0', plain,
% 4.19/4.42      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 4.19/4.42        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 4.19/4.42        (k6_partfun1 @ sk_A_1))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('1', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('2', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf(redefinition_k1_partfun1, axiom,
% 4.19/4.42    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.19/4.42     ( ( ( v1_funct_1 @ E ) & 
% 4.19/4.42         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.19/4.42         ( v1_funct_1 @ F ) & 
% 4.19/4.42         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.19/4.42       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 4.19/4.42  thf('3', plain,
% 4.19/4.42      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 4.19/4.42         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 4.19/4.42          | ~ (v1_funct_1 @ X52)
% 4.19/4.42          | ~ (v1_funct_1 @ X55)
% 4.19/4.42          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 4.19/4.42          | ((k1_partfun1 @ X53 @ X54 @ X56 @ X57 @ X52 @ X55)
% 4.19/4.42              = (k5_relat_1 @ X52 @ X55)))),
% 4.19/4.42      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 4.19/4.42  thf('4', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.19/4.42         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.19/4.42            = (k5_relat_1 @ sk_C @ X0))
% 4.19/4.42          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.19/4.42          | ~ (v1_funct_1 @ X0)
% 4.19/4.42          | ~ (v1_funct_1 @ sk_C))),
% 4.19/4.42      inference('sup-', [status(thm)], ['2', '3'])).
% 4.19/4.42  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('6', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.19/4.42         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.19/4.42            = (k5_relat_1 @ sk_C @ X0))
% 4.19/4.42          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.19/4.42          | ~ (v1_funct_1 @ X0))),
% 4.19/4.42      inference('demod', [status(thm)], ['4', '5'])).
% 4.19/4.42  thf('7', plain,
% 4.19/4.42      ((~ (v1_funct_1 @ sk_D)
% 4.19/4.42        | ((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 4.19/4.42            = (k5_relat_1 @ sk_C @ sk_D)))),
% 4.19/4.42      inference('sup-', [status(thm)], ['1', '6'])).
% 4.19/4.42  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('9', plain,
% 4.19/4.42      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 4.19/4.42         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.19/4.42      inference('demod', [status(thm)], ['7', '8'])).
% 4.19/4.42  thf('10', plain,
% 4.19/4.42      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.19/4.42        (k6_partfun1 @ sk_A_1))),
% 4.19/4.42      inference('demod', [status(thm)], ['0', '9'])).
% 4.19/4.42  thf('11', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('12', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf(dt_k1_partfun1, axiom,
% 4.19/4.42    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.19/4.42     ( ( ( v1_funct_1 @ E ) & 
% 4.19/4.42         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.19/4.42         ( v1_funct_1 @ F ) & 
% 4.19/4.42         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.19/4.42       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.19/4.42         ( m1_subset_1 @
% 4.19/4.42           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.19/4.42           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.19/4.42  thf('13', plain,
% 4.19/4.42      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 4.19/4.42         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 4.19/4.42          | ~ (v1_funct_1 @ X46)
% 4.19/4.42          | ~ (v1_funct_1 @ X49)
% 4.19/4.42          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 4.19/4.42          | (m1_subset_1 @ (k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49) @ 
% 4.19/4.42             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X51))))),
% 4.19/4.42      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.19/4.42  thf('14', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.19/4.42         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.19/4.42           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 4.19/4.42          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.19/4.42          | ~ (v1_funct_1 @ X1)
% 4.19/4.42          | ~ (v1_funct_1 @ sk_C))),
% 4.19/4.42      inference('sup-', [status(thm)], ['12', '13'])).
% 4.19/4.42  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('16', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.19/4.42         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.19/4.42           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 4.19/4.42          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.19/4.42          | ~ (v1_funct_1 @ X1))),
% 4.19/4.42      inference('demod', [status(thm)], ['14', '15'])).
% 4.19/4.42  thf('17', plain,
% 4.19/4.42      ((~ (v1_funct_1 @ sk_D)
% 4.19/4.42        | (m1_subset_1 @ 
% 4.19/4.42           (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 4.19/4.42           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 4.19/4.42      inference('sup-', [status(thm)], ['11', '16'])).
% 4.19/4.42  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('19', plain,
% 4.19/4.42      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 4.19/4.42         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.19/4.42      inference('demod', [status(thm)], ['7', '8'])).
% 4.19/4.42  thf('20', plain,
% 4.19/4.42      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.19/4.42        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))),
% 4.19/4.42      inference('demod', [status(thm)], ['17', '18', '19'])).
% 4.19/4.42  thf(redefinition_r2_relset_1, axiom,
% 4.19/4.42    (![A:$i,B:$i,C:$i,D:$i]:
% 4.19/4.42     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.19/4.42         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.19/4.42       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.19/4.42  thf('21', plain,
% 4.19/4.42      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 4.19/4.42         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 4.19/4.42          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 4.19/4.42          | ((X30) = (X33))
% 4.19/4.42          | ~ (r2_relset_1 @ X31 @ X32 @ X30 @ X33))),
% 4.19/4.42      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.19/4.42  thf('22', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 4.19/4.42          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 4.19/4.42          | ~ (m1_subset_1 @ X0 @ 
% 4.19/4.42               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 4.19/4.42      inference('sup-', [status(thm)], ['20', '21'])).
% 4.19/4.42  thf('23', plain,
% 4.19/4.42      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A_1) @ 
% 4.19/4.42           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))
% 4.19/4.42        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1)))),
% 4.19/4.42      inference('sup-', [status(thm)], ['10', '22'])).
% 4.19/4.42  thf(t29_relset_1, axiom,
% 4.19/4.42    (![A:$i]:
% 4.19/4.42     ( m1_subset_1 @
% 4.19/4.42       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 4.19/4.42  thf('24', plain,
% 4.19/4.42      (![X34 : $i]:
% 4.19/4.42         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 4.19/4.42          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 4.19/4.42      inference('cnf', [status(esa)], [t29_relset_1])).
% 4.19/4.42  thf(redefinition_k6_partfun1, axiom,
% 4.19/4.42    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.19/4.42  thf('25', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 4.19/4.42      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.19/4.42  thf('26', plain,
% 4.19/4.42      (![X34 : $i]:
% 4.19/4.42         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 4.19/4.42          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 4.19/4.42      inference('demod', [status(thm)], ['24', '25'])).
% 4.19/4.42  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1))),
% 4.19/4.42      inference('demod', [status(thm)], ['23', '26'])).
% 4.19/4.42  thf(dt_k2_funct_1, axiom,
% 4.19/4.42    (![A:$i]:
% 4.19/4.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.19/4.42       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 4.19/4.42         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 4.19/4.42  thf('28', plain,
% 4.19/4.42      (![X13 : $i]:
% 4.19/4.42         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 4.19/4.42          | ~ (v1_funct_1 @ X13)
% 4.19/4.42          | ~ (v1_relat_1 @ X13))),
% 4.19/4.42      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.19/4.42  thf(t61_funct_1, axiom,
% 4.19/4.42    (![A:$i]:
% 4.19/4.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.19/4.42       ( ( v2_funct_1 @ A ) =>
% 4.19/4.42         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 4.19/4.42             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 4.19/4.42           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 4.19/4.42             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 4.19/4.42  thf('29', plain,
% 4.19/4.42      (![X19 : $i]:
% 4.19/4.42         (~ (v2_funct_1 @ X19)
% 4.19/4.42          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 4.19/4.42              = (k6_relat_1 @ (k2_relat_1 @ X19)))
% 4.19/4.42          | ~ (v1_funct_1 @ X19)
% 4.19/4.42          | ~ (v1_relat_1 @ X19))),
% 4.19/4.42      inference('cnf', [status(esa)], [t61_funct_1])).
% 4.19/4.42  thf('30', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 4.19/4.42      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.19/4.42  thf('31', plain,
% 4.19/4.42      (![X19 : $i]:
% 4.19/4.42         (~ (v2_funct_1 @ X19)
% 4.19/4.42          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 4.19/4.42              = (k6_partfun1 @ (k2_relat_1 @ X19)))
% 4.19/4.42          | ~ (v1_funct_1 @ X19)
% 4.19/4.42          | ~ (v1_relat_1 @ X19))),
% 4.19/4.42      inference('demod', [status(thm)], ['29', '30'])).
% 4.19/4.42  thf('32', plain,
% 4.19/4.42      (![X13 : $i]:
% 4.19/4.42         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 4.19/4.42          | ~ (v1_funct_1 @ X13)
% 4.19/4.42          | ~ (v1_relat_1 @ X13))),
% 4.19/4.42      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.19/4.42  thf('33', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf(redefinition_k2_relset_1, axiom,
% 4.19/4.42    (![A:$i,B:$i,C:$i]:
% 4.19/4.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.19/4.42       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.19/4.42  thf('34', plain,
% 4.19/4.42      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.19/4.42         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 4.19/4.42          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 4.19/4.42      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.19/4.42  thf('35', plain,
% 4.19/4.42      (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 4.19/4.42      inference('sup-', [status(thm)], ['33', '34'])).
% 4.19/4.42  thf('36', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('37', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.19/4.42      inference('sup+', [status(thm)], ['35', '36'])).
% 4.19/4.42  thf('38', plain,
% 4.19/4.42      (![X13 : $i]:
% 4.19/4.42         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 4.19/4.42          | ~ (v1_funct_1 @ X13)
% 4.19/4.42          | ~ (v1_relat_1 @ X13))),
% 4.19/4.42      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.19/4.42  thf(t55_funct_1, axiom,
% 4.19/4.42    (![A:$i]:
% 4.19/4.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.19/4.42       ( ( v2_funct_1 @ A ) =>
% 4.19/4.42         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 4.19/4.42           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 4.19/4.42  thf('39', plain,
% 4.19/4.42      (![X18 : $i]:
% 4.19/4.42         (~ (v2_funct_1 @ X18)
% 4.19/4.42          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 4.19/4.42          | ~ (v1_funct_1 @ X18)
% 4.19/4.42          | ~ (v1_relat_1 @ X18))),
% 4.19/4.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.19/4.42  thf(t78_relat_1, axiom,
% 4.19/4.42    (![A:$i]:
% 4.19/4.42     ( ( v1_relat_1 @ A ) =>
% 4.19/4.42       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 4.19/4.42  thf('40', plain,
% 4.19/4.42      (![X11 : $i]:
% 4.19/4.42         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 4.19/4.42          | ~ (v1_relat_1 @ X11))),
% 4.19/4.42      inference('cnf', [status(esa)], [t78_relat_1])).
% 4.19/4.42  thf('41', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 4.19/4.42      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.19/4.42  thf('42', plain,
% 4.19/4.42      (![X11 : $i]:
% 4.19/4.42         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 4.19/4.42          | ~ (v1_relat_1 @ X11))),
% 4.19/4.42      inference('demod', [status(thm)], ['40', '41'])).
% 4.19/4.42  thf('43', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 4.19/4.42            = (k2_funct_1 @ X0))
% 4.19/4.42          | ~ (v1_relat_1 @ X0)
% 4.19/4.42          | ~ (v1_funct_1 @ X0)
% 4.19/4.42          | ~ (v2_funct_1 @ X0)
% 4.19/4.42          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 4.19/4.42      inference('sup+', [status(thm)], ['39', '42'])).
% 4.19/4.42  thf('44', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (~ (v1_relat_1 @ X0)
% 4.19/4.42          | ~ (v1_funct_1 @ X0)
% 4.19/4.42          | ~ (v2_funct_1 @ X0)
% 4.19/4.42          | ~ (v1_funct_1 @ X0)
% 4.19/4.42          | ~ (v1_relat_1 @ X0)
% 4.19/4.42          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 4.19/4.42              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 4.19/4.42      inference('sup-', [status(thm)], ['38', '43'])).
% 4.19/4.42  thf('45', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 4.19/4.42            = (k2_funct_1 @ X0))
% 4.19/4.42          | ~ (v2_funct_1 @ X0)
% 4.19/4.42          | ~ (v1_funct_1 @ X0)
% 4.19/4.42          | ~ (v1_relat_1 @ X0))),
% 4.19/4.42      inference('simplify', [status(thm)], ['44'])).
% 4.19/4.42  thf('46', plain,
% 4.19/4.42      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 4.19/4.42          = (k2_funct_1 @ sk_C))
% 4.19/4.42        | ~ (v1_relat_1 @ sk_C)
% 4.19/4.42        | ~ (v1_funct_1 @ sk_C)
% 4.19/4.42        | ~ (v2_funct_1 @ sk_C))),
% 4.19/4.42      inference('sup+', [status(thm)], ['37', '45'])).
% 4.19/4.42  thf('47', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf(cc2_relat_1, axiom,
% 4.19/4.42    (![A:$i]:
% 4.19/4.42     ( ( v1_relat_1 @ A ) =>
% 4.19/4.42       ( ![B:$i]:
% 4.19/4.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.19/4.42  thf('48', plain,
% 4.19/4.42      (![X3 : $i, X4 : $i]:
% 4.19/4.42         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 4.19/4.42          | (v1_relat_1 @ X3)
% 4.19/4.42          | ~ (v1_relat_1 @ X4))),
% 4.19/4.42      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.19/4.42  thf('49', plain,
% 4.19/4.42      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)) | (v1_relat_1 @ sk_C))),
% 4.19/4.42      inference('sup-', [status(thm)], ['47', '48'])).
% 4.19/4.42  thf(fc6_relat_1, axiom,
% 4.19/4.42    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.19/4.42  thf('50', plain,
% 4.19/4.42      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 4.19/4.42      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.19/4.42  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 4.19/4.42      inference('demod', [status(thm)], ['49', '50'])).
% 4.19/4.42  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('54', plain,
% 4.19/4.42      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 4.19/4.42         = (k2_funct_1 @ sk_C))),
% 4.19/4.42      inference('demod', [status(thm)], ['46', '51', '52', '53'])).
% 4.19/4.42  thf(t55_relat_1, axiom,
% 4.19/4.42    (![A:$i]:
% 4.19/4.42     ( ( v1_relat_1 @ A ) =>
% 4.19/4.42       ( ![B:$i]:
% 4.19/4.42         ( ( v1_relat_1 @ B ) =>
% 4.19/4.42           ( ![C:$i]:
% 4.19/4.42             ( ( v1_relat_1 @ C ) =>
% 4.19/4.42               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 4.19/4.42                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 4.19/4.42  thf('55', plain,
% 4.19/4.42      (![X8 : $i, X9 : $i, X10 : $i]:
% 4.19/4.42         (~ (v1_relat_1 @ X8)
% 4.19/4.42          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 4.19/4.42              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 4.19/4.42          | ~ (v1_relat_1 @ X10)
% 4.19/4.42          | ~ (v1_relat_1 @ X9))),
% 4.19/4.42      inference('cnf', [status(esa)], [t55_relat_1])).
% 4.19/4.42  thf('56', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 4.19/4.42            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 4.19/4.42               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 4.19/4.42          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 4.19/4.42          | ~ (v1_relat_1 @ X0)
% 4.19/4.42          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.19/4.42      inference('sup+', [status(thm)], ['54', '55'])).
% 4.19/4.42  thf(fc3_funct_1, axiom,
% 4.19/4.42    (![A:$i]:
% 4.19/4.42     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 4.19/4.42       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 4.19/4.42  thf('57', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 4.19/4.42      inference('cnf', [status(esa)], [fc3_funct_1])).
% 4.19/4.42  thf('58', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 4.19/4.42      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.19/4.42  thf('59', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 4.19/4.42      inference('demod', [status(thm)], ['57', '58'])).
% 4.19/4.42  thf('60', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 4.19/4.42            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 4.19/4.42               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 4.19/4.42          | ~ (v1_relat_1 @ X0)
% 4.19/4.42          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.19/4.42      inference('demod', [status(thm)], ['56', '59'])).
% 4.19/4.42  thf('61', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (~ (v1_relat_1 @ sk_C)
% 4.19/4.42          | ~ (v1_funct_1 @ sk_C)
% 4.19/4.42          | ~ (v1_relat_1 @ X0)
% 4.19/4.42          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 4.19/4.42              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 4.19/4.42                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 4.19/4.42      inference('sup-', [status(thm)], ['32', '60'])).
% 4.19/4.42  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 4.19/4.42      inference('demod', [status(thm)], ['49', '50'])).
% 4.19/4.42  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('64', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (~ (v1_relat_1 @ X0)
% 4.19/4.42          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 4.19/4.42              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 4.19/4.42                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 4.19/4.42      inference('demod', [status(thm)], ['61', '62', '63'])).
% 4.19/4.42  thf('65', plain,
% 4.19/4.42      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 4.19/4.42          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 4.19/4.42             (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 4.19/4.42        | ~ (v1_relat_1 @ sk_C)
% 4.19/4.42        | ~ (v1_funct_1 @ sk_C)
% 4.19/4.42        | ~ (v2_funct_1 @ sk_C)
% 4.19/4.42        | ~ (v1_relat_1 @ sk_C))),
% 4.19/4.42      inference('sup+', [status(thm)], ['31', '64'])).
% 4.19/4.42  thf('66', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.19/4.42      inference('sup+', [status(thm)], ['35', '36'])).
% 4.19/4.42  thf(t67_funct_1, axiom,
% 4.19/4.42    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 4.19/4.42  thf('67', plain,
% 4.19/4.42      (![X22 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X22)) = (k6_relat_1 @ X22))),
% 4.19/4.42      inference('cnf', [status(esa)], [t67_funct_1])).
% 4.19/4.42  thf('68', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 4.19/4.42      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.19/4.42  thf('69', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 4.19/4.42      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.19/4.42  thf('70', plain,
% 4.19/4.42      (![X22 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X22)) = (k6_partfun1 @ X22))),
% 4.19/4.42      inference('demod', [status(thm)], ['67', '68', '69'])).
% 4.19/4.42  thf('71', plain,
% 4.19/4.42      (![X19 : $i]:
% 4.19/4.42         (~ (v2_funct_1 @ X19)
% 4.19/4.42          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 4.19/4.42              = (k6_partfun1 @ (k2_relat_1 @ X19)))
% 4.19/4.42          | ~ (v1_funct_1 @ X19)
% 4.19/4.42          | ~ (v1_relat_1 @ X19))),
% 4.19/4.42      inference('demod', [status(thm)], ['29', '30'])).
% 4.19/4.42  thf('72', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 4.19/4.42            = (k6_partfun1 @ (k2_relat_1 @ (k6_partfun1 @ X0))))
% 4.19/4.42          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 4.19/4.42          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 4.19/4.42          | ~ (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 4.19/4.42      inference('sup+', [status(thm)], ['70', '71'])).
% 4.19/4.42  thf('73', plain,
% 4.19/4.42      (![X22 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X22)) = (k6_partfun1 @ X22))),
% 4.19/4.42      inference('demod', [status(thm)], ['67', '68', '69'])).
% 4.19/4.42  thf('74', plain,
% 4.19/4.42      (![X18 : $i]:
% 4.19/4.42         (~ (v2_funct_1 @ X18)
% 4.19/4.42          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 4.19/4.42          | ~ (v1_funct_1 @ X18)
% 4.19/4.42          | ~ (v1_relat_1 @ X18))),
% 4.19/4.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.19/4.42  thf('75', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (((k1_relat_1 @ (k6_partfun1 @ X0))
% 4.19/4.42            = (k2_relat_1 @ (k6_partfun1 @ X0)))
% 4.19/4.42          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 4.19/4.42          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 4.19/4.42          | ~ (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 4.19/4.42      inference('sup+', [status(thm)], ['73', '74'])).
% 4.19/4.42  thf('76', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 4.19/4.42      inference('demod', [status(thm)], ['57', '58'])).
% 4.19/4.42  thf('77', plain, (![X15 : $i]: (v1_funct_1 @ (k6_relat_1 @ X15))),
% 4.19/4.42      inference('cnf', [status(esa)], [fc3_funct_1])).
% 4.19/4.42  thf('78', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 4.19/4.42      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.19/4.42  thf('79', plain, (![X15 : $i]: (v1_funct_1 @ (k6_partfun1 @ X15))),
% 4.19/4.42      inference('demod', [status(thm)], ['77', '78'])).
% 4.19/4.42  thf(fc4_funct_1, axiom,
% 4.19/4.42    (![A:$i]:
% 4.19/4.42     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 4.19/4.42       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 4.19/4.42  thf('80', plain, (![X17 : $i]: (v2_funct_1 @ (k6_relat_1 @ X17))),
% 4.19/4.42      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.19/4.42  thf('81', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 4.19/4.42      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.19/4.42  thf('82', plain, (![X17 : $i]: (v2_funct_1 @ (k6_partfun1 @ X17))),
% 4.19/4.42      inference('demod', [status(thm)], ['80', '81'])).
% 4.19/4.42  thf('83', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         ((k1_relat_1 @ (k6_partfun1 @ X0)) = (k2_relat_1 @ (k6_partfun1 @ X0)))),
% 4.19/4.42      inference('demod', [status(thm)], ['75', '76', '79', '82'])).
% 4.19/4.42  thf('84', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 4.19/4.42      inference('demod', [status(thm)], ['57', '58'])).
% 4.19/4.42  thf('85', plain, (![X15 : $i]: (v1_funct_1 @ (k6_partfun1 @ X15))),
% 4.19/4.42      inference('demod', [status(thm)], ['77', '78'])).
% 4.19/4.42  thf('86', plain, (![X17 : $i]: (v2_funct_1 @ (k6_partfun1 @ X17))),
% 4.19/4.42      inference('demod', [status(thm)], ['80', '81'])).
% 4.19/4.42  thf('87', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 4.19/4.42           = (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ X0))))),
% 4.19/4.42      inference('demod', [status(thm)], ['72', '83', '84', '85', '86'])).
% 4.19/4.42  thf('88', plain, ((v1_relat_1 @ sk_C)),
% 4.19/4.42      inference('demod', [status(thm)], ['49', '50'])).
% 4.19/4.42  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('90', plain, ((v2_funct_1 @ sk_C)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 4.19/4.42      inference('demod', [status(thm)], ['49', '50'])).
% 4.19/4.42  thf('92', plain,
% 4.19/4.42      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 4.19/4.42         = (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ sk_B))))),
% 4.19/4.42      inference('demod', [status(thm)],
% 4.19/4.42                ['65', '66', '87', '88', '89', '90', '91'])).
% 4.19/4.42  thf('93', plain,
% 4.19/4.42      (![X19 : $i]:
% 4.19/4.42         (~ (v2_funct_1 @ X19)
% 4.19/4.42          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 4.19/4.42              = (k6_partfun1 @ (k2_relat_1 @ X19)))
% 4.19/4.42          | ~ (v1_funct_1 @ X19)
% 4.19/4.42          | ~ (v1_relat_1 @ X19))),
% 4.19/4.42      inference('demod', [status(thm)], ['29', '30'])).
% 4.19/4.42  thf('94', plain,
% 4.19/4.42      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 4.19/4.42         = (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ sk_B))))),
% 4.19/4.42      inference('demod', [status(thm)],
% 4.19/4.42                ['65', '66', '87', '88', '89', '90', '91'])).
% 4.19/4.42  thf('95', plain,
% 4.19/4.42      ((((k6_partfun1 @ (k2_relat_1 @ sk_C))
% 4.19/4.42          = (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ sk_B))))
% 4.19/4.42        | ~ (v1_relat_1 @ sk_C)
% 4.19/4.42        | ~ (v1_funct_1 @ sk_C)
% 4.19/4.42        | ~ (v2_funct_1 @ sk_C))),
% 4.19/4.42      inference('sup+', [status(thm)], ['93', '94'])).
% 4.19/4.42  thf('96', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.19/4.42      inference('sup+', [status(thm)], ['35', '36'])).
% 4.19/4.42  thf('97', plain, ((v1_relat_1 @ sk_C)),
% 4.19/4.42      inference('demod', [status(thm)], ['49', '50'])).
% 4.19/4.42  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('99', plain, ((v2_funct_1 @ sk_C)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('100', plain,
% 4.19/4.42      (((k6_partfun1 @ sk_B)
% 4.19/4.42         = (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ sk_B))))),
% 4.19/4.42      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 4.19/4.42  thf('101', plain,
% 4.19/4.42      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 4.19/4.42      inference('demod', [status(thm)], ['92', '100'])).
% 4.19/4.42  thf('102', plain,
% 4.19/4.42      (![X8 : $i, X9 : $i, X10 : $i]:
% 4.19/4.42         (~ (v1_relat_1 @ X8)
% 4.19/4.42          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 4.19/4.42              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 4.19/4.42          | ~ (v1_relat_1 @ X10)
% 4.19/4.42          | ~ (v1_relat_1 @ X9))),
% 4.19/4.42      inference('cnf', [status(esa)], [t55_relat_1])).
% 4.19/4.42  thf('103', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 4.19/4.42            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 4.19/4.42          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.19/4.42          | ~ (v1_relat_1 @ X0)
% 4.19/4.42          | ~ (v1_relat_1 @ sk_C))),
% 4.19/4.42      inference('sup+', [status(thm)], ['101', '102'])).
% 4.19/4.42  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 4.19/4.42      inference('demod', [status(thm)], ['49', '50'])).
% 4.19/4.42  thf('105', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 4.19/4.42            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 4.19/4.42          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.19/4.42          | ~ (v1_relat_1 @ X0))),
% 4.19/4.42      inference('demod', [status(thm)], ['103', '104'])).
% 4.19/4.42  thf('106', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (~ (v1_relat_1 @ sk_C)
% 4.19/4.42          | ~ (v1_funct_1 @ sk_C)
% 4.19/4.42          | ~ (v1_relat_1 @ X0)
% 4.19/4.42          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 4.19/4.42              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 4.19/4.42      inference('sup-', [status(thm)], ['28', '105'])).
% 4.19/4.42  thf('107', plain, ((v1_relat_1 @ sk_C)),
% 4.19/4.42      inference('demod', [status(thm)], ['49', '50'])).
% 4.19/4.42  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('109', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (~ (v1_relat_1 @ X0)
% 4.19/4.42          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 4.19/4.42              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 4.19/4.42      inference('demod', [status(thm)], ['106', '107', '108'])).
% 4.19/4.42  thf('110', plain,
% 4.19/4.42      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 4.19/4.42          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A_1)))
% 4.19/4.42        | ~ (v1_relat_1 @ sk_D))),
% 4.19/4.42      inference('sup+', [status(thm)], ['27', '109'])).
% 4.19/4.42  thf('111', plain,
% 4.19/4.42      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 4.19/4.42        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 4.19/4.42        (k6_partfun1 @ sk_A_1))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('112', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf(t24_funct_2, axiom,
% 4.19/4.42    (![A:$i,B:$i,C:$i]:
% 4.19/4.42     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.19/4.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.19/4.42       ( ![D:$i]:
% 4.19/4.42         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.19/4.42             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.19/4.42           ( ( r2_relset_1 @
% 4.19/4.42               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 4.19/4.42               ( k6_partfun1 @ B ) ) =>
% 4.19/4.42             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 4.19/4.42  thf('113', plain,
% 4.19/4.42      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 4.19/4.42         (~ (v1_funct_1 @ X59)
% 4.19/4.42          | ~ (v1_funct_2 @ X59 @ X60 @ X61)
% 4.19/4.42          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 4.19/4.42          | ~ (r2_relset_1 @ X60 @ X60 @ 
% 4.19/4.42               (k1_partfun1 @ X60 @ X61 @ X61 @ X60 @ X59 @ X62) @ 
% 4.19/4.42               (k6_partfun1 @ X60))
% 4.19/4.42          | ((k2_relset_1 @ X61 @ X60 @ X62) = (X60))
% 4.19/4.42          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X60)))
% 4.19/4.42          | ~ (v1_funct_2 @ X62 @ X61 @ X60)
% 4.19/4.42          | ~ (v1_funct_1 @ X62))),
% 4.19/4.42      inference('cnf', [status(esa)], [t24_funct_2])).
% 4.19/4.42  thf('114', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (~ (v1_funct_1 @ X0)
% 4.19/4.42          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 4.19/4.42          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 4.19/4.42          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 4.19/4.42          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 4.19/4.42               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 4.19/4.42               (k6_partfun1 @ sk_A_1))
% 4.19/4.42          | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 4.19/4.42          | ~ (v1_funct_1 @ sk_C))),
% 4.19/4.42      inference('sup-', [status(thm)], ['112', '113'])).
% 4.19/4.42  thf('115', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('117', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (~ (v1_funct_1 @ X0)
% 4.19/4.42          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 4.19/4.42          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 4.19/4.42          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 4.19/4.42          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 4.19/4.42               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 4.19/4.42               (k6_partfun1 @ sk_A_1)))),
% 4.19/4.42      inference('demod', [status(thm)], ['114', '115', '116'])).
% 4.19/4.42  thf('118', plain,
% 4.19/4.42      ((((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (sk_A_1))
% 4.19/4.42        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 4.19/4.42        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 4.19/4.42        | ~ (v1_funct_1 @ sk_D))),
% 4.19/4.42      inference('sup-', [status(thm)], ['111', '117'])).
% 4.19/4.42  thf('119', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('120', plain,
% 4.19/4.42      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.19/4.42         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 4.19/4.42          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 4.19/4.42      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.19/4.42  thf('121', plain,
% 4.19/4.42      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 4.19/4.42      inference('sup-', [status(thm)], ['119', '120'])).
% 4.19/4.42  thf('122', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('123', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('124', plain, ((v1_funct_1 @ sk_D)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('125', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 4.19/4.42      inference('demod', [status(thm)], ['118', '121', '122', '123', '124'])).
% 4.19/4.42  thf(t169_relat_1, axiom,
% 4.19/4.42    (![A:$i]:
% 4.19/4.42     ( ( v1_relat_1 @ A ) =>
% 4.19/4.42       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 4.19/4.42  thf('126', plain,
% 4.19/4.42      (![X7 : $i]:
% 4.19/4.42         (((k10_relat_1 @ X7 @ (k2_relat_1 @ X7)) = (k1_relat_1 @ X7))
% 4.19/4.42          | ~ (v1_relat_1 @ X7))),
% 4.19/4.42      inference('cnf', [status(esa)], [t169_relat_1])).
% 4.19/4.42  thf('127', plain,
% 4.19/4.42      ((((k10_relat_1 @ sk_D @ sk_A_1) = (k1_relat_1 @ sk_D))
% 4.19/4.42        | ~ (v1_relat_1 @ sk_D))),
% 4.19/4.42      inference('sup+', [status(thm)], ['125', '126'])).
% 4.19/4.42  thf('128', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf(t38_relset_1, axiom,
% 4.19/4.42    (![A:$i,B:$i,C:$i]:
% 4.19/4.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.19/4.42       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 4.19/4.42         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.19/4.42  thf('129', plain,
% 4.19/4.42      (![X35 : $i, X36 : $i, X37 : $i]:
% 4.19/4.42         (((k8_relset_1 @ X35 @ X36 @ X37 @ X36)
% 4.19/4.42            = (k1_relset_1 @ X35 @ X36 @ X37))
% 4.19/4.42          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 4.19/4.42      inference('cnf', [status(esa)], [t38_relset_1])).
% 4.19/4.42  thf('130', plain,
% 4.19/4.42      (((k8_relset_1 @ sk_B @ sk_A_1 @ sk_D @ sk_A_1)
% 4.19/4.42         = (k1_relset_1 @ sk_B @ sk_A_1 @ sk_D))),
% 4.19/4.42      inference('sup-', [status(thm)], ['128', '129'])).
% 4.19/4.42  thf('131', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf(redefinition_k8_relset_1, axiom,
% 4.19/4.42    (![A:$i,B:$i,C:$i,D:$i]:
% 4.19/4.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.19/4.42       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 4.19/4.42  thf('132', plain,
% 4.19/4.42      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 4.19/4.42         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 4.19/4.42          | ((k8_relset_1 @ X27 @ X28 @ X26 @ X29) = (k10_relat_1 @ X26 @ X29)))),
% 4.19/4.42      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 4.19/4.42  thf('133', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         ((k8_relset_1 @ sk_B @ sk_A_1 @ sk_D @ X0) = (k10_relat_1 @ sk_D @ X0))),
% 4.19/4.42      inference('sup-', [status(thm)], ['131', '132'])).
% 4.19/4.42  thf('134', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf(d1_funct_2, axiom,
% 4.19/4.42    (![A:$i,B:$i,C:$i]:
% 4.19/4.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.19/4.42       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.19/4.42           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.19/4.42             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.19/4.42         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.19/4.42           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.19/4.42             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.19/4.42  thf(zf_stmt_1, axiom,
% 4.19/4.42    (![C:$i,B:$i,A:$i]:
% 4.19/4.42     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.19/4.42       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.19/4.42  thf('135', plain,
% 4.19/4.42      (![X40 : $i, X41 : $i, X42 : $i]:
% 4.19/4.42         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 4.19/4.42          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 4.19/4.42          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.19/4.42  thf('136', plain,
% 4.19/4.42      ((~ (zip_tseitin_1 @ sk_D @ sk_A_1 @ sk_B)
% 4.19/4.42        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A_1 @ sk_D)))),
% 4.19/4.42      inference('sup-', [status(thm)], ['134', '135'])).
% 4.19/4.42  thf('137', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.19/4.42  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 4.19/4.42  thf(zf_stmt_4, axiom,
% 4.19/4.42    (![B:$i,A:$i]:
% 4.19/4.42     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.19/4.42       ( zip_tseitin_0 @ B @ A ) ))).
% 4.19/4.42  thf(zf_stmt_5, axiom,
% 4.19/4.42    (![A:$i,B:$i,C:$i]:
% 4.19/4.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.19/4.42       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.19/4.42         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.19/4.42           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.19/4.42             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.19/4.42  thf('138', plain,
% 4.19/4.42      (![X43 : $i, X44 : $i, X45 : $i]:
% 4.19/4.42         (~ (zip_tseitin_0 @ X43 @ X44)
% 4.19/4.42          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 4.19/4.42          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.19/4.42  thf('139', plain,
% 4.19/4.42      (((zip_tseitin_1 @ sk_D @ sk_A_1 @ sk_B)
% 4.19/4.42        | ~ (zip_tseitin_0 @ sk_A_1 @ sk_B))),
% 4.19/4.42      inference('sup-', [status(thm)], ['137', '138'])).
% 4.19/4.42  thf('140', plain,
% 4.19/4.42      (![X38 : $i, X39 : $i]:
% 4.19/4.42         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.19/4.42  thf(l13_xboole_0, axiom,
% 4.19/4.42    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.19/4.42  thf('141', plain,
% 4.19/4.42      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.19/4.42      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.19/4.42  thf('142', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.19/4.42         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X2) | ~ (v1_xboole_0 @ X1))),
% 4.19/4.42      inference('sup+', [status(thm)], ['140', '141'])).
% 4.19/4.42  thf('143', plain, (((sk_A_1) != (k1_xboole_0))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('144', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i]:
% 4.19/4.42         (((X0) != (k1_xboole_0))
% 4.19/4.42          | ~ (v1_xboole_0 @ X0)
% 4.19/4.42          | (zip_tseitin_0 @ sk_A_1 @ X1))),
% 4.19/4.42      inference('sup-', [status(thm)], ['142', '143'])).
% 4.19/4.42  thf('145', plain,
% 4.19/4.42      (![X1 : $i]:
% 4.19/4.42         ((zip_tseitin_0 @ sk_A_1 @ X1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 4.19/4.42      inference('simplify', [status(thm)], ['144'])).
% 4.19/4.42  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 4.19/4.42  thf('146', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 4.19/4.42      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 4.19/4.42  thf('147', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 4.19/4.42      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 4.19/4.42  thf('148', plain,
% 4.19/4.42      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.19/4.42      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.19/4.42  thf('149', plain, (((o_0_0_xboole_0) = (k1_xboole_0))),
% 4.19/4.42      inference('sup-', [status(thm)], ['147', '148'])).
% 4.19/4.42  thf('150', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.19/4.42      inference('demod', [status(thm)], ['146', '149'])).
% 4.19/4.42  thf('151', plain, (![X1 : $i]: (zip_tseitin_0 @ sk_A_1 @ X1)),
% 4.19/4.42      inference('simplify_reflect+', [status(thm)], ['145', '150'])).
% 4.19/4.42  thf('152', plain, ((zip_tseitin_1 @ sk_D @ sk_A_1 @ sk_B)),
% 4.19/4.42      inference('demod', [status(thm)], ['139', '151'])).
% 4.19/4.42  thf('153', plain, (((sk_B) = (k1_relset_1 @ sk_B @ sk_A_1 @ sk_D))),
% 4.19/4.42      inference('demod', [status(thm)], ['136', '152'])).
% 4.19/4.42  thf('154', plain, (((k10_relat_1 @ sk_D @ sk_A_1) = (sk_B))),
% 4.19/4.42      inference('demod', [status(thm)], ['130', '133', '153'])).
% 4.19/4.42  thf('155', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('156', plain,
% 4.19/4.42      (![X3 : $i, X4 : $i]:
% 4.19/4.42         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 4.19/4.42          | (v1_relat_1 @ X3)
% 4.19/4.42          | ~ (v1_relat_1 @ X4))),
% 4.19/4.42      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.19/4.42  thf('157', plain,
% 4.19/4.42      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)) | (v1_relat_1 @ sk_D))),
% 4.19/4.42      inference('sup-', [status(thm)], ['155', '156'])).
% 4.19/4.42  thf('158', plain,
% 4.19/4.42      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 4.19/4.42      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.19/4.42  thf('159', plain, ((v1_relat_1 @ sk_D)),
% 4.19/4.42      inference('demod', [status(thm)], ['157', '158'])).
% 4.19/4.42  thf('160', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 4.19/4.42      inference('demod', [status(thm)], ['127', '154', '159'])).
% 4.19/4.42  thf('161', plain,
% 4.19/4.42      (![X11 : $i]:
% 4.19/4.42         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 4.19/4.42          | ~ (v1_relat_1 @ X11))),
% 4.19/4.42      inference('demod', [status(thm)], ['40', '41'])).
% 4.19/4.42  thf('162', plain,
% 4.19/4.42      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 4.19/4.42        | ~ (v1_relat_1 @ sk_D))),
% 4.19/4.42      inference('sup+', [status(thm)], ['160', '161'])).
% 4.19/4.42  thf('163', plain, ((v1_relat_1 @ sk_D)),
% 4.19/4.42      inference('demod', [status(thm)], ['157', '158'])).
% 4.19/4.42  thf('164', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 4.19/4.42      inference('demod', [status(thm)], ['162', '163'])).
% 4.19/4.42  thf('165', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('166', plain,
% 4.19/4.42      (![X35 : $i, X36 : $i, X37 : $i]:
% 4.19/4.42         (((k8_relset_1 @ X35 @ X36 @ X37 @ X36)
% 4.19/4.42            = (k1_relset_1 @ X35 @ X36 @ X37))
% 4.19/4.42          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 4.19/4.42      inference('cnf', [status(esa)], [t38_relset_1])).
% 4.19/4.42  thf('167', plain,
% 4.19/4.42      (((k8_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_B)
% 4.19/4.42         = (k1_relset_1 @ sk_A_1 @ sk_B @ sk_C))),
% 4.19/4.42      inference('sup-', [status(thm)], ['165', '166'])).
% 4.19/4.42  thf('168', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('169', plain,
% 4.19/4.42      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 4.19/4.42         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 4.19/4.42          | ((k8_relset_1 @ X27 @ X28 @ X26 @ X29) = (k10_relat_1 @ X26 @ X29)))),
% 4.19/4.42      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 4.19/4.42  thf('170', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         ((k8_relset_1 @ sk_A_1 @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 4.19/4.42      inference('sup-', [status(thm)], ['168', '169'])).
% 4.19/4.42  thf('171', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('172', plain,
% 4.19/4.42      (![X40 : $i, X41 : $i, X42 : $i]:
% 4.19/4.42         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 4.19/4.42          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 4.19/4.42          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.19/4.42  thf('173', plain,
% 4.19/4.42      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 4.19/4.42        | ((sk_A_1) = (k1_relset_1 @ sk_A_1 @ sk_B @ sk_C)))),
% 4.19/4.42      inference('sup-', [status(thm)], ['171', '172'])).
% 4.19/4.42  thf('174', plain,
% 4.19/4.42      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('175', plain,
% 4.19/4.42      (![X43 : $i, X44 : $i, X45 : $i]:
% 4.19/4.42         (~ (zip_tseitin_0 @ X43 @ X44)
% 4.19/4.42          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 4.19/4.42          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.19/4.42  thf('176', plain,
% 4.19/4.42      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 4.19/4.42        | ~ (zip_tseitin_0 @ sk_B @ sk_A_1))),
% 4.19/4.42      inference('sup-', [status(thm)], ['174', '175'])).
% 4.19/4.42  thf('177', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.19/4.42         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X2) | ~ (v1_xboole_0 @ X1))),
% 4.19/4.42      inference('sup+', [status(thm)], ['140', '141'])).
% 4.19/4.42  thf('178', plain, (((sk_B) != (k1_xboole_0))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('179', plain,
% 4.19/4.42      (![X0 : $i, X1 : $i]:
% 4.19/4.42         (((X0) != (k1_xboole_0))
% 4.19/4.42          | ~ (v1_xboole_0 @ X0)
% 4.19/4.42          | (zip_tseitin_0 @ sk_B @ X1))),
% 4.19/4.42      inference('sup-', [status(thm)], ['177', '178'])).
% 4.19/4.42  thf('180', plain,
% 4.19/4.42      (![X1 : $i]:
% 4.19/4.42         ((zip_tseitin_0 @ sk_B @ X1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 4.19/4.42      inference('simplify', [status(thm)], ['179'])).
% 4.19/4.42  thf('181', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.19/4.42      inference('demod', [status(thm)], ['146', '149'])).
% 4.19/4.42  thf('182', plain, (![X1 : $i]: (zip_tseitin_0 @ sk_B @ X1)),
% 4.19/4.42      inference('simplify_reflect+', [status(thm)], ['180', '181'])).
% 4.19/4.42  thf('183', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)),
% 4.19/4.42      inference('demod', [status(thm)], ['176', '182'])).
% 4.19/4.42  thf('184', plain, (((sk_A_1) = (k1_relset_1 @ sk_A_1 @ sk_B @ sk_C))),
% 4.19/4.42      inference('demod', [status(thm)], ['173', '183'])).
% 4.19/4.42  thf('185', plain, (((k10_relat_1 @ sk_C @ sk_B) = (sk_A_1))),
% 4.19/4.42      inference('demod', [status(thm)], ['167', '170', '184'])).
% 4.19/4.42  thf('186', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.19/4.42      inference('sup+', [status(thm)], ['35', '36'])).
% 4.19/4.42  thf('187', plain,
% 4.19/4.42      (![X7 : $i]:
% 4.19/4.42         (((k10_relat_1 @ X7 @ (k2_relat_1 @ X7)) = (k1_relat_1 @ X7))
% 4.19/4.42          | ~ (v1_relat_1 @ X7))),
% 4.19/4.42      inference('cnf', [status(esa)], [t169_relat_1])).
% 4.19/4.42  thf('188', plain,
% 4.19/4.42      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 4.19/4.42        | ~ (v1_relat_1 @ sk_C))),
% 4.19/4.42      inference('sup+', [status(thm)], ['186', '187'])).
% 4.19/4.42  thf('189', plain, ((v1_relat_1 @ sk_C)),
% 4.19/4.42      inference('demod', [status(thm)], ['49', '50'])).
% 4.19/4.42  thf('190', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 4.19/4.42      inference('demod', [status(thm)], ['188', '189'])).
% 4.19/4.42  thf('191', plain, (((sk_A_1) = (k1_relat_1 @ sk_C))),
% 4.19/4.42      inference('sup+', [status(thm)], ['185', '190'])).
% 4.19/4.42  thf('192', plain,
% 4.19/4.42      (![X13 : $i]:
% 4.19/4.42         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 4.19/4.42          | ~ (v1_funct_1 @ X13)
% 4.19/4.42          | ~ (v1_relat_1 @ X13))),
% 4.19/4.42      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.19/4.42  thf('193', plain,
% 4.19/4.42      (![X18 : $i]:
% 4.19/4.42         (~ (v2_funct_1 @ X18)
% 4.19/4.42          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 4.19/4.42          | ~ (v1_funct_1 @ X18)
% 4.19/4.42          | ~ (v1_relat_1 @ X18))),
% 4.19/4.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.19/4.42  thf(t80_relat_1, axiom,
% 4.19/4.42    (![A:$i]:
% 4.19/4.42     ( ( v1_relat_1 @ A ) =>
% 4.19/4.42       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 4.19/4.42  thf('194', plain,
% 4.19/4.42      (![X12 : $i]:
% 4.19/4.42         (((k5_relat_1 @ X12 @ (k6_relat_1 @ (k2_relat_1 @ X12))) = (X12))
% 4.19/4.42          | ~ (v1_relat_1 @ X12))),
% 4.19/4.42      inference('cnf', [status(esa)], [t80_relat_1])).
% 4.19/4.42  thf('195', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 4.19/4.42      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.19/4.42  thf('196', plain,
% 4.19/4.42      (![X12 : $i]:
% 4.19/4.42         (((k5_relat_1 @ X12 @ (k6_partfun1 @ (k2_relat_1 @ X12))) = (X12))
% 4.19/4.42          | ~ (v1_relat_1 @ X12))),
% 4.19/4.42      inference('demod', [status(thm)], ['194', '195'])).
% 4.19/4.42  thf('197', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 4.19/4.42            = (k2_funct_1 @ X0))
% 4.19/4.42          | ~ (v1_relat_1 @ X0)
% 4.19/4.42          | ~ (v1_funct_1 @ X0)
% 4.19/4.42          | ~ (v2_funct_1 @ X0)
% 4.19/4.42          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 4.19/4.42      inference('sup+', [status(thm)], ['193', '196'])).
% 4.19/4.42  thf('198', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (~ (v1_relat_1 @ X0)
% 4.19/4.42          | ~ (v1_funct_1 @ X0)
% 4.19/4.42          | ~ (v2_funct_1 @ X0)
% 4.19/4.42          | ~ (v1_funct_1 @ X0)
% 4.19/4.42          | ~ (v1_relat_1 @ X0)
% 4.19/4.42          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 4.19/4.42              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 4.19/4.42      inference('sup-', [status(thm)], ['192', '197'])).
% 4.19/4.42  thf('199', plain,
% 4.19/4.42      (![X0 : $i]:
% 4.19/4.42         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 4.19/4.42            = (k2_funct_1 @ X0))
% 4.19/4.42          | ~ (v2_funct_1 @ X0)
% 4.19/4.42          | ~ (v1_funct_1 @ X0)
% 4.19/4.42          | ~ (v1_relat_1 @ X0))),
% 4.19/4.42      inference('simplify', [status(thm)], ['198'])).
% 4.19/4.42  thf('200', plain,
% 4.19/4.42      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A_1))
% 4.19/4.42          = (k2_funct_1 @ sk_C))
% 4.19/4.42        | ~ (v1_relat_1 @ sk_C)
% 4.19/4.42        | ~ (v1_funct_1 @ sk_C)
% 4.19/4.42        | ~ (v2_funct_1 @ sk_C))),
% 4.19/4.42      inference('sup+', [status(thm)], ['191', '199'])).
% 4.19/4.42  thf('201', plain, ((v1_relat_1 @ sk_C)),
% 4.19/4.42      inference('demod', [status(thm)], ['49', '50'])).
% 4.19/4.42  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('203', plain, ((v2_funct_1 @ sk_C)),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('204', plain,
% 4.19/4.42      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A_1))
% 4.19/4.42         = (k2_funct_1 @ sk_C))),
% 4.19/4.42      inference('demod', [status(thm)], ['200', '201', '202', '203'])).
% 4.19/4.42  thf('205', plain, ((v1_relat_1 @ sk_D)),
% 4.19/4.42      inference('demod', [status(thm)], ['157', '158'])).
% 4.19/4.42  thf('206', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 4.19/4.42      inference('demod', [status(thm)], ['110', '164', '204', '205'])).
% 4.19/4.42  thf('207', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 4.19/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.42  thf('208', plain, ($false),
% 4.19/4.42      inference('simplify_reflect-', [status(thm)], ['206', '207'])).
% 4.19/4.42  
% 4.19/4.42  % SZS output end Refutation
% 4.19/4.42  
% 4.19/4.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
