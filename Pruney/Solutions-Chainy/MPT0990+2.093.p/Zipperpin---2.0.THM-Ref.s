%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DdmcLM1rrt

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:10 EST 2020

% Result     : Theorem 3.77s
% Output     : Refutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 456 expanded)
%              Number of leaves         :   44 ( 155 expanded)
%              Depth                    :   19
%              Number of atoms          : 1968 (11554 expanded)
%              Number of equality atoms :  138 ( 801 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ X46 @ ( k2_funct_1 @ X46 ) )
        = ( k6_relat_1 @ X47 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
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
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X13 = X16 )
      | ~ ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('25',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('26',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
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

thf('30',plain,(
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

thf('31',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('32',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_relset_1 @ X33 @ X33 @ ( k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35 ) @ ( k6_relat_1 @ X33 ) )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 )
      | ( X13 != X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('40',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','41','42','43','44'])).

thf('46',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','45'])).

thf('47',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('49',plain,(
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

thf('50',plain,(
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

thf('51',plain,(
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
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('56',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['55','56','57','58','59','60'])).

thf('62',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X38 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('64',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X36: $i,X37: $i] :
      ( ( v2_funct_1 @ X37 )
      | ~ ( zip_tseitin_0 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('68',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['47','68'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('70',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('71',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('72',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('74',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['66','67'])).

thf('78',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['71','72','75','76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
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

thf('81',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('88',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['85','86','87'])).

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

thf('89',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X9 @ X8 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('90',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ X46 @ ( k2_funct_1 @ X46 ) )
        = ( k6_relat_1 @ X47 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('93',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('103',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('107',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['103','104','107','108','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['105','106'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X46 ) @ X46 )
        = ( k6_partfun1 @ X45 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('116',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('117',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X46 ) @ X46 )
        = ( k6_relat_1 @ X45 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['118','119','120','121','122'])).

thf('124',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['124','125'])).

thf(t59_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('127',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X7 ) @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('128',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('130',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['105','106'])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('136',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','110','111','112','113','133','134','135'])).

thf('137',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    sk_B
 != ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['137','138'])).

thf('140',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['78','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DdmcLM1rrt
% 0.13/0.32  % Computer   : n015.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 13:52:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 3.77/3.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.77/3.96  % Solved by: fo/fo7.sh
% 3.77/3.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.77/3.96  % done 592 iterations in 3.524s
% 3.77/3.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.77/3.96  % SZS output start Refutation
% 3.77/3.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.77/3.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.77/3.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.77/3.96  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.77/3.96  thf(sk_A_type, type, sk_A: $i).
% 3.77/3.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.77/3.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.77/3.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.77/3.96  thf(sk_D_type, type, sk_D: $i).
% 3.77/3.96  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.77/3.96  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 3.77/3.96  thf(sk_C_type, type, sk_C: $i).
% 3.77/3.96  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.77/3.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.77/3.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.77/3.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.77/3.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.77/3.96  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.77/3.96  thf(sk_B_type, type, sk_B: $i).
% 3.77/3.96  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.77/3.96  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.77/3.96  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.77/3.96  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.77/3.96  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.77/3.96  thf(t36_funct_2, conjecture,
% 3.77/3.96    (![A:$i,B:$i,C:$i]:
% 3.77/3.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.77/3.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.77/3.96       ( ![D:$i]:
% 3.77/3.96         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.77/3.96             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.77/3.96           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.77/3.96               ( r2_relset_1 @
% 3.77/3.96                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.77/3.96                 ( k6_partfun1 @ A ) ) & 
% 3.77/3.96               ( v2_funct_1 @ C ) ) =>
% 3.77/3.96             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.77/3.96               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 3.77/3.96  thf(zf_stmt_0, negated_conjecture,
% 3.77/3.96    (~( ![A:$i,B:$i,C:$i]:
% 3.77/3.96        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.77/3.96            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.77/3.96          ( ![D:$i]:
% 3.77/3.96            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.77/3.96                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.77/3.96              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.77/3.96                  ( r2_relset_1 @
% 3.77/3.96                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.77/3.96                    ( k6_partfun1 @ A ) ) & 
% 3.77/3.96                  ( v2_funct_1 @ C ) ) =>
% 3.77/3.96                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.77/3.96                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 3.77/3.96    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 3.77/3.96  thf('0', plain,
% 3.77/3.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf(t35_funct_2, axiom,
% 3.77/3.96    (![A:$i,B:$i,C:$i]:
% 3.77/3.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.77/3.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.77/3.96       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.77/3.96         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.77/3.96           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 3.77/3.96             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 3.77/3.96  thf('1', plain,
% 3.77/3.96      (![X45 : $i, X46 : $i, X47 : $i]:
% 3.77/3.96         (((X45) = (k1_xboole_0))
% 3.77/3.96          | ~ (v1_funct_1 @ X46)
% 3.77/3.96          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 3.77/3.96          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 3.77/3.96          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_partfun1 @ X47))
% 3.77/3.96          | ~ (v2_funct_1 @ X46)
% 3.77/3.96          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 3.77/3.96      inference('cnf', [status(esa)], [t35_funct_2])).
% 3.77/3.96  thf(redefinition_k6_partfun1, axiom,
% 3.77/3.96    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.77/3.96  thf('2', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 3.77/3.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.77/3.96  thf('3', plain,
% 3.77/3.96      (![X45 : $i, X46 : $i, X47 : $i]:
% 3.77/3.96         (((X45) = (k1_xboole_0))
% 3.77/3.96          | ~ (v1_funct_1 @ X46)
% 3.77/3.96          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 3.77/3.96          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 3.77/3.96          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_relat_1 @ X47))
% 3.77/3.96          | ~ (v2_funct_1 @ X46)
% 3.77/3.96          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 3.77/3.96      inference('demod', [status(thm)], ['1', '2'])).
% 3.77/3.96  thf('4', plain,
% 3.77/3.96      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 3.77/3.96        | ~ (v2_funct_1 @ sk_D)
% 3.77/3.96        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 3.77/3.96        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.77/3.96        | ~ (v1_funct_1 @ sk_D)
% 3.77/3.96        | ((sk_A) = (k1_xboole_0)))),
% 3.77/3.96      inference('sup-', [status(thm)], ['0', '3'])).
% 3.77/3.96  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('7', plain,
% 3.77/3.96      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 3.77/3.96        | ~ (v2_funct_1 @ sk_D)
% 3.77/3.96        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 3.77/3.96        | ((sk_A) = (k1_xboole_0)))),
% 3.77/3.96      inference('demod', [status(thm)], ['4', '5', '6'])).
% 3.77/3.96  thf('8', plain, (((sk_A) != (k1_xboole_0))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('9', plain,
% 3.77/3.96      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 3.77/3.96        | ~ (v2_funct_1 @ sk_D)
% 3.77/3.96        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 3.77/3.96      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 3.77/3.96  thf('10', plain,
% 3.77/3.96      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.77/3.96        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.77/3.96        (k6_partfun1 @ sk_A))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('11', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 3.77/3.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.77/3.96  thf('12', plain,
% 3.77/3.96      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.77/3.96        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.77/3.96        (k6_relat_1 @ sk_A))),
% 3.77/3.96      inference('demod', [status(thm)], ['10', '11'])).
% 3.77/3.96  thf('13', plain,
% 3.77/3.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('14', plain,
% 3.77/3.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf(dt_k1_partfun1, axiom,
% 3.77/3.96    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.77/3.96     ( ( ( v1_funct_1 @ E ) & 
% 3.77/3.96         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.77/3.96         ( v1_funct_1 @ F ) & 
% 3.77/3.96         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.77/3.96       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.77/3.96         ( m1_subset_1 @
% 3.77/3.96           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.77/3.96           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.77/3.96  thf('15', plain,
% 3.77/3.96      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.77/3.96         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 3.77/3.96          | ~ (v1_funct_1 @ X17)
% 3.77/3.96          | ~ (v1_funct_1 @ X20)
% 3.77/3.96          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.77/3.96          | (m1_subset_1 @ (k1_partfun1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20) @ 
% 3.77/3.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X22))))),
% 3.77/3.96      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.77/3.96  thf('16', plain,
% 3.77/3.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.77/3.96         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.77/3.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.77/3.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.77/3.96          | ~ (v1_funct_1 @ X1)
% 3.77/3.96          | ~ (v1_funct_1 @ sk_C))),
% 3.77/3.96      inference('sup-', [status(thm)], ['14', '15'])).
% 3.77/3.96  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('18', plain,
% 3.77/3.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.77/3.96         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.77/3.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.77/3.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.77/3.96          | ~ (v1_funct_1 @ X1))),
% 3.77/3.96      inference('demod', [status(thm)], ['16', '17'])).
% 3.77/3.96  thf('19', plain,
% 3.77/3.96      ((~ (v1_funct_1 @ sk_D)
% 3.77/3.96        | (m1_subset_1 @ 
% 3.77/3.96           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.77/3.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.77/3.96      inference('sup-', [status(thm)], ['13', '18'])).
% 3.77/3.96  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('21', plain,
% 3.77/3.96      ((m1_subset_1 @ 
% 3.77/3.96        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.77/3.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.77/3.96      inference('demod', [status(thm)], ['19', '20'])).
% 3.77/3.96  thf(redefinition_r2_relset_1, axiom,
% 3.77/3.96    (![A:$i,B:$i,C:$i,D:$i]:
% 3.77/3.96     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.77/3.96         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.77/3.96       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.77/3.96  thf('22', plain,
% 3.77/3.96      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 3.77/3.96         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 3.77/3.96          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 3.77/3.96          | ((X13) = (X16))
% 3.77/3.96          | ~ (r2_relset_1 @ X14 @ X15 @ X13 @ X16))),
% 3.77/3.96      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.77/3.96  thf('23', plain,
% 3.77/3.96      (![X0 : $i]:
% 3.77/3.96         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.77/3.96             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.77/3.96          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.77/3.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.77/3.96      inference('sup-', [status(thm)], ['21', '22'])).
% 3.77/3.96  thf('24', plain,
% 3.77/3.96      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 3.77/3.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.77/3.96        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.77/3.96            = (k6_relat_1 @ sk_A)))),
% 3.77/3.96      inference('sup-', [status(thm)], ['12', '23'])).
% 3.77/3.96  thf(dt_k6_partfun1, axiom,
% 3.77/3.96    (![A:$i]:
% 3.77/3.96     ( ( m1_subset_1 @
% 3.77/3.96         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.77/3.96       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.77/3.96  thf('25', plain,
% 3.77/3.96      (![X24 : $i]:
% 3.77/3.96         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 3.77/3.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 3.77/3.96      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.77/3.96  thf('26', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 3.77/3.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.77/3.96  thf('27', plain,
% 3.77/3.96      (![X24 : $i]:
% 3.77/3.96         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 3.77/3.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 3.77/3.96      inference('demod', [status(thm)], ['25', '26'])).
% 3.77/3.96  thf('28', plain,
% 3.77/3.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.77/3.96         = (k6_relat_1 @ sk_A))),
% 3.77/3.96      inference('demod', [status(thm)], ['24', '27'])).
% 3.77/3.96  thf('29', plain,
% 3.77/3.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf(t24_funct_2, axiom,
% 3.77/3.96    (![A:$i,B:$i,C:$i]:
% 3.77/3.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.77/3.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.77/3.96       ( ![D:$i]:
% 3.77/3.96         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.77/3.96             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.77/3.96           ( ( r2_relset_1 @
% 3.77/3.96               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.77/3.96               ( k6_partfun1 @ B ) ) =>
% 3.77/3.96             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.77/3.96  thf('30', plain,
% 3.77/3.96      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 3.77/3.96         (~ (v1_funct_1 @ X32)
% 3.77/3.96          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 3.77/3.96          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 3.77/3.96          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 3.77/3.96               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 3.77/3.96               (k6_partfun1 @ X33))
% 3.77/3.96          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 3.77/3.96          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 3.77/3.96          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 3.77/3.96          | ~ (v1_funct_1 @ X35))),
% 3.77/3.96      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.77/3.96  thf('31', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 3.77/3.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.77/3.96  thf('32', plain,
% 3.77/3.96      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 3.77/3.96         (~ (v1_funct_1 @ X32)
% 3.77/3.96          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 3.77/3.96          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 3.77/3.96          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 3.77/3.96               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 3.77/3.96               (k6_relat_1 @ X33))
% 3.77/3.96          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 3.77/3.96          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 3.77/3.96          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 3.77/3.96          | ~ (v1_funct_1 @ X35))),
% 3.77/3.96      inference('demod', [status(thm)], ['30', '31'])).
% 3.77/3.96  thf('33', plain,
% 3.77/3.96      (![X0 : $i]:
% 3.77/3.96         (~ (v1_funct_1 @ X0)
% 3.77/3.96          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.77/3.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.77/3.96          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.77/3.96          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.77/3.96               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.77/3.96               (k6_relat_1 @ sk_A))
% 3.77/3.96          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.77/3.96          | ~ (v1_funct_1 @ sk_C))),
% 3.77/3.96      inference('sup-', [status(thm)], ['29', '32'])).
% 3.77/3.96  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('36', plain,
% 3.77/3.96      (![X0 : $i]:
% 3.77/3.96         (~ (v1_funct_1 @ X0)
% 3.77/3.96          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.77/3.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.77/3.96          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.77/3.96          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.77/3.96               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.77/3.96               (k6_relat_1 @ sk_A)))),
% 3.77/3.96      inference('demod', [status(thm)], ['33', '34', '35'])).
% 3.77/3.96  thf('37', plain,
% 3.77/3.96      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 3.77/3.96           (k6_relat_1 @ sk_A))
% 3.77/3.96        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.77/3.96        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.77/3.96        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.77/3.96        | ~ (v1_funct_1 @ sk_D))),
% 3.77/3.96      inference('sup-', [status(thm)], ['28', '36'])).
% 3.77/3.96  thf('38', plain,
% 3.77/3.96      (![X24 : $i]:
% 3.77/3.96         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 3.77/3.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 3.77/3.96      inference('demod', [status(thm)], ['25', '26'])).
% 3.77/3.96  thf('39', plain,
% 3.77/3.96      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 3.77/3.96         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 3.77/3.96          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 3.77/3.96          | (r2_relset_1 @ X14 @ X15 @ X13 @ X16)
% 3.77/3.96          | ((X13) != (X16)))),
% 3.77/3.96      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.77/3.96  thf('40', plain,
% 3.77/3.96      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.77/3.96         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 3.77/3.96          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.77/3.96      inference('simplify', [status(thm)], ['39'])).
% 3.77/3.96  thf('41', plain,
% 3.77/3.96      (![X0 : $i]:
% 3.77/3.96         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 3.77/3.96      inference('sup-', [status(thm)], ['38', '40'])).
% 3.77/3.96  thf('42', plain,
% 3.77/3.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('43', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('45', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 3.77/3.96      inference('demod', [status(thm)], ['37', '41', '42', '43', '44'])).
% 3.77/3.96  thf('46', plain,
% 3.77/3.96      ((((sk_A) != (sk_A))
% 3.77/3.96        | ~ (v2_funct_1 @ sk_D)
% 3.77/3.96        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 3.77/3.96      inference('demod', [status(thm)], ['9', '45'])).
% 3.77/3.96  thf('47', plain,
% 3.77/3.96      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 3.77/3.96        | ~ (v2_funct_1 @ sk_D))),
% 3.77/3.96      inference('simplify', [status(thm)], ['46'])).
% 3.77/3.96  thf('48', plain,
% 3.77/3.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.77/3.96         = (k6_relat_1 @ sk_A))),
% 3.77/3.96      inference('demod', [status(thm)], ['24', '27'])).
% 3.77/3.96  thf('49', plain,
% 3.77/3.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf(t30_funct_2, axiom,
% 3.77/3.96    (![A:$i,B:$i,C:$i,D:$i]:
% 3.77/3.96     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.77/3.96         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 3.77/3.96       ( ![E:$i]:
% 3.77/3.96         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 3.77/3.96             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 3.77/3.96           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 3.77/3.96               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 3.77/3.96             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 3.77/3.96               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 3.77/3.96  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 3.77/3.96  thf(zf_stmt_2, axiom,
% 3.77/3.96    (![C:$i,B:$i]:
% 3.77/3.96     ( ( zip_tseitin_1 @ C @ B ) =>
% 3.77/3.96       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 3.77/3.96  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 3.77/3.96  thf(zf_stmt_4, axiom,
% 3.77/3.96    (![E:$i,D:$i]:
% 3.77/3.96     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 3.77/3.96  thf(zf_stmt_5, axiom,
% 3.77/3.96    (![A:$i,B:$i,C:$i,D:$i]:
% 3.77/3.96     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.77/3.96         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.77/3.96       ( ![E:$i]:
% 3.77/3.96         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.77/3.96             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.77/3.96           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 3.77/3.96               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 3.77/3.96             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 3.77/3.96  thf('50', plain,
% 3.77/3.96      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.77/3.96         (~ (v1_funct_1 @ X40)
% 3.77/3.96          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 3.77/3.96          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 3.77/3.96          | (zip_tseitin_0 @ X40 @ X43)
% 3.77/3.96          | ~ (v2_funct_1 @ (k1_partfun1 @ X44 @ X41 @ X41 @ X42 @ X43 @ X40))
% 3.77/3.96          | (zip_tseitin_1 @ X42 @ X41)
% 3.77/3.96          | ((k2_relset_1 @ X44 @ X41 @ X43) != (X41))
% 3.77/3.96          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X41)))
% 3.77/3.96          | ~ (v1_funct_2 @ X43 @ X44 @ X41)
% 3.77/3.96          | ~ (v1_funct_1 @ X43))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.77/3.96  thf('51', plain,
% 3.77/3.96      (![X0 : $i, X1 : $i]:
% 3.77/3.96         (~ (v1_funct_1 @ X0)
% 3.77/3.96          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.77/3.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.77/3.96          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 3.77/3.96          | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.77/3.96          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.77/3.96          | (zip_tseitin_0 @ sk_D @ X0)
% 3.77/3.96          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.77/3.96          | ~ (v1_funct_1 @ sk_D))),
% 3.77/3.96      inference('sup-', [status(thm)], ['49', '50'])).
% 3.77/3.96  thf('52', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('53', plain, ((v1_funct_1 @ sk_D)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('54', plain,
% 3.77/3.96      (![X0 : $i, X1 : $i]:
% 3.77/3.96         (~ (v1_funct_1 @ X0)
% 3.77/3.96          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.77/3.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.77/3.96          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 3.77/3.96          | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.77/3.96          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.77/3.96          | (zip_tseitin_0 @ sk_D @ X0))),
% 3.77/3.96      inference('demod', [status(thm)], ['51', '52', '53'])).
% 3.77/3.96  thf('55', plain,
% 3.77/3.96      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 3.77/3.96        | (zip_tseitin_0 @ sk_D @ sk_C)
% 3.77/3.96        | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.77/3.96        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 3.77/3.96        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.77/3.96        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.77/3.96        | ~ (v1_funct_1 @ sk_C))),
% 3.77/3.96      inference('sup-', [status(thm)], ['48', '54'])).
% 3.77/3.96  thf(fc4_funct_1, axiom,
% 3.77/3.96    (![A:$i]:
% 3.77/3.96     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.77/3.96       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.77/3.96  thf('56', plain, (![X3 : $i]: (v2_funct_1 @ (k6_relat_1 @ X3))),
% 3.77/3.96      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.77/3.96  thf('57', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('58', plain,
% 3.77/3.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('59', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('61', plain,
% 3.77/3.96      (((zip_tseitin_0 @ sk_D @ sk_C)
% 3.77/3.96        | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.77/3.96        | ((sk_B) != (sk_B)))),
% 3.77/3.96      inference('demod', [status(thm)], ['55', '56', '57', '58', '59', '60'])).
% 3.77/3.96  thf('62', plain,
% 3.77/3.96      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 3.77/3.96      inference('simplify', [status(thm)], ['61'])).
% 3.77/3.96  thf('63', plain,
% 3.77/3.96      (![X38 : $i, X39 : $i]:
% 3.77/3.96         (((X38) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X38 @ X39))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.77/3.96  thf('64', plain,
% 3.77/3.96      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.77/3.96      inference('sup-', [status(thm)], ['62', '63'])).
% 3.77/3.96  thf('65', plain, (((sk_A) != (k1_xboole_0))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('66', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 3.77/3.96      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 3.77/3.96  thf('67', plain,
% 3.77/3.96      (![X36 : $i, X37 : $i]:
% 3.77/3.96         ((v2_funct_1 @ X37) | ~ (zip_tseitin_0 @ X37 @ X36))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.77/3.96  thf('68', plain, ((v2_funct_1 @ sk_D)),
% 3.77/3.96      inference('sup-', [status(thm)], ['66', '67'])).
% 3.77/3.96  thf('69', plain,
% 3.77/3.96      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 3.77/3.96      inference('demod', [status(thm)], ['47', '68'])).
% 3.77/3.96  thf(t58_funct_1, axiom,
% 3.77/3.96    (![A:$i]:
% 3.77/3.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.77/3.96       ( ( v2_funct_1 @ A ) =>
% 3.77/3.96         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 3.77/3.96             ( k1_relat_1 @ A ) ) & 
% 3.77/3.96           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 3.77/3.96             ( k1_relat_1 @ A ) ) ) ) ))).
% 3.77/3.96  thf('70', plain,
% 3.77/3.96      (![X6 : $i]:
% 3.77/3.96         (~ (v2_funct_1 @ X6)
% 3.77/3.96          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ (k2_funct_1 @ X6)))
% 3.77/3.96              = (k1_relat_1 @ X6))
% 3.77/3.96          | ~ (v1_funct_1 @ X6)
% 3.77/3.96          | ~ (v1_relat_1 @ X6))),
% 3.77/3.96      inference('cnf', [status(esa)], [t58_funct_1])).
% 3.77/3.96  thf('71', plain,
% 3.77/3.96      ((((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 3.77/3.96        | ~ (v1_relat_1 @ sk_D)
% 3.77/3.96        | ~ (v1_funct_1 @ sk_D)
% 3.77/3.96        | ~ (v2_funct_1 @ sk_D))),
% 3.77/3.96      inference('sup+', [status(thm)], ['69', '70'])).
% 3.77/3.96  thf(t71_relat_1, axiom,
% 3.77/3.96    (![A:$i]:
% 3.77/3.96     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.77/3.96       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.77/3.96  thf('72', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 3.77/3.96      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.77/3.96  thf('73', plain,
% 3.77/3.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf(cc1_relset_1, axiom,
% 3.77/3.96    (![A:$i,B:$i,C:$i]:
% 3.77/3.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.77/3.96       ( v1_relat_1 @ C ) ))).
% 3.77/3.96  thf('74', plain,
% 3.77/3.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.77/3.96         ((v1_relat_1 @ X10)
% 3.77/3.96          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 3.77/3.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.77/3.96  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 3.77/3.96      inference('sup-', [status(thm)], ['73', '74'])).
% 3.77/3.96  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('77', plain, ((v2_funct_1 @ sk_D)),
% 3.77/3.96      inference('sup-', [status(thm)], ['66', '67'])).
% 3.77/3.96  thf('78', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 3.77/3.96      inference('demod', [status(thm)], ['71', '72', '75', '76', '77'])).
% 3.77/3.96  thf('79', plain,
% 3.77/3.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('80', plain,
% 3.77/3.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf(redefinition_k1_partfun1, axiom,
% 3.77/3.96    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.77/3.96     ( ( ( v1_funct_1 @ E ) & 
% 3.77/3.96         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.77/3.96         ( v1_funct_1 @ F ) & 
% 3.77/3.96         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.77/3.96       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.77/3.96  thf('81', plain,
% 3.77/3.96      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 3.77/3.96         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 3.77/3.96          | ~ (v1_funct_1 @ X25)
% 3.77/3.96          | ~ (v1_funct_1 @ X28)
% 3.77/3.96          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.77/3.96          | ((k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 3.77/3.96              = (k5_relat_1 @ X25 @ X28)))),
% 3.77/3.96      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.77/3.96  thf('82', plain,
% 3.77/3.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.77/3.96         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.77/3.96            = (k5_relat_1 @ sk_C @ X0))
% 3.77/3.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.77/3.96          | ~ (v1_funct_1 @ X0)
% 3.77/3.96          | ~ (v1_funct_1 @ sk_C))),
% 3.77/3.96      inference('sup-', [status(thm)], ['80', '81'])).
% 3.77/3.96  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('84', plain,
% 3.77/3.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.77/3.96         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.77/3.96            = (k5_relat_1 @ sk_C @ X0))
% 3.77/3.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.77/3.96          | ~ (v1_funct_1 @ X0))),
% 3.77/3.96      inference('demod', [status(thm)], ['82', '83'])).
% 3.77/3.96  thf('85', plain,
% 3.77/3.96      ((~ (v1_funct_1 @ sk_D)
% 3.77/3.96        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.77/3.96            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.77/3.96      inference('sup-', [status(thm)], ['79', '84'])).
% 3.77/3.96  thf('86', plain, ((v1_funct_1 @ sk_D)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('87', plain,
% 3.77/3.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.77/3.96         = (k6_relat_1 @ sk_A))),
% 3.77/3.96      inference('demod', [status(thm)], ['24', '27'])).
% 3.77/3.96  thf('88', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 3.77/3.96      inference('demod', [status(thm)], ['85', '86', '87'])).
% 3.77/3.96  thf(t63_funct_1, axiom,
% 3.77/3.96    (![A:$i]:
% 3.77/3.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.77/3.96       ( ![B:$i]:
% 3.77/3.96         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.77/3.96           ( ( ( v2_funct_1 @ A ) & 
% 3.77/3.96               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 3.77/3.96               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 3.77/3.96             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.77/3.96  thf('89', plain,
% 3.77/3.96      (![X8 : $i, X9 : $i]:
% 3.77/3.96         (~ (v1_relat_1 @ X8)
% 3.77/3.96          | ~ (v1_funct_1 @ X8)
% 3.77/3.96          | ((X8) = (k2_funct_1 @ X9))
% 3.77/3.96          | ((k5_relat_1 @ X9 @ X8) != (k6_relat_1 @ (k1_relat_1 @ X9)))
% 3.77/3.96          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X8))
% 3.77/3.96          | ~ (v2_funct_1 @ X9)
% 3.77/3.96          | ~ (v1_funct_1 @ X9)
% 3.77/3.96          | ~ (v1_relat_1 @ X9))),
% 3.77/3.96      inference('cnf', [status(esa)], [t63_funct_1])).
% 3.77/3.96  thf('90', plain,
% 3.77/3.96      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 3.77/3.96        | ~ (v1_relat_1 @ sk_C)
% 3.77/3.96        | ~ (v1_funct_1 @ sk_C)
% 3.77/3.96        | ~ (v2_funct_1 @ sk_C)
% 3.77/3.96        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 3.77/3.96        | ((sk_D) = (k2_funct_1 @ sk_C))
% 3.77/3.96        | ~ (v1_funct_1 @ sk_D)
% 3.77/3.96        | ~ (v1_relat_1 @ sk_D))),
% 3.77/3.96      inference('sup-', [status(thm)], ['88', '89'])).
% 3.77/3.96  thf('91', plain,
% 3.77/3.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('92', plain,
% 3.77/3.96      (![X45 : $i, X46 : $i, X47 : $i]:
% 3.77/3.96         (((X45) = (k1_xboole_0))
% 3.77/3.96          | ~ (v1_funct_1 @ X46)
% 3.77/3.96          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 3.77/3.96          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 3.77/3.96          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_relat_1 @ X47))
% 3.77/3.96          | ~ (v2_funct_1 @ X46)
% 3.77/3.96          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 3.77/3.96      inference('demod', [status(thm)], ['1', '2'])).
% 3.77/3.96  thf('93', plain,
% 3.77/3.96      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 3.77/3.96        | ~ (v2_funct_1 @ sk_C)
% 3.77/3.96        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 3.77/3.96        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.77/3.96        | ~ (v1_funct_1 @ sk_C)
% 3.77/3.96        | ((sk_B) = (k1_xboole_0)))),
% 3.77/3.96      inference('sup-', [status(thm)], ['91', '92'])).
% 3.77/3.96  thf('94', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('96', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('98', plain,
% 3.77/3.96      ((((sk_B) != (sk_B))
% 3.77/3.96        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 3.77/3.96        | ((sk_B) = (k1_xboole_0)))),
% 3.77/3.96      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 3.77/3.96  thf('99', plain,
% 3.77/3.96      ((((sk_B) = (k1_xboole_0))
% 3.77/3.96        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 3.77/3.96      inference('simplify', [status(thm)], ['98'])).
% 3.77/3.96  thf('100', plain, (((sk_B) != (k1_xboole_0))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('101', plain,
% 3.77/3.96      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 3.77/3.96      inference('simplify_reflect-', [status(thm)], ['99', '100'])).
% 3.77/3.96  thf('102', plain,
% 3.77/3.96      (![X6 : $i]:
% 3.77/3.96         (~ (v2_funct_1 @ X6)
% 3.77/3.96          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ (k2_funct_1 @ X6)))
% 3.77/3.96              = (k1_relat_1 @ X6))
% 3.77/3.96          | ~ (v1_funct_1 @ X6)
% 3.77/3.96          | ~ (v1_relat_1 @ X6))),
% 3.77/3.96      inference('cnf', [status(esa)], [t58_funct_1])).
% 3.77/3.96  thf('103', plain,
% 3.77/3.96      ((((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 3.77/3.96        | ~ (v1_relat_1 @ sk_C)
% 3.77/3.96        | ~ (v1_funct_1 @ sk_C)
% 3.77/3.96        | ~ (v2_funct_1 @ sk_C))),
% 3.77/3.96      inference('sup+', [status(thm)], ['101', '102'])).
% 3.77/3.96  thf('104', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 3.77/3.96      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.77/3.96  thf('105', plain,
% 3.77/3.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('106', plain,
% 3.77/3.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.77/3.96         ((v1_relat_1 @ X10)
% 3.77/3.96          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 3.77/3.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.77/3.96  thf('107', plain, ((v1_relat_1 @ sk_C)),
% 3.77/3.96      inference('sup-', [status(thm)], ['105', '106'])).
% 3.77/3.96  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('109', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('110', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 3.77/3.96      inference('demod', [status(thm)], ['103', '104', '107', '108', '109'])).
% 3.77/3.96  thf('111', plain, ((v1_relat_1 @ sk_C)),
% 3.77/3.96      inference('sup-', [status(thm)], ['105', '106'])).
% 3.77/3.96  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('113', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('114', plain,
% 3.77/3.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('115', plain,
% 3.77/3.96      (![X45 : $i, X46 : $i, X47 : $i]:
% 3.77/3.96         (((X45) = (k1_xboole_0))
% 3.77/3.96          | ~ (v1_funct_1 @ X46)
% 3.77/3.96          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 3.77/3.96          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 3.77/3.96          | ((k5_relat_1 @ (k2_funct_1 @ X46) @ X46) = (k6_partfun1 @ X45))
% 3.77/3.96          | ~ (v2_funct_1 @ X46)
% 3.77/3.96          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 3.77/3.96      inference('cnf', [status(esa)], [t35_funct_2])).
% 3.77/3.96  thf('116', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 3.77/3.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.77/3.96  thf('117', plain,
% 3.77/3.96      (![X45 : $i, X46 : $i, X47 : $i]:
% 3.77/3.96         (((X45) = (k1_xboole_0))
% 3.77/3.96          | ~ (v1_funct_1 @ X46)
% 3.77/3.96          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 3.77/3.96          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 3.77/3.96          | ((k5_relat_1 @ (k2_funct_1 @ X46) @ X46) = (k6_relat_1 @ X45))
% 3.77/3.96          | ~ (v2_funct_1 @ X46)
% 3.77/3.96          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 3.77/3.96      inference('demod', [status(thm)], ['115', '116'])).
% 3.77/3.96  thf('118', plain,
% 3.77/3.96      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 3.77/3.96        | ~ (v2_funct_1 @ sk_C)
% 3.77/3.96        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 3.77/3.96        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.77/3.96        | ~ (v1_funct_1 @ sk_C)
% 3.77/3.96        | ((sk_B) = (k1_xboole_0)))),
% 3.77/3.96      inference('sup-', [status(thm)], ['114', '117'])).
% 3.77/3.96  thf('119', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('120', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('121', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('123', plain,
% 3.77/3.96      ((((sk_B) != (sk_B))
% 3.77/3.96        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 3.77/3.96        | ((sk_B) = (k1_xboole_0)))),
% 3.77/3.96      inference('demod', [status(thm)], ['118', '119', '120', '121', '122'])).
% 3.77/3.96  thf('124', plain,
% 3.77/3.96      ((((sk_B) = (k1_xboole_0))
% 3.77/3.96        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 3.77/3.96      inference('simplify', [status(thm)], ['123'])).
% 3.77/3.96  thf('125', plain, (((sk_B) != (k1_xboole_0))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('126', plain,
% 3.77/3.96      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 3.77/3.96      inference('simplify_reflect-', [status(thm)], ['124', '125'])).
% 3.77/3.96  thf(t59_funct_1, axiom,
% 3.77/3.96    (![A:$i]:
% 3.77/3.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.77/3.96       ( ( v2_funct_1 @ A ) =>
% 3.77/3.96         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 3.77/3.96             ( k2_relat_1 @ A ) ) & 
% 3.77/3.96           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 3.77/3.96             ( k2_relat_1 @ A ) ) ) ) ))).
% 3.77/3.96  thf('127', plain,
% 3.77/3.96      (![X7 : $i]:
% 3.77/3.96         (~ (v2_funct_1 @ X7)
% 3.77/3.96          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X7) @ X7))
% 3.77/3.96              = (k2_relat_1 @ X7))
% 3.77/3.96          | ~ (v1_funct_1 @ X7)
% 3.77/3.96          | ~ (v1_relat_1 @ X7))),
% 3.77/3.96      inference('cnf', [status(esa)], [t59_funct_1])).
% 3.77/3.96  thf('128', plain,
% 3.77/3.96      ((((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (k2_relat_1 @ sk_C))
% 3.77/3.96        | ~ (v1_relat_1 @ sk_C)
% 3.77/3.96        | ~ (v1_funct_1 @ sk_C)
% 3.77/3.96        | ~ (v2_funct_1 @ sk_C))),
% 3.77/3.96      inference('sup+', [status(thm)], ['126', '127'])).
% 3.77/3.96  thf('129', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 3.77/3.96      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.77/3.96  thf('130', plain, ((v1_relat_1 @ sk_C)),
% 3.77/3.96      inference('sup-', [status(thm)], ['105', '106'])).
% 3.77/3.96  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('133', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 3.77/3.96      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 3.77/3.96  thf('134', plain, ((v1_funct_1 @ sk_D)),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('135', plain, ((v1_relat_1 @ sk_D)),
% 3.77/3.96      inference('sup-', [status(thm)], ['73', '74'])).
% 3.77/3.96  thf('136', plain,
% 3.77/3.96      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 3.77/3.96        | ((sk_B) != (k1_relat_1 @ sk_D))
% 3.77/3.96        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 3.77/3.96      inference('demod', [status(thm)],
% 3.77/3.96                ['90', '110', '111', '112', '113', '133', '134', '135'])).
% 3.77/3.96  thf('137', plain,
% 3.77/3.96      ((((sk_D) = (k2_funct_1 @ sk_C)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 3.77/3.96      inference('simplify', [status(thm)], ['136'])).
% 3.77/3.96  thf('138', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 3.77/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.96  thf('139', plain, (((sk_B) != (k1_relat_1 @ sk_D))),
% 3.77/3.96      inference('simplify_reflect-', [status(thm)], ['137', '138'])).
% 3.77/3.96  thf('140', plain, ($false),
% 3.77/3.96      inference('simplify_reflect-', [status(thm)], ['78', '139'])).
% 3.77/3.96  
% 3.77/3.96  % SZS output end Refutation
% 3.77/3.96  
% 3.77/3.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
