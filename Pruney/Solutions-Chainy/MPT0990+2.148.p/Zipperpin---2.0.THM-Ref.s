%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tQnpkLYPVp

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:20 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 503 expanded)
%              Number of leaves         :   48 ( 169 expanded)
%              Depth                    :   17
%              Number of atoms          : 1859 (11490 expanded)
%              Number of equality atoms :  124 ( 784 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('21',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

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

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X12
        = ( k2_funct_1 @ X13 ) )
      | ( ( k5_relat_1 @ X12 @ X13 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X13 ) ) )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('27',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X12
        = ( k2_funct_1 @ X13 ) )
      | ( ( k5_relat_1 @ X12 @ X13 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X13 ) ) )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
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
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('31',plain,(
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

thf('32',plain,(
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

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

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
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('40',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','41','44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('63',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('71',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('72',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['62','69','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','48','53','54','59','73','74','79'])).

thf('81',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

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

thf('83',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('84',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('85',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('86',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('87',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('91',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['62','69','72'])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('94',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['84','87','88','89','90','91','92','93'])).

thf('95',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','95'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('97',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('98',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('99',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('100',plain,(
    ! [X7: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('101',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('102',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('103',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('104',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X12
        = ( k2_funct_1 @ X13 ) )
      | ( ( k5_relat_1 @ X12 @ X13 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X13 ) ) )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['101','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['100','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['99','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['98','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['97','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['96','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('120',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['94'])).

thf('122',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['118','119','120','121'])).

thf('123',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['122','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tQnpkLYPVp
% 0.16/0.37  % Computer   : n025.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 14:22:36 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.69/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.87  % Solved by: fo/fo7.sh
% 0.69/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.87  % done 287 iterations in 0.392s
% 0.69/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.87  % SZS output start Refutation
% 0.69/0.87  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.87  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.69/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.87  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.69/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.87  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.69/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.87  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.69/0.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.69/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.87  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.69/0.87  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.69/0.87  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.69/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.87  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.69/0.87  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.69/0.87  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.69/0.87  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.69/0.87  thf(sk_D_type, type, sk_D: $i).
% 0.69/0.87  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.69/0.87  thf(t36_funct_2, conjecture,
% 0.69/0.87    (![A:$i,B:$i,C:$i]:
% 0.69/0.87     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.69/0.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.87       ( ![D:$i]:
% 0.69/0.87         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.69/0.87             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.69/0.87           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.69/0.87               ( r2_relset_1 @
% 0.69/0.87                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.69/0.87                 ( k6_partfun1 @ A ) ) & 
% 0.69/0.87               ( v2_funct_1 @ C ) ) =>
% 0.69/0.87             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.87               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.69/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.87    (~( ![A:$i,B:$i,C:$i]:
% 0.69/0.87        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.69/0.87            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.87          ( ![D:$i]:
% 0.69/0.87            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.69/0.87                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.69/0.87              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.69/0.87                  ( r2_relset_1 @
% 0.69/0.87                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.69/0.87                    ( k6_partfun1 @ A ) ) & 
% 0.69/0.87                  ( v2_funct_1 @ C ) ) =>
% 0.69/0.87                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.87                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.69/0.87    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.69/0.87  thf('0', plain,
% 0.69/0.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('1', plain,
% 0.69/0.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf(redefinition_k1_partfun1, axiom,
% 0.69/0.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.69/0.87     ( ( ( v1_funct_1 @ E ) & 
% 0.69/0.87         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.87         ( v1_funct_1 @ F ) & 
% 0.69/0.87         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.69/0.87       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.69/0.87  thf('2', plain,
% 0.69/0.87      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.69/0.87          | ~ (v1_funct_1 @ X39)
% 0.69/0.87          | ~ (v1_funct_1 @ X42)
% 0.69/0.87          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.69/0.87          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 0.69/0.87              = (k5_relat_1 @ X39 @ X42)))),
% 0.69/0.87      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.69/0.87  thf('3', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.69/0.87            = (k5_relat_1 @ sk_C @ X0))
% 0.69/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.69/0.87          | ~ (v1_funct_1 @ X0)
% 0.69/0.87          | ~ (v1_funct_1 @ sk_C))),
% 0.69/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.69/0.87  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('5', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.69/0.87            = (k5_relat_1 @ sk_C @ X0))
% 0.69/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.69/0.87          | ~ (v1_funct_1 @ X0))),
% 0.69/0.87      inference('demod', [status(thm)], ['3', '4'])).
% 0.69/0.87  thf('6', plain,
% 0.69/0.87      ((~ (v1_funct_1 @ sk_D)
% 0.69/0.87        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.69/0.87            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['0', '5'])).
% 0.69/0.87  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('8', plain,
% 0.69/0.87      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.69/0.87        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.69/0.87        (k6_partfun1 @ sk_A))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('9', plain,
% 0.69/0.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('10', plain,
% 0.69/0.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf(dt_k1_partfun1, axiom,
% 0.69/0.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.69/0.87     ( ( ( v1_funct_1 @ E ) & 
% 0.69/0.87         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.87         ( v1_funct_1 @ F ) & 
% 0.69/0.87         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.69/0.87       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.69/0.87         ( m1_subset_1 @
% 0.69/0.87           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.69/0.87           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.69/0.87  thf('11', plain,
% 0.69/0.87      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.69/0.87          | ~ (v1_funct_1 @ X33)
% 0.69/0.87          | ~ (v1_funct_1 @ X36)
% 0.69/0.87          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.69/0.87          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 0.69/0.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 0.69/0.87      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.69/0.87  thf('12', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.69/0.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.69/0.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.69/0.87          | ~ (v1_funct_1 @ X1)
% 0.69/0.87          | ~ (v1_funct_1 @ sk_C))),
% 0.69/0.87      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.87  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('14', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.69/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.69/0.88          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.69/0.88          | ~ (v1_funct_1 @ X1))),
% 0.69/0.88      inference('demod', [status(thm)], ['12', '13'])).
% 0.69/0.88  thf('15', plain,
% 0.69/0.88      ((~ (v1_funct_1 @ sk_D)
% 0.69/0.88        | (m1_subset_1 @ 
% 0.69/0.88           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.69/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['9', '14'])).
% 0.69/0.88  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('17', plain,
% 0.69/0.88      ((m1_subset_1 @ 
% 0.69/0.88        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.69/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.69/0.88      inference('demod', [status(thm)], ['15', '16'])).
% 0.69/0.88  thf(redefinition_r2_relset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.88     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.88         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.88       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.69/0.88  thf('18', plain,
% 0.69/0.88      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.69/0.88          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.69/0.88          | ((X20) = (X23))
% 0.69/0.88          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.69/0.88  thf('19', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.69/0.88             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.69/0.88          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.69/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['17', '18'])).
% 0.69/0.88  thf('20', plain,
% 0.69/0.88      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.69/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.69/0.88        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.69/0.88            = (k6_partfun1 @ sk_A)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['8', '19'])).
% 0.69/0.88  thf(t29_relset_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( m1_subset_1 @
% 0.69/0.88       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.69/0.88  thf('21', plain,
% 0.69/0.88      (![X24 : $i]:
% 0.69/0.88         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 0.69/0.88          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.69/0.88      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.69/0.88  thf(redefinition_k6_partfun1, axiom,
% 0.69/0.88    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.69/0.88  thf('22', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.69/0.88  thf('23', plain,
% 0.69/0.88      (![X24 : $i]:
% 0.69/0.88         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 0.69/0.88          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.69/0.88      inference('demod', [status(thm)], ['21', '22'])).
% 0.69/0.88  thf('24', plain,
% 0.69/0.88      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.69/0.88         = (k6_partfun1 @ sk_A))),
% 0.69/0.88      inference('demod', [status(thm)], ['20', '23'])).
% 0.69/0.88  thf('25', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)], ['6', '7', '24'])).
% 0.69/0.88  thf(t64_funct_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.69/0.88           ( ( ( v2_funct_1 @ A ) & 
% 0.69/0.88               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.69/0.88               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.69/0.88             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.69/0.88  thf('26', plain,
% 0.69/0.88      (![X12 : $i, X13 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X12)
% 0.69/0.88          | ~ (v1_funct_1 @ X12)
% 0.69/0.88          | ((X12) = (k2_funct_1 @ X13))
% 0.69/0.88          | ((k5_relat_1 @ X12 @ X13) != (k6_relat_1 @ (k2_relat_1 @ X13)))
% 0.69/0.88          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X13))
% 0.69/0.88          | ~ (v2_funct_1 @ X13)
% 0.69/0.88          | ~ (v1_funct_1 @ X13)
% 0.69/0.88          | ~ (v1_relat_1 @ X13))),
% 0.69/0.88      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.69/0.88  thf('27', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.69/0.88  thf('28', plain,
% 0.69/0.88      (![X12 : $i, X13 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X12)
% 0.69/0.88          | ~ (v1_funct_1 @ X12)
% 0.69/0.88          | ((X12) = (k2_funct_1 @ X13))
% 0.69/0.88          | ((k5_relat_1 @ X12 @ X13) != (k6_partfun1 @ (k2_relat_1 @ X13)))
% 0.69/0.88          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X13))
% 0.69/0.88          | ~ (v2_funct_1 @ X13)
% 0.69/0.88          | ~ (v1_funct_1 @ X13)
% 0.69/0.88          | ~ (v1_relat_1 @ X13))),
% 0.69/0.88      inference('demod', [status(thm)], ['26', '27'])).
% 0.69/0.88  thf('29', plain,
% 0.69/0.88      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.69/0.88        | ~ (v1_relat_1 @ sk_D)
% 0.69/0.88        | ~ (v1_funct_1 @ sk_D)
% 0.69/0.88        | ~ (v2_funct_1 @ sk_D)
% 0.69/0.88        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.69/0.88        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.69/0.88        | ~ (v1_funct_1 @ sk_C)
% 0.69/0.88        | ~ (v1_relat_1 @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['25', '28'])).
% 0.69/0.88  thf('30', plain,
% 0.69/0.88      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.69/0.88         = (k6_partfun1 @ sk_A))),
% 0.69/0.88      inference('demod', [status(thm)], ['20', '23'])).
% 0.69/0.88  thf('31', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(t24_funct_2, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.69/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.88       ( ![D:$i]:
% 0.69/0.88         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.69/0.88             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.69/0.88           ( ( r2_relset_1 @
% 0.69/0.88               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.69/0.88               ( k6_partfun1 @ B ) ) =>
% 0.69/0.88             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.69/0.88  thf('32', plain,
% 0.69/0.88      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.69/0.88         (~ (v1_funct_1 @ X46)
% 0.69/0.88          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 0.69/0.88          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.69/0.88          | ~ (r2_relset_1 @ X47 @ X47 @ 
% 0.69/0.88               (k1_partfun1 @ X47 @ X48 @ X48 @ X47 @ X46 @ X49) @ 
% 0.69/0.88               (k6_partfun1 @ X47))
% 0.69/0.88          | ((k2_relset_1 @ X48 @ X47 @ X49) = (X47))
% 0.69/0.88          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47)))
% 0.69/0.88          | ~ (v1_funct_2 @ X49 @ X48 @ X47)
% 0.69/0.88          | ~ (v1_funct_1 @ X49))),
% 0.69/0.88      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.69/0.88  thf('33', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.69/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.69/0.88          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.69/0.88          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.69/0.88               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.69/0.88               (k6_partfun1 @ sk_A))
% 0.69/0.88          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.69/0.88          | ~ (v1_funct_1 @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['31', '32'])).
% 0.69/0.88  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('36', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.69/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.69/0.88          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.69/0.88          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.69/0.88               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.69/0.88               (k6_partfun1 @ sk_A)))),
% 0.69/0.88      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.69/0.88  thf('37', plain,
% 0.69/0.88      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.69/0.88           (k6_partfun1 @ sk_A))
% 0.69/0.88        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.69/0.88        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.69/0.88        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.69/0.88        | ~ (v1_funct_1 @ sk_D))),
% 0.69/0.88      inference('sup-', [status(thm)], ['30', '36'])).
% 0.69/0.88  thf('38', plain,
% 0.69/0.88      (![X24 : $i]:
% 0.69/0.88         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 0.69/0.88          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.69/0.88      inference('demod', [status(thm)], ['21', '22'])).
% 0.69/0.88  thf('39', plain,
% 0.69/0.88      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.69/0.88          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.69/0.88          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 0.69/0.88          | ((X20) != (X23)))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.69/0.88  thf('40', plain,
% 0.69/0.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.69/0.88         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 0.69/0.88          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.69/0.88      inference('simplify', [status(thm)], ['39'])).
% 0.69/0.88  thf('41', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['38', '40'])).
% 0.69/0.88  thf('42', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(redefinition_k2_relset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.69/0.88  thf('43', plain,
% 0.69/0.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.88         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.69/0.88          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.69/0.88  thf('44', plain,
% 0.69/0.88      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.69/0.88      inference('sup-', [status(thm)], ['42', '43'])).
% 0.69/0.88  thf('45', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.69/0.88      inference('demod', [status(thm)], ['37', '41', '44', '45', '46', '47'])).
% 0.69/0.88  thf('49', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(cc2_relat_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( v1_relat_1 @ A ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.69/0.88  thf('50', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.69/0.88          | (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X1))),
% 0.69/0.88      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.69/0.88  thf('51', plain,
% 0.69/0.88      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.69/0.88      inference('sup-', [status(thm)], ['49', '50'])).
% 0.69/0.88  thf(fc6_relat_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.69/0.88  thf('52', plain,
% 0.69/0.88      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.69/0.88      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.88  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 0.69/0.88      inference('demod', [status(thm)], ['51', '52'])).
% 0.69/0.88  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('55', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('56', plain,
% 0.69/0.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.88         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.69/0.88          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.69/0.88  thf('57', plain,
% 0.69/0.88      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['55', '56'])).
% 0.69/0.88  thf('58', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('59', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.69/0.88      inference('sup+', [status(thm)], ['57', '58'])).
% 0.69/0.88  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(d1_funct_2, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.69/0.88           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.69/0.88             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.69/0.88         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.88           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.69/0.88             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_1, axiom,
% 0.69/0.88    (![C:$i,B:$i,A:$i]:
% 0.69/0.88     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.69/0.88       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.69/0.88  thf('61', plain,
% 0.69/0.88      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.69/0.88         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.69/0.88          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 0.69/0.88          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.69/0.88  thf('62', plain,
% 0.69/0.88      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.69/0.88        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['60', '61'])).
% 0.69/0.88  thf(zf_stmt_2, axiom,
% 0.69/0.88    (![B:$i,A:$i]:
% 0.69/0.88     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.88       ( zip_tseitin_0 @ B @ A ) ))).
% 0.69/0.88  thf('63', plain,
% 0.69/0.88      (![X25 : $i, X26 : $i]:
% 0.69/0.88         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.69/0.88  thf('64', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.69/0.88  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.69/0.88  thf(zf_stmt_5, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.69/0.88         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.69/0.88           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.69/0.88             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.69/0.88  thf('65', plain,
% 0.69/0.88      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.69/0.88         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.69/0.88          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.69/0.88          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.69/0.88  thf('66', plain,
% 0.69/0.88      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.69/0.88      inference('sup-', [status(thm)], ['64', '65'])).
% 0.69/0.88  thf('67', plain,
% 0.69/0.88      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.69/0.88      inference('sup-', [status(thm)], ['63', '66'])).
% 0.69/0.88  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('69', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.69/0.88      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 0.69/0.88  thf('70', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(redefinition_k1_relset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.69/0.88  thf('71', plain,
% 0.69/0.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.69/0.88         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.69/0.88          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.69/0.88  thf('72', plain,
% 0.69/0.88      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.69/0.88      inference('sup-', [status(thm)], ['70', '71'])).
% 0.69/0.88  thf('73', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)], ['62', '69', '72'])).
% 0.69/0.88  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('75', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('76', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.69/0.88          | (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X1))),
% 0.69/0.88      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.69/0.88  thf('77', plain,
% 0.69/0.88      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['75', '76'])).
% 0.69/0.88  thf('78', plain,
% 0.69/0.88      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.69/0.88      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.88  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.88      inference('demod', [status(thm)], ['77', '78'])).
% 0.69/0.88  thf('80', plain,
% 0.69/0.88      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.69/0.88        | ~ (v2_funct_1 @ sk_D)
% 0.69/0.88        | ((sk_B) != (sk_B))
% 0.69/0.88        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.69/0.88      inference('demod', [status(thm)],
% 0.69/0.88                ['29', '48', '53', '54', '59', '73', '74', '79'])).
% 0.69/0.88  thf('81', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 0.69/0.88      inference('simplify', [status(thm)], ['80'])).
% 0.69/0.88  thf('82', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)], ['6', '7', '24'])).
% 0.69/0.88  thf(t48_funct_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.69/0.88           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.69/0.88               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.69/0.88             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.69/0.88  thf('83', plain,
% 0.69/0.88      (![X8 : $i, X9 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X8)
% 0.69/0.88          | ~ (v1_funct_1 @ X8)
% 0.69/0.88          | (v2_funct_1 @ X9)
% 0.69/0.88          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 0.69/0.88          | ~ (v2_funct_1 @ (k5_relat_1 @ X8 @ X9))
% 0.69/0.88          | ~ (v1_funct_1 @ X9)
% 0.69/0.88          | ~ (v1_relat_1 @ X9))),
% 0.69/0.88      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.69/0.88  thf('84', plain,
% 0.69/0.88      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.69/0.88        | ~ (v1_relat_1 @ sk_D)
% 0.69/0.88        | ~ (v1_funct_1 @ sk_D)
% 0.69/0.88        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.69/0.88        | (v2_funct_1 @ sk_D)
% 0.69/0.88        | ~ (v1_funct_1 @ sk_C)
% 0.69/0.88        | ~ (v1_relat_1 @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['82', '83'])).
% 0.69/0.88  thf(fc4_funct_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.69/0.88       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.69/0.88  thf('85', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 0.69/0.88      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.69/0.88  thf('86', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.69/0.88  thf('87', plain, (![X6 : $i]: (v2_funct_1 @ (k6_partfun1 @ X6))),
% 0.69/0.88      inference('demod', [status(thm)], ['85', '86'])).
% 0.69/0.88  thf('88', plain, ((v1_relat_1 @ sk_D)),
% 0.69/0.88      inference('demod', [status(thm)], ['51', '52'])).
% 0.69/0.88  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('90', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.69/0.88      inference('sup+', [status(thm)], ['57', '58'])).
% 0.69/0.88  thf('91', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)], ['62', '69', '72'])).
% 0.69/0.88  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.88      inference('demod', [status(thm)], ['77', '78'])).
% 0.69/0.88  thf('94', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)],
% 0.69/0.88                ['84', '87', '88', '89', '90', '91', '92', '93'])).
% 0.69/0.88  thf('95', plain, ((v2_funct_1 @ sk_D)),
% 0.69/0.88      inference('simplify', [status(thm)], ['94'])).
% 0.69/0.88  thf('96', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)], ['81', '95'])).
% 0.69/0.88  thf(t55_funct_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.69/0.88       ( ( v2_funct_1 @ A ) =>
% 0.69/0.88         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.69/0.88           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.69/0.88  thf('97', plain,
% 0.69/0.88      (![X10 : $i]:
% 0.69/0.88         (~ (v2_funct_1 @ X10)
% 0.69/0.88          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 0.69/0.88          | ~ (v1_funct_1 @ X10)
% 0.69/0.88          | ~ (v1_relat_1 @ X10))),
% 0.69/0.88      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.69/0.88  thf(dt_k2_funct_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.69/0.88       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.69/0.88         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.69/0.88  thf('98', plain,
% 0.69/0.88      (![X4 : $i]:
% 0.69/0.88         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.69/0.88          | ~ (v1_funct_1 @ X4)
% 0.69/0.88          | ~ (v1_relat_1 @ X4))),
% 0.69/0.88      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.69/0.88  thf('99', plain,
% 0.69/0.88      (![X4 : $i]:
% 0.69/0.88         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.69/0.88          | ~ (v1_funct_1 @ X4)
% 0.69/0.88          | ~ (v1_relat_1 @ X4))),
% 0.69/0.88      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.69/0.88  thf(fc6_funct_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.69/0.88       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.69/0.88         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.69/0.88         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.69/0.88  thf('100', plain,
% 0.69/0.88      (![X7 : $i]:
% 0.69/0.88         ((v2_funct_1 @ (k2_funct_1 @ X7))
% 0.69/0.88          | ~ (v2_funct_1 @ X7)
% 0.69/0.88          | ~ (v1_funct_1 @ X7)
% 0.69/0.88          | ~ (v1_relat_1 @ X7))),
% 0.69/0.88      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.69/0.88  thf('101', plain,
% 0.69/0.88      (![X10 : $i]:
% 0.69/0.88         (~ (v2_funct_1 @ X10)
% 0.69/0.88          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 0.69/0.88          | ~ (v1_funct_1 @ X10)
% 0.69/0.88          | ~ (v1_relat_1 @ X10))),
% 0.69/0.88      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.69/0.88  thf(t61_funct_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.69/0.88       ( ( v2_funct_1 @ A ) =>
% 0.69/0.88         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.69/0.88             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.69/0.88           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.69/0.88             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.69/0.88  thf('102', plain,
% 0.69/0.88      (![X11 : $i]:
% 0.69/0.88         (~ (v2_funct_1 @ X11)
% 0.69/0.88          | ((k5_relat_1 @ X11 @ (k2_funct_1 @ X11))
% 0.69/0.88              = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.69/0.88          | ~ (v1_funct_1 @ X11)
% 0.69/0.88          | ~ (v1_relat_1 @ X11))),
% 0.69/0.88      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.69/0.88  thf('103', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.69/0.88  thf('104', plain,
% 0.69/0.88      (![X11 : $i]:
% 0.69/0.88         (~ (v2_funct_1 @ X11)
% 0.69/0.88          | ((k5_relat_1 @ X11 @ (k2_funct_1 @ X11))
% 0.69/0.88              = (k6_partfun1 @ (k1_relat_1 @ X11)))
% 0.69/0.88          | ~ (v1_funct_1 @ X11)
% 0.69/0.88          | ~ (v1_relat_1 @ X11))),
% 0.69/0.88      inference('demod', [status(thm)], ['102', '103'])).
% 0.69/0.88  thf('105', plain,
% 0.69/0.88      (![X12 : $i, X13 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X12)
% 0.69/0.88          | ~ (v1_funct_1 @ X12)
% 0.69/0.88          | ((X12) = (k2_funct_1 @ X13))
% 0.69/0.88          | ((k5_relat_1 @ X12 @ X13) != (k6_partfun1 @ (k2_relat_1 @ X13)))
% 0.69/0.88          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X13))
% 0.69/0.88          | ~ (v2_funct_1 @ X13)
% 0.69/0.88          | ~ (v1_funct_1 @ X13)
% 0.69/0.88          | ~ (v1_relat_1 @ X13))),
% 0.69/0.88      inference('demod', [status(thm)], ['26', '27'])).
% 0.69/0.88  thf('106', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.69/0.88            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['104', '105'])).
% 0.69/0.88  thf('107', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.69/0.88              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.69/0.88      inference('simplify', [status(thm)], ['106'])).
% 0.69/0.88  thf('108', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.69/0.88            != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['101', '107'])).
% 0.69/0.88  thf('109', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['108'])).
% 0.69/0.88  thf('110', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['100', '109'])).
% 0.69/0.88  thf('111', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['110'])).
% 0.69/0.88  thf('112', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['99', '111'])).
% 0.69/0.88  thf('113', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['112'])).
% 0.69/0.88  thf('114', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['98', '113'])).
% 0.69/0.88  thf('115', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['114'])).
% 0.69/0.88  thf('116', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['97', '115'])).
% 0.69/0.88  thf('117', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['116'])).
% 0.69/0.88  thf('118', plain,
% 0.69/0.88      ((((sk_D) = (k2_funct_1 @ sk_C))
% 0.69/0.88        | ~ (v1_relat_1 @ sk_D)
% 0.69/0.88        | ~ (v1_funct_1 @ sk_D)
% 0.69/0.88        | ~ (v2_funct_1 @ sk_D))),
% 0.69/0.88      inference('sup+', [status(thm)], ['96', '117'])).
% 0.69/0.88  thf('119', plain, ((v1_relat_1 @ sk_D)),
% 0.69/0.88      inference('demod', [status(thm)], ['51', '52'])).
% 0.69/0.88  thf('120', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('121', plain, ((v2_funct_1 @ sk_D)),
% 0.69/0.88      inference('simplify', [status(thm)], ['94'])).
% 0.69/0.88  thf('122', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.69/0.88      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 0.69/0.88  thf('123', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('124', plain, ($false),
% 0.69/0.88      inference('simplify_reflect-', [status(thm)], ['122', '123'])).
% 0.69/0.88  
% 0.69/0.88  % SZS output end Refutation
% 0.69/0.88  
% 0.69/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
