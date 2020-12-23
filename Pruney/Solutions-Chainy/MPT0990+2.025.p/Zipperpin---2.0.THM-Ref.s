%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8pteehZCkE

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:58 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  347 (2505 expanded)
%              Number of leaves         :   51 ( 751 expanded)
%              Depth                    :   40
%              Number of atoms          : 3575 (56175 expanded)
%              Number of equality atoms :  211 (3953 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X42 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 ) ) ),
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

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('24',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

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

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X13
        = ( k2_funct_1 @ X14 ) )
      | ( ( k5_relat_1 @ X13 @ X14 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
      | ( ( k2_relat_1 @ X13 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('29',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X13
        = ( k2_funct_1 @ X14 ) )
      | ( ( k5_relat_1 @ X13 @ X14 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X14 ) ) )
      | ( ( k2_relat_1 @ X13 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
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
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( r2_relset_1 @ X51 @ X51 @ ( k1_partfun1 @ X51 @ X52 @ X52 @ X51 @ X50 @ X53 ) @ ( k6_partfun1 @ X51 ) )
      | ( ( k2_relset_1 @ X52 @ X51 @ X53 )
        = X51 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['39','42','43','44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('48',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('49',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('59',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('67',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('68',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['58','65','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','46','49','50','55','69','70','73'])).

thf('75',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

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

thf('77',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('78',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('79',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('82',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('86',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('92',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','89','92'])).

thf('94',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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

thf('95',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('97',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['96'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('98',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ X6 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('99',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('100',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ( ( k5_relat_1 @ X5 @ ( k6_partfun1 @ X6 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['93','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('111',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('113',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('115',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('116',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('117',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X3 ) )
      = X3 ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != sk_A )
    | ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','114','117'])).

thf('119',plain,(
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

thf('120',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( v2_funct_1 @ X54 )
      | ( ( k2_relset_1 @ X56 @ X55 @ X54 )
       != X55 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X55 ) ) )
      | ~ ( v1_funct_2 @ X54 @ X56 @ X55 )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('121',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['121','122','123','124','125'])).

thf('127',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != sk_A )
    | ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['118','127'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('129',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('130',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('131',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('132',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('133',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('134',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('135',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf('136',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X12 @ ( k2_funct_1 @ X12 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('137',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('138',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X12 @ ( k2_funct_1 @ X12 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X13
        = ( k2_funct_1 @ X14 ) )
      | ( ( k5_relat_1 @ X13 @ X14 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X14 ) ) )
      | ( ( k2_relat_1 @ X13 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('140',plain,(
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
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
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
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
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
    inference('sup-',[status(thm)],['135','141'])).

thf('143',plain,(
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
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
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
    inference('sup-',[status(thm)],['134','143'])).

thf('145',plain,(
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
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
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
    inference('sup-',[status(thm)],['133','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
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
    inference('sup-',[status(thm)],['132','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
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
    inference('sup-',[status(thm)],['131','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('153',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('154',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('155',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('156',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['155','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['154','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['153','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['152','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('167',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['165','166','167','168'])).

thf('170',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['151','169'])).

thf('171',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('173',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('175',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('177',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['170','175','176','177','178'])).

thf('180',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('181',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','89','92'])).

thf('183',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['126'])).

thf('184',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['130','184'])).

thf('186',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('187',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['129','188'])).

thf('190',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['189','190','191','192'])).

thf('194',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( sk_A != sk_A )
    | ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['128','193'])).

thf('195',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','195'])).

thf('197',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('198',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','89','92'])).

thf('201',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('202',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('203',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('204',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('205',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('206',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('207',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['207','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['206','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['205','217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['204','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['203','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['202','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['201','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,
    ( ( v2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['200','226'])).

thf('228',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('229',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('230',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['227','228','229','230','231'])).

thf('233',plain,
    ( ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['199','232'])).

thf('234',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( v2_funct_1 @ X54 )
      | ( ( k2_relset_1 @ X56 @ X55 @ X54 )
       != X55 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X54 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X55 ) ) )
      | ~ ( v1_funct_2 @ X54 @ X56 @ X55 )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('236',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['236','237','238','239','240'])).

thf('242',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('245',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['242','247'])).

thf('249',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['126'])).

thf('250',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['248','249'])).

thf('251',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['241'])).

thf('252',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('253',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['126'])).

thf('255',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('256',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('257',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['170','175','176','177','178'])).

thf('258',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('259',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('260',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['257','260'])).

thf('262',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['126'])).

thf('263',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['261','262'])).

thf('264',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['189','190','191','192'])).

thf('265',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['263','264'])).

thf('266',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['256','265'])).

thf('267',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('268',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['266','267','268'])).

thf('270',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['255','269'])).

thf('271',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('272',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['270','271','272','273'])).

thf('275',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['253','254','274'])).

thf('276',plain,(
    v1_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['250','275'])).

thf('277',plain,(
    v2_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['233','276'])).

thf('278',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('279',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('281',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['58','65','68'])).

thf('282',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('284',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['78','277','278','279','280','281','282','283'])).

thf('285',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['284'])).

thf('286',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['75','285'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('288',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['286','287'])).

thf('289',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('290',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['284'])).

thf('292',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['288','289','290','291'])).

thf('293',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['292','293'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8pteehZCkE
% 0.14/0.36  % Computer   : n002.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 17:38:52 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.89/1.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.89/1.13  % Solved by: fo/fo7.sh
% 0.89/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.13  % done 519 iterations in 0.680s
% 0.89/1.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.89/1.13  % SZS output start Refutation
% 0.89/1.13  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.89/1.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.89/1.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.13  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.89/1.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.89/1.13  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.89/1.13  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.89/1.13  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.89/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.13  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.89/1.13  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.89/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.13  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.89/1.13  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.89/1.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.13  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.89/1.13  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.89/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.13  thf(sk_D_type, type, sk_D: $i).
% 0.89/1.13  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.89/1.13  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.13  thf(t36_funct_2, conjecture,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13       ( ![D:$i]:
% 0.89/1.13         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.89/1.13             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.89/1.13           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.89/1.13               ( r2_relset_1 @
% 0.89/1.13                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.89/1.13                 ( k6_partfun1 @ A ) ) & 
% 0.89/1.13               ( v2_funct_1 @ C ) ) =>
% 0.89/1.13             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.13               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.89/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.13    (~( ![A:$i,B:$i,C:$i]:
% 0.89/1.13        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.13            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13          ( ![D:$i]:
% 0.89/1.13            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.89/1.13                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.89/1.13              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.89/1.13                  ( r2_relset_1 @
% 0.89/1.13                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.89/1.13                    ( k6_partfun1 @ A ) ) & 
% 0.89/1.13                  ( v2_funct_1 @ C ) ) =>
% 0.89/1.13                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.13                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.89/1.13    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.89/1.13  thf('0', plain,
% 0.89/1.13      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.89/1.13        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.89/1.13        (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('1', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('2', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(redefinition_k1_partfun1, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ E ) & 
% 0.89/1.13         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.13         ( v1_funct_1 @ F ) & 
% 0.89/1.13         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.89/1.13       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.89/1.13  thf('3', plain,
% 0.89/1.13      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.89/1.13         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.89/1.13          | ~ (v1_funct_1 @ X43)
% 0.89/1.13          | ~ (v1_funct_1 @ X46)
% 0.89/1.13          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.89/1.13          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 0.89/1.13              = (k5_relat_1 @ X43 @ X46)))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.89/1.13  thf('4', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.89/1.13            = (k5_relat_1 @ sk_C @ X0))
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['2', '3'])).
% 0.89/1.13  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('6', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.89/1.13            = (k5_relat_1 @ sk_C @ X0))
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.89/1.13          | ~ (v1_funct_1 @ X0))),
% 0.89/1.13      inference('demod', [status(thm)], ['4', '5'])).
% 0.89/1.13  thf('7', plain,
% 0.89/1.13      ((~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.13            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['1', '6'])).
% 0.89/1.13  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('9', plain,
% 0.89/1.13      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.13         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.89/1.13      inference('demod', [status(thm)], ['7', '8'])).
% 0.89/1.13  thf('10', plain,
% 0.89/1.13      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.89/1.13        (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['0', '9'])).
% 0.89/1.13  thf('11', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('12', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(dt_k1_partfun1, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ E ) & 
% 0.89/1.13         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.13         ( v1_funct_1 @ F ) & 
% 0.89/1.13         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.89/1.13       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.89/1.13         ( m1_subset_1 @
% 0.89/1.13           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.89/1.13           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.89/1.13  thf('13', plain,
% 0.89/1.13      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.89/1.13         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.89/1.13          | ~ (v1_funct_1 @ X37)
% 0.89/1.13          | ~ (v1_funct_1 @ X40)
% 0.89/1.13          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.89/1.13          | (m1_subset_1 @ (k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40) @ 
% 0.89/1.13             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X42))))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.89/1.13  thf('14', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.89/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.89/1.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.89/1.13          | ~ (v1_funct_1 @ X1)
% 0.89/1.13          | ~ (v1_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['12', '13'])).
% 0.89/1.13  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('16', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.89/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.89/1.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.89/1.13          | ~ (v1_funct_1 @ X1))),
% 0.89/1.13      inference('demod', [status(thm)], ['14', '15'])).
% 0.89/1.13  thf('17', plain,
% 0.89/1.13      ((~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | (m1_subset_1 @ 
% 0.89/1.13           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.89/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['11', '16'])).
% 0.89/1.13  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('19', plain,
% 0.89/1.13      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.13         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.89/1.13      inference('demod', [status(thm)], ['7', '8'])).
% 0.89/1.13  thf('20', plain,
% 0.89/1.13      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.89/1.13        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.89/1.13      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.89/1.13  thf(redefinition_r2_relset_1, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.13     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.13         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.89/1.13  thf('21', plain,
% 0.89/1.13      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.89/1.13         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.89/1.13          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.89/1.13          | ((X24) = (X27))
% 0.89/1.13          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.89/1.13  thf('22', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.89/1.13          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['20', '21'])).
% 0.89/1.13  thf('23', plain,
% 0.89/1.13      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.89/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.89/1.13        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['10', '22'])).
% 0.89/1.13  thf(t29_relset_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( m1_subset_1 @
% 0.89/1.13       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.89/1.13  thf('24', plain,
% 0.89/1.13      (![X28 : $i]:
% 0.89/1.13         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 0.89/1.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.89/1.13      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.89/1.13  thf(redefinition_k6_partfun1, axiom,
% 0.89/1.13    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.89/1.13  thf('25', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('26', plain,
% 0.89/1.13      (![X28 : $i]:
% 0.89/1.13         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 0.89/1.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.89/1.13      inference('demod', [status(thm)], ['24', '25'])).
% 0.89/1.13  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['23', '26'])).
% 0.89/1.13  thf(t64_funct_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.13       ( ![B:$i]:
% 0.89/1.13         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.89/1.13           ( ( ( v2_funct_1 @ A ) & 
% 0.89/1.13               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.89/1.13               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.89/1.13             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.89/1.13  thf('28', plain,
% 0.89/1.13      (![X13 : $i, X14 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X13)
% 0.89/1.13          | ~ (v1_funct_1 @ X13)
% 0.89/1.13          | ((X13) = (k2_funct_1 @ X14))
% 0.89/1.13          | ((k5_relat_1 @ X13 @ X14) != (k6_relat_1 @ (k2_relat_1 @ X14)))
% 0.89/1.13          | ((k2_relat_1 @ X13) != (k1_relat_1 @ X14))
% 0.89/1.13          | ~ (v2_funct_1 @ X14)
% 0.89/1.13          | ~ (v1_funct_1 @ X14)
% 0.89/1.13          | ~ (v1_relat_1 @ X14))),
% 0.89/1.13      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.89/1.13  thf('29', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('30', plain,
% 0.89/1.13      (![X13 : $i, X14 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X13)
% 0.89/1.13          | ~ (v1_funct_1 @ X13)
% 0.89/1.13          | ((X13) = (k2_funct_1 @ X14))
% 0.89/1.13          | ((k5_relat_1 @ X13 @ X14) != (k6_partfun1 @ (k2_relat_1 @ X14)))
% 0.89/1.13          | ((k2_relat_1 @ X13) != (k1_relat_1 @ X14))
% 0.89/1.13          | ~ (v2_funct_1 @ X14)
% 0.89/1.13          | ~ (v1_funct_1 @ X14)
% 0.89/1.13          | ~ (v1_relat_1 @ X14))),
% 0.89/1.13      inference('demod', [status(thm)], ['28', '29'])).
% 0.89/1.13  thf('31', plain,
% 0.89/1.13      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.89/1.13        | ~ (v1_relat_1 @ sk_D)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.89/1.13        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['27', '30'])).
% 0.89/1.13  thf('32', plain,
% 0.89/1.13      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.89/1.13        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.89/1.13        (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('33', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(t24_funct_2, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13       ( ![D:$i]:
% 0.89/1.13         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.89/1.13             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.89/1.13           ( ( r2_relset_1 @
% 0.89/1.13               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.89/1.13               ( k6_partfun1 @ B ) ) =>
% 0.89/1.13             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.89/1.13  thf('34', plain,
% 0.89/1.13      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.89/1.13         (~ (v1_funct_1 @ X50)
% 0.89/1.13          | ~ (v1_funct_2 @ X50 @ X51 @ X52)
% 0.89/1.13          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 0.89/1.13          | ~ (r2_relset_1 @ X51 @ X51 @ 
% 0.89/1.13               (k1_partfun1 @ X51 @ X52 @ X52 @ X51 @ X50 @ X53) @ 
% 0.89/1.13               (k6_partfun1 @ X51))
% 0.89/1.13          | ((k2_relset_1 @ X52 @ X51 @ X53) = (X51))
% 0.89/1.13          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 0.89/1.13          | ~ (v1_funct_2 @ X53 @ X52 @ X51)
% 0.89/1.13          | ~ (v1_funct_1 @ X53))),
% 0.89/1.13      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.89/1.13  thf('35', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.89/1.13          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.89/1.13          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.89/1.13               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.89/1.13               (k6_partfun1 @ sk_A))
% 0.89/1.13          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.89/1.13          | ~ (v1_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['33', '34'])).
% 0.89/1.13  thf('36', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('38', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.89/1.13          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.89/1.13          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.89/1.13               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.89/1.13               (k6_partfun1 @ sk_A)))),
% 0.89/1.13      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.89/1.13  thf('39', plain,
% 0.89/1.13      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.89/1.13        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.89/1.13        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_D))),
% 0.89/1.13      inference('sup-', [status(thm)], ['32', '38'])).
% 0.89/1.13  thf('40', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(redefinition_k2_relset_1, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.13       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.89/1.13  thf('41', plain,
% 0.89/1.13      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.89/1.13         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.89/1.13          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.89/1.13  thf('42', plain,
% 0.89/1.13      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.89/1.13      inference('sup-', [status(thm)], ['40', '41'])).
% 0.89/1.13  thf('43', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('44', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('46', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['39', '42', '43', '44', '45'])).
% 0.89/1.13  thf('47', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(cc1_relset_1, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.13       ( v1_relat_1 @ C ) ))).
% 0.89/1.13  thf('48', plain,
% 0.89/1.13      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.89/1.13         ((v1_relat_1 @ X15)
% 0.89/1.13          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.89/1.13      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.89/1.13  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 0.89/1.13      inference('sup-', [status(thm)], ['47', '48'])).
% 0.89/1.13  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('51', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('52', plain,
% 0.89/1.13      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.89/1.13         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.89/1.13          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.89/1.13  thf('53', plain,
% 0.89/1.13      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['51', '52'])).
% 0.89/1.13  thf('54', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('55', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.89/1.13      inference('sup+', [status(thm)], ['53', '54'])).
% 0.89/1.13  thf('56', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(d1_funct_2, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.13       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.89/1.13           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.89/1.13             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.89/1.13         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.89/1.13           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.89/1.13             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.89/1.13  thf(zf_stmt_1, axiom,
% 0.89/1.13    (![C:$i,B:$i,A:$i]:
% 0.89/1.13     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.89/1.13       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.89/1.13  thf('57', plain,
% 0.89/1.13      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.89/1.13         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.89/1.13          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.89/1.13          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.13  thf('58', plain,
% 0.89/1.13      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.89/1.13        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['56', '57'])).
% 0.89/1.13  thf(zf_stmt_2, axiom,
% 0.89/1.13    (![B:$i,A:$i]:
% 0.89/1.13     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.89/1.13       ( zip_tseitin_0 @ B @ A ) ))).
% 0.89/1.13  thf('59', plain,
% 0.89/1.13      (![X29 : $i, X30 : $i]:
% 0.89/1.13         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.89/1.13  thf('60', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.89/1.13  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.89/1.13  thf(zf_stmt_5, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.13       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.89/1.13         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.89/1.13           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.89/1.13             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.89/1.13  thf('61', plain,
% 0.89/1.13      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.89/1.13         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.89/1.13          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.89/1.13          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.89/1.13  thf('62', plain,
% 0.89/1.13      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.89/1.13      inference('sup-', [status(thm)], ['60', '61'])).
% 0.89/1.13  thf('63', plain,
% 0.89/1.13      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.89/1.13      inference('sup-', [status(thm)], ['59', '62'])).
% 0.89/1.13  thf('64', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('65', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.89/1.13      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.89/1.13  thf('66', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(redefinition_k1_relset_1, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.13       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.89/1.13  thf('67', plain,
% 0.89/1.13      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.89/1.13         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.89/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.89/1.13  thf('68', plain,
% 0.89/1.13      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.89/1.13      inference('sup-', [status(thm)], ['66', '67'])).
% 0.89/1.13  thf('69', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.89/1.13      inference('demod', [status(thm)], ['58', '65', '68'])).
% 0.89/1.13  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('71', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('72', plain,
% 0.89/1.13      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.89/1.13         ((v1_relat_1 @ X15)
% 0.89/1.13          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.89/1.13      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.89/1.13  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('sup-', [status(thm)], ['71', '72'])).
% 0.89/1.13  thf('74', plain,
% 0.89/1.13      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ((sk_B) != (sk_B))
% 0.89/1.13        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.89/1.13      inference('demod', [status(thm)],
% 0.89/1.13                ['31', '46', '49', '50', '55', '69', '70', '73'])).
% 0.89/1.13  thf('75', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['74'])).
% 0.89/1.13  thf('76', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['23', '26'])).
% 0.89/1.13  thf(t48_funct_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.13       ( ![B:$i]:
% 0.89/1.13         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.89/1.13           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.89/1.13               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.89/1.13             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.89/1.13  thf('77', plain,
% 0.89/1.13      (![X9 : $i, X10 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X9)
% 0.89/1.13          | ~ (v1_funct_1 @ X9)
% 0.89/1.13          | (v2_funct_1 @ X10)
% 0.89/1.13          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 0.89/1.13          | ~ (v2_funct_1 @ (k5_relat_1 @ X9 @ X10))
% 0.89/1.13          | ~ (v1_funct_1 @ X10)
% 0.89/1.13          | ~ (v1_relat_1 @ X10))),
% 0.89/1.13      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.89/1.13  thf('78', plain,
% 0.89/1.13      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | ~ (v1_relat_1 @ sk_D)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.89/1.13        | (v2_funct_1 @ sk_D)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['76', '77'])).
% 0.89/1.13  thf(dt_k2_funct_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.13       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.89/1.13         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.89/1.13  thf('79', plain,
% 0.89/1.13      (![X7 : $i]:
% 0.89/1.13         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.89/1.13          | ~ (v1_funct_1 @ X7)
% 0.89/1.13          | ~ (v1_relat_1 @ X7))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.13  thf('80', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('81', plain,
% 0.89/1.13      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.89/1.13         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.89/1.13          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.89/1.13          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.13  thf('82', plain,
% 0.89/1.13      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.89/1.13        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['80', '81'])).
% 0.89/1.13  thf('83', plain,
% 0.89/1.13      (![X29 : $i, X30 : $i]:
% 0.89/1.13         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.89/1.13  thf('84', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('85', plain,
% 0.89/1.13      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.89/1.13         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.89/1.13          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.89/1.13          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.89/1.13  thf('86', plain,
% 0.89/1.13      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.89/1.13      inference('sup-', [status(thm)], ['84', '85'])).
% 0.89/1.13  thf('87', plain,
% 0.89/1.13      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.89/1.13      inference('sup-', [status(thm)], ['83', '86'])).
% 0.89/1.13  thf('88', plain, (((sk_B) != (k1_xboole_0))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('89', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.89/1.13      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 0.89/1.13  thf('90', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('91', plain,
% 0.89/1.13      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.89/1.13         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.89/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.89/1.13  thf('92', plain,
% 0.89/1.13      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['90', '91'])).
% 0.89/1.13  thf('93', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['82', '89', '92'])).
% 0.89/1.13  thf('94', plain,
% 0.89/1.13      (![X7 : $i]:
% 0.89/1.13         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.89/1.13          | ~ (v1_funct_1 @ X7)
% 0.89/1.13          | ~ (v1_relat_1 @ X7))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.13  thf(t55_funct_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.13       ( ( v2_funct_1 @ A ) =>
% 0.89/1.13         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.89/1.13           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.89/1.13  thf('95', plain,
% 0.89/1.13      (![X11 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X11)
% 0.89/1.13          | ((k1_relat_1 @ X11) = (k2_relat_1 @ (k2_funct_1 @ X11)))
% 0.89/1.13          | ~ (v1_funct_1 @ X11)
% 0.89/1.13          | ~ (v1_relat_1 @ X11))),
% 0.89/1.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.89/1.13  thf(d10_xboole_0, axiom,
% 0.89/1.13    (![A:$i,B:$i]:
% 0.89/1.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.13  thf('96', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.89/1.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.13  thf('97', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.89/1.13      inference('simplify', [status(thm)], ['96'])).
% 0.89/1.13  thf(t79_relat_1, axiom,
% 0.89/1.13    (![A:$i,B:$i]:
% 0.89/1.13     ( ( v1_relat_1 @ B ) =>
% 0.89/1.13       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.89/1.13         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.89/1.13  thf('98', plain,
% 0.89/1.13      (![X5 : $i, X6 : $i]:
% 0.89/1.13         (~ (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.89/1.13          | ((k5_relat_1 @ X5 @ (k6_relat_1 @ X6)) = (X5))
% 0.89/1.13          | ~ (v1_relat_1 @ X5))),
% 0.89/1.13      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.89/1.13  thf('99', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('100', plain,
% 0.89/1.13      (![X5 : $i, X6 : $i]:
% 0.89/1.13         (~ (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.89/1.13          | ((k5_relat_1 @ X5 @ (k6_partfun1 @ X6)) = (X5))
% 0.89/1.13          | ~ (v1_relat_1 @ X5))),
% 0.89/1.13      inference('demod', [status(thm)], ['98', '99'])).
% 0.89/1.13  thf('101', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['97', '100'])).
% 0.89/1.13  thf('102', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.89/1.13            = (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.89/1.13      inference('sup+', [status(thm)], ['95', '101'])).
% 0.89/1.13  thf('103', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.89/1.13              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['94', '102'])).
% 0.89/1.13  thf('104', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.89/1.13            = (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['103'])).
% 0.89/1.13  thf('105', plain,
% 0.89/1.13      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.89/1.13          = (k2_funct_1 @ sk_C))
% 0.89/1.13        | ~ (v1_relat_1 @ sk_C)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v2_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup+', [status(thm)], ['93', '104'])).
% 0.89/1.13  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('sup-', [status(thm)], ['71', '72'])).
% 0.89/1.13  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('109', plain,
% 0.89/1.13      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.89/1.13         = (k2_funct_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.89/1.13  thf('110', plain,
% 0.89/1.13      (![X9 : $i, X10 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X9)
% 0.89/1.13          | ~ (v1_funct_1 @ X9)
% 0.89/1.13          | (v2_funct_1 @ X10)
% 0.89/1.13          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 0.89/1.13          | ~ (v2_funct_1 @ (k5_relat_1 @ X9 @ X10))
% 0.89/1.13          | ~ (v1_funct_1 @ X10)
% 0.89/1.13          | ~ (v1_relat_1 @ X10))),
% 0.89/1.13      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.89/1.13  thf('111', plain,
% 0.89/1.13      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | ~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | ((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13            != (k1_relat_1 @ (k6_partfun1 @ sk_A)))
% 0.89/1.13        | (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['109', '110'])).
% 0.89/1.13  thf('112', plain,
% 0.89/1.13      (![X28 : $i]:
% 0.89/1.13         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 0.89/1.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.89/1.13      inference('demod', [status(thm)], ['24', '25'])).
% 0.89/1.13  thf('113', plain,
% 0.89/1.13      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.89/1.13         ((v1_relat_1 @ X15)
% 0.89/1.13          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.89/1.13      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.89/1.13  thf('114', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.89/1.13      inference('sup-', [status(thm)], ['112', '113'])).
% 0.89/1.13  thf(t71_relat_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.89/1.13       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.89/1.13  thf('115', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.89/1.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.13  thf('116', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('117', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X3)) = (X3))),
% 0.89/1.13      inference('demod', [status(thm)], ['115', '116'])).
% 0.89/1.13  thf('118', plain,
% 0.89/1.13      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13        | ~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (sk_A))
% 0.89/1.13        | (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.13      inference('demod', [status(thm)], ['111', '114', '117'])).
% 0.89/1.13  thf('119', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(t31_funct_2, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.89/1.13         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.89/1.13           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.89/1.13           ( m1_subset_1 @
% 0.89/1.13             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.89/1.13  thf('120', plain,
% 0.89/1.13      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X54)
% 0.89/1.13          | ((k2_relset_1 @ X56 @ X55 @ X54) != (X55))
% 0.89/1.13          | (v1_funct_1 @ (k2_funct_1 @ X54))
% 0.89/1.13          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X55)))
% 0.89/1.13          | ~ (v1_funct_2 @ X54 @ X56 @ X55)
% 0.89/1.13          | ~ (v1_funct_1 @ X54))),
% 0.89/1.13      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.89/1.13  thf('121', plain,
% 0.89/1.13      ((~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.89/1.13        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['119', '120'])).
% 0.89/1.13  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('123', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('124', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('126', plain,
% 0.89/1.13      (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 0.89/1.13      inference('demod', [status(thm)], ['121', '122', '123', '124', '125'])).
% 0.89/1.13  thf('127', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.89/1.13      inference('simplify', [status(thm)], ['126'])).
% 0.89/1.13  thf('128', plain,
% 0.89/1.13      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13        | ~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (sk_A))
% 0.89/1.13        | (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.13      inference('demod', [status(thm)], ['118', '127'])).
% 0.89/1.13  thf(fc6_funct_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.89/1.13       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.89/1.13         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.89/1.13         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.89/1.13  thf('129', plain,
% 0.89/1.13      (![X8 : $i]:
% 0.89/1.13         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 0.89/1.13          | ~ (v2_funct_1 @ X8)
% 0.89/1.13          | ~ (v1_funct_1 @ X8)
% 0.89/1.13          | ~ (v1_relat_1 @ X8))),
% 0.89/1.13      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.89/1.13  thf('130', plain,
% 0.89/1.13      (![X7 : $i]:
% 0.89/1.13         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.89/1.13          | ~ (v1_funct_1 @ X7)
% 0.89/1.13          | ~ (v1_relat_1 @ X7))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.13  thf('131', plain,
% 0.89/1.13      (![X11 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X11)
% 0.89/1.13          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 0.89/1.13          | ~ (v1_funct_1 @ X11)
% 0.89/1.13          | ~ (v1_relat_1 @ X11))),
% 0.89/1.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.89/1.13  thf('132', plain,
% 0.89/1.13      (![X7 : $i]:
% 0.89/1.13         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.89/1.13          | ~ (v1_funct_1 @ X7)
% 0.89/1.13          | ~ (v1_relat_1 @ X7))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.13  thf('133', plain,
% 0.89/1.13      (![X7 : $i]:
% 0.89/1.13         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.89/1.13          | ~ (v1_funct_1 @ X7)
% 0.89/1.13          | ~ (v1_relat_1 @ X7))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.13  thf('134', plain,
% 0.89/1.13      (![X8 : $i]:
% 0.89/1.13         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 0.89/1.13          | ~ (v2_funct_1 @ X8)
% 0.89/1.13          | ~ (v1_funct_1 @ X8)
% 0.89/1.13          | ~ (v1_relat_1 @ X8))),
% 0.89/1.13      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.89/1.13  thf('135', plain,
% 0.89/1.13      (![X11 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X11)
% 0.89/1.13          | ((k1_relat_1 @ X11) = (k2_relat_1 @ (k2_funct_1 @ X11)))
% 0.89/1.13          | ~ (v1_funct_1 @ X11)
% 0.89/1.13          | ~ (v1_relat_1 @ X11))),
% 0.89/1.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.89/1.13  thf(t61_funct_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.13       ( ( v2_funct_1 @ A ) =>
% 0.89/1.13         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.89/1.13             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.89/1.13           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.89/1.13             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.89/1.13  thf('136', plain,
% 0.89/1.13      (![X12 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X12)
% 0.89/1.13          | ((k5_relat_1 @ X12 @ (k2_funct_1 @ X12))
% 0.89/1.13              = (k6_relat_1 @ (k1_relat_1 @ X12)))
% 0.89/1.13          | ~ (v1_funct_1 @ X12)
% 0.89/1.13          | ~ (v1_relat_1 @ X12))),
% 0.89/1.13      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.89/1.13  thf('137', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('138', plain,
% 0.89/1.13      (![X12 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X12)
% 0.89/1.13          | ((k5_relat_1 @ X12 @ (k2_funct_1 @ X12))
% 0.89/1.13              = (k6_partfun1 @ (k1_relat_1 @ X12)))
% 0.89/1.13          | ~ (v1_funct_1 @ X12)
% 0.89/1.13          | ~ (v1_relat_1 @ X12))),
% 0.89/1.13      inference('demod', [status(thm)], ['136', '137'])).
% 0.89/1.13  thf('139', plain,
% 0.89/1.13      (![X13 : $i, X14 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X13)
% 0.89/1.13          | ~ (v1_funct_1 @ X13)
% 0.89/1.13          | ((X13) = (k2_funct_1 @ X14))
% 0.89/1.13          | ((k5_relat_1 @ X13 @ X14) != (k6_partfun1 @ (k2_relat_1 @ X14)))
% 0.89/1.13          | ((k2_relat_1 @ X13) != (k1_relat_1 @ X14))
% 0.89/1.13          | ~ (v2_funct_1 @ X14)
% 0.89/1.13          | ~ (v1_funct_1 @ X14)
% 0.89/1.13          | ~ (v1_relat_1 @ X14))),
% 0.89/1.13      inference('demod', [status(thm)], ['28', '29'])).
% 0.89/1.13  thf('140', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.89/1.13            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('sup-', [status(thm)], ['138', '139'])).
% 0.89/1.13  thf('141', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.89/1.13              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.89/1.13      inference('simplify', [status(thm)], ['140'])).
% 0.89/1.13  thf('142', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.89/1.13            != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['135', '141'])).
% 0.89/1.13  thf('143', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['142'])).
% 0.89/1.13  thf('144', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['134', '143'])).
% 0.89/1.13  thf('145', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['144'])).
% 0.89/1.13  thf('146', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['133', '145'])).
% 0.89/1.13  thf('147', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['146'])).
% 0.89/1.13  thf('148', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['132', '147'])).
% 0.89/1.13  thf('149', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['148'])).
% 0.89/1.13  thf('150', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['131', '149'])).
% 0.89/1.13  thf('151', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['150'])).
% 0.89/1.13  thf('152', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.89/1.13      inference('sup+', [status(thm)], ['53', '54'])).
% 0.89/1.13  thf('153', plain,
% 0.89/1.13      (![X8 : $i]:
% 0.89/1.13         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 0.89/1.13          | ~ (v2_funct_1 @ X8)
% 0.89/1.13          | ~ (v1_funct_1 @ X8)
% 0.89/1.13          | ~ (v1_relat_1 @ X8))),
% 0.89/1.13      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.89/1.13  thf('154', plain,
% 0.89/1.13      (![X7 : $i]:
% 0.89/1.13         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.89/1.13          | ~ (v1_funct_1 @ X7)
% 0.89/1.13          | ~ (v1_relat_1 @ X7))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.13  thf('155', plain,
% 0.89/1.13      (![X7 : $i]:
% 0.89/1.13         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.89/1.13          | ~ (v1_funct_1 @ X7)
% 0.89/1.13          | ~ (v1_relat_1 @ X7))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.13  thf('156', plain,
% 0.89/1.13      (![X11 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X11)
% 0.89/1.13          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 0.89/1.13          | ~ (v1_funct_1 @ X11)
% 0.89/1.13          | ~ (v1_relat_1 @ X11))),
% 0.89/1.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.89/1.13  thf('157', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.89/1.13            = (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['103'])).
% 0.89/1.13  thf('158', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.89/1.13            (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.89/1.13            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.89/1.13      inference('sup+', [status(thm)], ['156', '157'])).
% 0.89/1.13  thf('159', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.89/1.13              (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.89/1.13              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['155', '158'])).
% 0.89/1.13  thf('160', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.89/1.13            (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.89/1.13            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['159'])).
% 0.89/1.13  thf('161', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.89/1.13              (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.89/1.13              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['154', '160'])).
% 0.89/1.13  thf('162', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.89/1.13            (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.89/1.13            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['161'])).
% 0.89/1.13  thf('163', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.89/1.13              (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.89/1.13              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['153', '162'])).
% 0.89/1.13  thf('164', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.89/1.13            (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.89/1.13            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['163'])).
% 0.89/1.13  thf('165', plain,
% 0.89/1.13      ((((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.89/1.13          (k6_partfun1 @ sk_B)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.89/1.13        | ~ (v1_relat_1 @ sk_C)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v2_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup+', [status(thm)], ['152', '164'])).
% 0.89/1.13  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('sup-', [status(thm)], ['71', '72'])).
% 0.89/1.13  thf('167', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('168', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('169', plain,
% 0.89/1.13      (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k6_partfun1 @ sk_B))
% 0.89/1.13         = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.13      inference('demod', [status(thm)], ['165', '166', '167', '168'])).
% 0.89/1.13  thf('170', plain,
% 0.89/1.13      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B))
% 0.89/1.13          = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.89/1.13        | ~ (v1_relat_1 @ sk_C)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v2_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup+', [status(thm)], ['151', '169'])).
% 0.89/1.13  thf('171', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.89/1.13      inference('sup+', [status(thm)], ['53', '54'])).
% 0.89/1.13  thf('172', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['97', '100'])).
% 0.89/1.13  thf('173', plain,
% 0.89/1.13      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 0.89/1.13        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.13      inference('sup+', [status(thm)], ['171', '172'])).
% 0.89/1.13  thf('174', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('sup-', [status(thm)], ['71', '72'])).
% 0.89/1.13  thf('175', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['173', '174'])).
% 0.89/1.13  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('sup-', [status(thm)], ['71', '72'])).
% 0.89/1.13  thf('177', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('178', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('179', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.13      inference('demod', [status(thm)], ['170', '175', '176', '177', '178'])).
% 0.89/1.13  thf('180', plain,
% 0.89/1.13      (![X11 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X11)
% 0.89/1.13          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 0.89/1.13          | ~ (v1_funct_1 @ X11)
% 0.89/1.13          | ~ (v1_relat_1 @ X11))),
% 0.89/1.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.89/1.13  thf('181', plain,
% 0.89/1.13      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.89/1.13        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.13      inference('sup+', [status(thm)], ['179', '180'])).
% 0.89/1.13  thf('182', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['82', '89', '92'])).
% 0.89/1.13  thf('183', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.89/1.13      inference('simplify', [status(thm)], ['126'])).
% 0.89/1.13  thf('184', plain,
% 0.89/1.13      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))
% 0.89/1.13        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.13      inference('demod', [status(thm)], ['181', '182', '183'])).
% 0.89/1.13  thf('185', plain,
% 0.89/1.13      ((~ (v1_relat_1 @ sk_C)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['130', '184'])).
% 0.89/1.13  thf('186', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('sup-', [status(thm)], ['71', '72'])).
% 0.89/1.13  thf('187', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('188', plain,
% 0.89/1.13      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 0.89/1.13      inference('demod', [status(thm)], ['185', '186', '187'])).
% 0.89/1.13  thf('189', plain,
% 0.89/1.13      ((~ (v1_relat_1 @ sk_C)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v2_funct_1 @ sk_C)
% 0.89/1.13        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['129', '188'])).
% 0.89/1.13  thf('190', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('sup-', [status(thm)], ['71', '72'])).
% 0.89/1.13  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('192', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('193', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['189', '190', '191', '192'])).
% 0.89/1.13  thf('194', plain,
% 0.89/1.13      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13        | ~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | ((sk_A) != (sk_A))
% 0.89/1.13        | (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.13      inference('demod', [status(thm)], ['128', '193'])).
% 0.89/1.13  thf('195', plain,
% 0.89/1.13      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13        | (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | ~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.13      inference('simplify', [status(thm)], ['194'])).
% 0.89/1.13  thf('196', plain,
% 0.89/1.13      ((~ (v1_relat_1 @ sk_C)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13        | ~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | (v2_funct_1 @ (k6_partfun1 @ sk_A)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['79', '195'])).
% 0.89/1.13  thf('197', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('sup-', [status(thm)], ['71', '72'])).
% 0.89/1.13  thf('198', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('199', plain,
% 0.89/1.13      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.13        | ~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | (v2_funct_1 @ (k6_partfun1 @ sk_A)))),
% 0.89/1.13      inference('demod', [status(thm)], ['196', '197', '198'])).
% 0.89/1.13  thf('200', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['82', '89', '92'])).
% 0.89/1.13  thf('201', plain,
% 0.89/1.13      (![X8 : $i]:
% 0.89/1.13         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 0.89/1.13          | ~ (v2_funct_1 @ X8)
% 0.89/1.13          | ~ (v1_funct_1 @ X8)
% 0.89/1.13          | ~ (v1_relat_1 @ X8))),
% 0.89/1.13      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.89/1.13  thf('202', plain,
% 0.89/1.13      (![X7 : $i]:
% 0.89/1.13         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.89/1.13          | ~ (v1_funct_1 @ X7)
% 0.89/1.13          | ~ (v1_relat_1 @ X7))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.13  thf('203', plain,
% 0.89/1.13      (![X7 : $i]:
% 0.89/1.13         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.89/1.13          | ~ (v1_funct_1 @ X7)
% 0.89/1.13          | ~ (v1_relat_1 @ X7))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.13  thf('204', plain,
% 0.89/1.13      (![X11 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X11)
% 0.89/1.13          | ((k1_relat_1 @ X11) = (k2_relat_1 @ (k2_funct_1 @ X11)))
% 0.89/1.13          | ~ (v1_funct_1 @ X11)
% 0.89/1.13          | ~ (v1_relat_1 @ X11))),
% 0.89/1.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.89/1.13  thf('205', plain,
% 0.89/1.13      (![X8 : $i]:
% 0.89/1.13         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 0.89/1.13          | ~ (v2_funct_1 @ X8)
% 0.89/1.13          | ~ (v1_funct_1 @ X8)
% 0.89/1.13          | ~ (v1_relat_1 @ X8))),
% 0.89/1.13      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.89/1.13  thf('206', plain,
% 0.89/1.13      (![X7 : $i]:
% 0.89/1.13         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.89/1.13          | ~ (v1_funct_1 @ X7)
% 0.89/1.13          | ~ (v1_relat_1 @ X7))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.13  thf('207', plain,
% 0.89/1.13      (![X7 : $i]:
% 0.89/1.13         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.89/1.13          | ~ (v1_funct_1 @ X7)
% 0.89/1.13          | ~ (v1_relat_1 @ X7))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.13  thf('208', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['150'])).
% 0.89/1.13  thf('209', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.89/1.13            (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.89/1.13            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['163'])).
% 0.89/1.13  thf('210', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.89/1.13            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0))),
% 0.89/1.13      inference('sup+', [status(thm)], ['208', '209'])).
% 0.89/1.13  thf('211', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.89/1.13              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.89/1.13      inference('simplify', [status(thm)], ['210'])).
% 0.89/1.13  thf('212', plain,
% 0.89/1.13      (![X8 : $i]:
% 0.89/1.13         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 0.89/1.13          | ~ (v2_funct_1 @ X8)
% 0.89/1.13          | ~ (v1_funct_1 @ X8)
% 0.89/1.13          | ~ (v1_relat_1 @ X8))),
% 0.89/1.13      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.89/1.13  thf('213', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         ((v2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.89/1.13      inference('sup+', [status(thm)], ['211', '212'])).
% 0.89/1.13  thf('214', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | (v2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['207', '213'])).
% 0.89/1.13  thf('215', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         ((v2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['214'])).
% 0.89/1.13  thf('216', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | (v2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['206', '215'])).
% 0.89/1.13  thf('217', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         ((v2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['216'])).
% 0.89/1.13  thf('218', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | (v2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['205', '217'])).
% 0.89/1.13  thf('219', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         ((v2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['218'])).
% 0.89/1.13  thf('220', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         ((v2_funct_1 @ 
% 0.89/1.13           (k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0))))
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.89/1.13      inference('sup+', [status(thm)], ['204', '219'])).
% 0.89/1.13  thf('221', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | (v2_funct_1 @ 
% 0.89/1.13             (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.89/1.13              (k6_partfun1 @ (k1_relat_1 @ X0)))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['203', '220'])).
% 0.89/1.13  thf('222', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         ((v2_funct_1 @ 
% 0.89/1.13           (k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0))))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['221'])).
% 0.89/1.13  thf('223', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | (v2_funct_1 @ 
% 0.89/1.13             (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.89/1.13              (k6_partfun1 @ (k1_relat_1 @ X0)))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['202', '222'])).
% 0.89/1.13  thf('224', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         ((v2_funct_1 @ 
% 0.89/1.13           (k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0))))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['223'])).
% 0.89/1.13  thf('225', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | (v2_funct_1 @ 
% 0.89/1.13             (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.89/1.13              (k6_partfun1 @ (k1_relat_1 @ X0)))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['201', '224'])).
% 0.89/1.13  thf('226', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         ((v2_funct_1 @ 
% 0.89/1.13           (k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0))))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['225'])).
% 0.89/1.13  thf('227', plain,
% 0.89/1.13      (((v2_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 0.89/1.13        | ~ (v1_relat_1 @ sk_C)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v2_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup+', [status(thm)], ['200', '226'])).
% 0.89/1.13  thf('228', plain,
% 0.89/1.13      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.89/1.13         = (k2_funct_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.89/1.13  thf('229', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('sup-', [status(thm)], ['71', '72'])).
% 0.89/1.13  thf('230', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('231', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('232', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['227', '228', '229', '230', '231'])).
% 0.89/1.13  thf('233', plain,
% 0.89/1.13      ((~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | (v2_funct_1 @ (k6_partfun1 @ sk_A)))),
% 0.89/1.13      inference('demod', [status(thm)], ['199', '232'])).
% 0.89/1.13  thf('234', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('235', plain,
% 0.89/1.13      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X54)
% 0.89/1.13          | ((k2_relset_1 @ X56 @ X55 @ X54) != (X55))
% 0.89/1.13          | (m1_subset_1 @ (k2_funct_1 @ X54) @ 
% 0.89/1.13             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 0.89/1.13          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X55)))
% 0.89/1.13          | ~ (v1_funct_2 @ X54 @ X56 @ X55)
% 0.89/1.13          | ~ (v1_funct_1 @ X54))),
% 0.89/1.13      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.89/1.13  thf('236', plain,
% 0.89/1.13      ((~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.89/1.13        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.89/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.89/1.13        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['234', '235'])).
% 0.89/1.13  thf('237', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('238', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('239', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('240', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('241', plain,
% 0.89/1.13      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.89/1.13         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.89/1.13        | ((sk_B) != (sk_B)))),
% 0.89/1.13      inference('demod', [status(thm)], ['236', '237', '238', '239', '240'])).
% 0.89/1.13  thf('242', plain,
% 0.89/1.13      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.89/1.13        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('simplify', [status(thm)], ['241'])).
% 0.89/1.13  thf('243', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('244', plain,
% 0.89/1.13      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.89/1.13         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.89/1.13          | ~ (v1_funct_1 @ X37)
% 0.89/1.13          | ~ (v1_funct_1 @ X40)
% 0.89/1.13          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.89/1.13          | (v1_funct_1 @ (k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.89/1.13  thf('245', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['243', '244'])).
% 0.89/1.13  thf('246', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('247', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 0.89/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.89/1.14          | ~ (v1_funct_1 @ X0))),
% 0.89/1.14      inference('demod', [status(thm)], ['245', '246'])).
% 0.89/1.14  thf('248', plain,
% 0.89/1.14      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.14        | (v1_funct_1 @ 
% 0.89/1.14           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 0.89/1.14            (k2_funct_1 @ sk_C))))),
% 0.89/1.14      inference('sup-', [status(thm)], ['242', '247'])).
% 0.89/1.14  thf('249', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.89/1.14      inference('simplify', [status(thm)], ['126'])).
% 0.89/1.14  thf('250', plain,
% 0.89/1.14      ((v1_funct_1 @ 
% 0.89/1.14        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C)))),
% 0.89/1.14      inference('demod', [status(thm)], ['248', '249'])).
% 0.89/1.14  thf('251', plain,
% 0.89/1.14      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.89/1.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.14      inference('simplify', [status(thm)], ['241'])).
% 0.89/1.14  thf('252', plain,
% 0.89/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.14         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.89/1.14            = (k5_relat_1 @ sk_C @ X0))
% 0.89/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.89/1.14          | ~ (v1_funct_1 @ X0))),
% 0.89/1.14      inference('demod', [status(thm)], ['4', '5'])).
% 0.89/1.14  thf('253', plain,
% 0.89/1.14      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.14        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 0.89/1.14            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 0.89/1.14      inference('sup-', [status(thm)], ['251', '252'])).
% 0.89/1.14  thf('254', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.89/1.14      inference('simplify', [status(thm)], ['126'])).
% 0.89/1.14  thf('255', plain,
% 0.89/1.14      (![X8 : $i]:
% 0.89/1.14         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 0.89/1.14          | ~ (v2_funct_1 @ X8)
% 0.89/1.14          | ~ (v1_funct_1 @ X8)
% 0.89/1.14          | ~ (v1_relat_1 @ X8))),
% 0.89/1.14      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.89/1.14  thf('256', plain,
% 0.89/1.14      (![X7 : $i]:
% 0.89/1.14         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.89/1.14          | ~ (v1_funct_1 @ X7)
% 0.89/1.14          | ~ (v1_relat_1 @ X7))),
% 0.89/1.14      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.14  thf('257', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.14      inference('demod', [status(thm)], ['170', '175', '176', '177', '178'])).
% 0.89/1.14  thf('258', plain,
% 0.89/1.14      (![X12 : $i]:
% 0.89/1.14         (~ (v2_funct_1 @ X12)
% 0.89/1.14          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 0.89/1.14              = (k6_relat_1 @ (k2_relat_1 @ X12)))
% 0.89/1.14          | ~ (v1_funct_1 @ X12)
% 0.89/1.14          | ~ (v1_relat_1 @ X12))),
% 0.89/1.14      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.89/1.14  thf('259', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 0.89/1.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.14  thf('260', plain,
% 0.89/1.14      (![X12 : $i]:
% 0.89/1.14         (~ (v2_funct_1 @ X12)
% 0.89/1.14          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 0.89/1.14              = (k6_partfun1 @ (k2_relat_1 @ X12)))
% 0.89/1.14          | ~ (v1_funct_1 @ X12)
% 0.89/1.14          | ~ (v1_relat_1 @ X12))),
% 0.89/1.14      inference('demod', [status(thm)], ['258', '259'])).
% 0.89/1.14  thf('261', plain,
% 0.89/1.14      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.89/1.14          = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.89/1.14        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.14        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.14        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.14      inference('sup+', [status(thm)], ['257', '260'])).
% 0.89/1.14  thf('262', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.89/1.14      inference('simplify', [status(thm)], ['126'])).
% 0.89/1.14  thf('263', plain,
% 0.89/1.14      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.89/1.14          = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.89/1.14        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.14        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.14      inference('demod', [status(thm)], ['261', '262'])).
% 0.89/1.14  thf('264', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 0.89/1.14      inference('demod', [status(thm)], ['189', '190', '191', '192'])).
% 0.89/1.14  thf('265', plain,
% 0.89/1.14      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.89/1.14        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.14        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.14      inference('demod', [status(thm)], ['263', '264'])).
% 0.89/1.14  thf('266', plain,
% 0.89/1.14      ((~ (v1_relat_1 @ sk_C)
% 0.89/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.14        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.14        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['256', '265'])).
% 0.89/1.14  thf('267', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.14      inference('sup-', [status(thm)], ['71', '72'])).
% 0.89/1.14  thf('268', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('269', plain,
% 0.89/1.14      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.14        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.89/1.14      inference('demod', [status(thm)], ['266', '267', '268'])).
% 0.89/1.14  thf('270', plain,
% 0.89/1.14      ((~ (v1_relat_1 @ sk_C)
% 0.89/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.14        | ~ (v2_funct_1 @ sk_C)
% 0.89/1.14        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['255', '269'])).
% 0.89/1.14  thf('271', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.14      inference('sup-', [status(thm)], ['71', '72'])).
% 0.89/1.14  thf('272', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('273', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('274', plain,
% 0.89/1.14      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.89/1.14      inference('demod', [status(thm)], ['270', '271', '272', '273'])).
% 0.89/1.14  thf('275', plain,
% 0.89/1.14      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 0.89/1.14         = (k6_partfun1 @ sk_A))),
% 0.89/1.14      inference('demod', [status(thm)], ['253', '254', '274'])).
% 0.89/1.14  thf('276', plain, ((v1_funct_1 @ (k6_partfun1 @ sk_A))),
% 0.89/1.14      inference('demod', [status(thm)], ['250', '275'])).
% 0.89/1.14  thf('277', plain, ((v2_funct_1 @ (k6_partfun1 @ sk_A))),
% 0.89/1.14      inference('demod', [status(thm)], ['233', '276'])).
% 0.89/1.14  thf('278', plain, ((v1_relat_1 @ sk_D)),
% 0.89/1.14      inference('sup-', [status(thm)], ['47', '48'])).
% 0.89/1.14  thf('279', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('280', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.89/1.14      inference('sup+', [status(thm)], ['53', '54'])).
% 0.89/1.14  thf('281', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.89/1.14      inference('demod', [status(thm)], ['58', '65', '68'])).
% 0.89/1.14  thf('282', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('283', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.14      inference('sup-', [status(thm)], ['71', '72'])).
% 0.89/1.14  thf('284', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 0.89/1.14      inference('demod', [status(thm)],
% 0.89/1.14                ['78', '277', '278', '279', '280', '281', '282', '283'])).
% 0.89/1.14  thf('285', plain, ((v2_funct_1 @ sk_D)),
% 0.89/1.14      inference('simplify', [status(thm)], ['284'])).
% 0.89/1.14  thf('286', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.89/1.14      inference('demod', [status(thm)], ['75', '285'])).
% 0.89/1.14  thf('287', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.14          | ~ (v2_funct_1 @ X0)
% 0.89/1.14          | ~ (v1_funct_1 @ X0)
% 0.89/1.14          | ~ (v1_relat_1 @ X0))),
% 0.89/1.14      inference('simplify', [status(thm)], ['150'])).
% 0.89/1.14  thf('288', plain,
% 0.89/1.14      ((((sk_D) = (k2_funct_1 @ sk_C))
% 0.89/1.14        | ~ (v1_relat_1 @ sk_D)
% 0.89/1.14        | ~ (v1_funct_1 @ sk_D)
% 0.89/1.14        | ~ (v2_funct_1 @ sk_D))),
% 0.89/1.14      inference('sup+', [status(thm)], ['286', '287'])).
% 0.89/1.14  thf('289', plain, ((v1_relat_1 @ sk_D)),
% 0.89/1.14      inference('sup-', [status(thm)], ['47', '48'])).
% 0.89/1.14  thf('290', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('291', plain, ((v2_funct_1 @ sk_D)),
% 0.89/1.14      inference('simplify', [status(thm)], ['284'])).
% 0.89/1.14  thf('292', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.89/1.14      inference('demod', [status(thm)], ['288', '289', '290', '291'])).
% 0.89/1.14  thf('293', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('294', plain, ($false),
% 0.89/1.14      inference('simplify_reflect-', [status(thm)], ['292', '293'])).
% 0.89/1.14  
% 0.89/1.14  % SZS output end Refutation
% 0.89/1.14  
% 0.89/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
