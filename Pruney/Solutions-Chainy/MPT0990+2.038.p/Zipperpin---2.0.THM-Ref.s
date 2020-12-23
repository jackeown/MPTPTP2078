%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ICuAEhWAHM

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:00 EST 2020

% Result     : Theorem 30.92s
% Output     : Refutation 30.92s
% Verified   : 
% Statistics : Number of formulae       :  194 (2106 expanded)
%              Number of leaves         :   52 ( 633 expanded)
%              Depth                    :   22
%              Number of atoms          : 1926 (57136 expanded)
%              Number of equality atoms :  129 (3863 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 )
        = ( k5_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','11'])).

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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
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

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X13 = X16 )
      | ~ ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('26',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

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

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( X2
        = ( k2_funct_1 @ X3 ) )
      | ( ( k5_relat_1 @ X2 @ X3 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
      | ( ( k2_relat_1 @ X2 )
       != ( k1_relat_1 @ X3 ) )
      | ~ ( v2_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('31',plain,
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
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( r2_relset_1 @ X41 @ X41 @ ( k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43 ) @ ( k6_partfun1 @ X41 ) )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
        = X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('35',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( r2_relset_1 @ X41 @ X41 @ ( k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43 ) @ ( k6_relat_1 @ X41 ) )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
        = X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    inference(demod,[status(thm)],['41','44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('50',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('62',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('63',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('65',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('66',plain,(
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

thf('67',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('68',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['64','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('76',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','48','51','52','57','72','73','76'])).

thf('78',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('80',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('81',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
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

thf(zf_stmt_6,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_3 @ C @ B )
     => ( ( C = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [E: $i,D: $i] :
      ( ( zip_tseitin_2 @ E @ D )
     => ( ( v2_funct_1 @ D )
        & ( v2_funct_1 @ E ) ) ) )).

thf(zf_stmt_10,axiom,(
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
           => ( ( zip_tseitin_3 @ C @ B )
              | ( zip_tseitin_2 @ E @ D ) ) ) ) ) )).

thf('83',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( zip_tseitin_2 @ X48 @ X51 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X52 @ X49 @ X49 @ X50 @ X51 @ X48 ) )
      | ( zip_tseitin_3 @ X50 @ X49 )
      | ( ( k2_relset_1 @ X52 @ X49 @ X51 )
       != X49 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X49 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_3 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_2 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_3 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_2 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_2 @ sk_D @ sk_C )
    | ( zip_tseitin_3 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('89',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('90',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( zip_tseitin_2 @ sk_D @ sk_C )
    | ( zip_tseitin_3 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['88','89','90','91','92','93'])).

thf('95',plain,
    ( ( zip_tseitin_3 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( zip_tseitin_3 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('97',plain,
    ( ( zip_tseitin_2 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    zip_tseitin_2 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X44: $i,X45: $i] :
      ( ( v2_funct_1 @ X45 )
      | ~ ( zip_tseitin_2 @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('101',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['78','101'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('103',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('104',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( X2
        = ( k2_funct_1 @ X3 ) )
      | ( ( k5_relat_1 @ X2 @ X3 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
      | ( ( k2_relat_1 @ X2 )
       != ( k1_relat_1 @ X3 ) )
      | ~ ( v2_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
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
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
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
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['102','106'])).

thf('108',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['64','71'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('110',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('111',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['99','100'])).

thf('113',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['78','101'])).

thf('114',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['74','75'])).

thf('115',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['78','101'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['78','101'])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','44','45','46','47'])).

thf('120',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['78','101'])).

thf('121',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('123',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('126',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('129',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('131',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['128','131'])).

thf('133',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['132','133'])).

thf('135',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','134'])).

thf('136',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['78','101'])).

thf('137',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['107','108','109','110','111','112','113','114','115','116','117','118','119','120','135','136'])).

thf('138',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['138','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ICuAEhWAHM
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:04:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 30.92/31.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 30.92/31.16  % Solved by: fo/fo7.sh
% 30.92/31.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 30.92/31.16  % done 3613 iterations in 30.694s
% 30.92/31.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 30.92/31.16  % SZS output start Refutation
% 30.92/31.16  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 30.92/31.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 30.92/31.16  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 30.92/31.16  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 30.92/31.16  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 30.92/31.16  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 30.92/31.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 30.92/31.16  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 30.92/31.16  thf(sk_B_type, type, sk_B: $i).
% 30.92/31.16  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 30.92/31.16  thf(sk_A_type, type, sk_A: $i).
% 30.92/31.16  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 30.92/31.16  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 30.92/31.16  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 30.92/31.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 30.92/31.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 30.92/31.16  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 30.92/31.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 30.92/31.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 30.92/31.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 30.92/31.16  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $o).
% 30.92/31.16  thf(sk_D_type, type, sk_D: $i).
% 30.92/31.16  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 30.92/31.16  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 30.92/31.16  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 30.92/31.16  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 30.92/31.16  thf(sk_C_type, type, sk_C: $i).
% 30.92/31.16  thf(t36_funct_2, conjecture,
% 30.92/31.16    (![A:$i,B:$i,C:$i]:
% 30.92/31.16     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 30.92/31.16         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.92/31.16       ( ![D:$i]:
% 30.92/31.16         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 30.92/31.16             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 30.92/31.16           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 30.92/31.16               ( r2_relset_1 @
% 30.92/31.16                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 30.92/31.16                 ( k6_partfun1 @ A ) ) & 
% 30.92/31.16               ( v2_funct_1 @ C ) ) =>
% 30.92/31.16             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 30.92/31.16               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 30.92/31.16  thf(zf_stmt_0, negated_conjecture,
% 30.92/31.16    (~( ![A:$i,B:$i,C:$i]:
% 30.92/31.16        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 30.92/31.16            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.92/31.16          ( ![D:$i]:
% 30.92/31.16            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 30.92/31.16                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 30.92/31.16              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 30.92/31.16                  ( r2_relset_1 @
% 30.92/31.16                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 30.92/31.16                    ( k6_partfun1 @ A ) ) & 
% 30.92/31.16                  ( v2_funct_1 @ C ) ) =>
% 30.92/31.16                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 30.92/31.16                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 30.92/31.16    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 30.92/31.16  thf('0', plain,
% 30.92/31.16      ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.92/31.16        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 30.92/31.16        (k6_partfun1 @ sk_A))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf(redefinition_k6_partfun1, axiom,
% 30.92/31.16    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 30.92/31.16  thf('1', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 30.92/31.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.92/31.16  thf('2', plain,
% 30.92/31.16      ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.92/31.16        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 30.92/31.16        (k6_relat_1 @ sk_A))),
% 30.92/31.16      inference('demod', [status(thm)], ['0', '1'])).
% 30.92/31.16  thf('3', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('4', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf(redefinition_k1_partfun1, axiom,
% 30.92/31.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 30.92/31.16     ( ( ( v1_funct_1 @ E ) & 
% 30.92/31.16         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 30.92/31.16         ( v1_funct_1 @ F ) & 
% 30.92/31.16         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 30.92/31.16       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 30.92/31.16  thf('5', plain,
% 30.92/31.16      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 30.92/31.16         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 30.92/31.16          | ~ (v1_funct_1 @ X33)
% 30.92/31.16          | ~ (v1_funct_1 @ X36)
% 30.92/31.16          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 30.92/31.16          | ((k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)
% 30.92/31.16              = (k5_relat_1 @ X33 @ X36)))),
% 30.92/31.16      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 30.92/31.16  thf('6', plain,
% 30.92/31.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.92/31.16         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 30.92/31.16            = (k5_relat_1 @ sk_C @ X0))
% 30.92/31.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 30.92/31.16          | ~ (v1_funct_1 @ X0)
% 30.92/31.16          | ~ (v1_funct_1 @ sk_C))),
% 30.92/31.16      inference('sup-', [status(thm)], ['4', '5'])).
% 30.92/31.16  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('8', plain,
% 30.92/31.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.92/31.16         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 30.92/31.16            = (k5_relat_1 @ sk_C @ X0))
% 30.92/31.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 30.92/31.16          | ~ (v1_funct_1 @ X0))),
% 30.92/31.16      inference('demod', [status(thm)], ['6', '7'])).
% 30.92/31.16  thf('9', plain,
% 30.92/31.16      ((~ (v1_funct_1 @ sk_D)
% 30.92/31.16        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 30.92/31.16            = (k5_relat_1 @ sk_C @ sk_D)))),
% 30.92/31.16      inference('sup-', [status(thm)], ['3', '8'])).
% 30.92/31.16  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('11', plain,
% 30.92/31.16      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 30.92/31.16         = (k5_relat_1 @ sk_C @ sk_D))),
% 30.92/31.16      inference('demod', [status(thm)], ['9', '10'])).
% 30.92/31.16  thf('12', plain,
% 30.92/31.16      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 30.92/31.16        (k6_relat_1 @ sk_A))),
% 30.92/31.16      inference('demod', [status(thm)], ['2', '11'])).
% 30.92/31.16  thf('13', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('14', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf(dt_k1_partfun1, axiom,
% 30.92/31.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 30.92/31.16     ( ( ( v1_funct_1 @ E ) & 
% 30.92/31.16         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 30.92/31.16         ( v1_funct_1 @ F ) & 
% 30.92/31.16         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 30.92/31.16       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 30.92/31.16         ( m1_subset_1 @
% 30.92/31.16           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 30.92/31.16           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 30.92/31.16  thf('15', plain,
% 30.92/31.16      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 30.92/31.16         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 30.92/31.16          | ~ (v1_funct_1 @ X25)
% 30.92/31.16          | ~ (v1_funct_1 @ X28)
% 30.92/31.16          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 30.92/31.16          | (m1_subset_1 @ (k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 30.92/31.16             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 30.92/31.16      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 30.92/31.16  thf('16', plain,
% 30.92/31.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.92/31.16         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 30.92/31.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 30.92/31.16          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 30.92/31.16          | ~ (v1_funct_1 @ X1)
% 30.92/31.16          | ~ (v1_funct_1 @ sk_C))),
% 30.92/31.16      inference('sup-', [status(thm)], ['14', '15'])).
% 30.92/31.16  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('18', plain,
% 30.92/31.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.92/31.16         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 30.92/31.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 30.92/31.16          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 30.92/31.16          | ~ (v1_funct_1 @ X1))),
% 30.92/31.16      inference('demod', [status(thm)], ['16', '17'])).
% 30.92/31.16  thf('19', plain,
% 30.92/31.16      ((~ (v1_funct_1 @ sk_D)
% 30.92/31.16        | (m1_subset_1 @ 
% 30.92/31.16           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 30.92/31.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 30.92/31.16      inference('sup-', [status(thm)], ['13', '18'])).
% 30.92/31.16  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('21', plain,
% 30.92/31.16      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 30.92/31.16         = (k5_relat_1 @ sk_C @ sk_D))),
% 30.92/31.16      inference('demod', [status(thm)], ['9', '10'])).
% 30.92/31.16  thf('22', plain,
% 30.92/31.16      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 30.92/31.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.92/31.16      inference('demod', [status(thm)], ['19', '20', '21'])).
% 30.92/31.16  thf(redefinition_r2_relset_1, axiom,
% 30.92/31.16    (![A:$i,B:$i,C:$i,D:$i]:
% 30.92/31.16     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 30.92/31.16         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.92/31.16       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 30.92/31.16  thf('23', plain,
% 30.92/31.16      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 30.92/31.16         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 30.92/31.16          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 30.92/31.16          | ((X13) = (X16))
% 30.92/31.16          | ~ (r2_relset_1 @ X14 @ X15 @ X13 @ X16))),
% 30.92/31.16      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 30.92/31.16  thf('24', plain,
% 30.92/31.16      (![X0 : $i]:
% 30.92/31.16         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 30.92/31.16          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 30.92/31.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 30.92/31.16      inference('sup-', [status(thm)], ['22', '23'])).
% 30.92/31.16  thf('25', plain,
% 30.92/31.16      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 30.92/31.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 30.92/31.16        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 30.92/31.16      inference('sup-', [status(thm)], ['12', '24'])).
% 30.92/31.16  thf(dt_k6_partfun1, axiom,
% 30.92/31.16    (![A:$i]:
% 30.92/31.16     ( ( m1_subset_1 @
% 30.92/31.16         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 30.92/31.16       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 30.92/31.16  thf('26', plain,
% 30.92/31.16      (![X32 : $i]:
% 30.92/31.16         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 30.92/31.16          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 30.92/31.16      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 30.92/31.16  thf('27', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 30.92/31.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.92/31.16  thf('28', plain,
% 30.92/31.16      (![X32 : $i]:
% 30.92/31.16         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 30.92/31.16          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 30.92/31.16      inference('demod', [status(thm)], ['26', '27'])).
% 30.92/31.16  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 30.92/31.16      inference('demod', [status(thm)], ['25', '28'])).
% 30.92/31.16  thf(t64_funct_1, axiom,
% 30.92/31.16    (![A:$i]:
% 30.92/31.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 30.92/31.16       ( ![B:$i]:
% 30.92/31.16         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 30.92/31.16           ( ( ( v2_funct_1 @ A ) & 
% 30.92/31.16               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 30.92/31.16               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 30.92/31.16             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 30.92/31.16  thf('30', plain,
% 30.92/31.16      (![X2 : $i, X3 : $i]:
% 30.92/31.16         (~ (v1_relat_1 @ X2)
% 30.92/31.16          | ~ (v1_funct_1 @ X2)
% 30.92/31.16          | ((X2) = (k2_funct_1 @ X3))
% 30.92/31.16          | ((k5_relat_1 @ X2 @ X3) != (k6_relat_1 @ (k2_relat_1 @ X3)))
% 30.92/31.16          | ((k2_relat_1 @ X2) != (k1_relat_1 @ X3))
% 30.92/31.16          | ~ (v2_funct_1 @ X3)
% 30.92/31.16          | ~ (v1_funct_1 @ X3)
% 30.92/31.16          | ~ (v1_relat_1 @ X3))),
% 30.92/31.16      inference('cnf', [status(esa)], [t64_funct_1])).
% 30.92/31.16  thf('31', plain,
% 30.92/31.16      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 30.92/31.16        | ~ (v1_relat_1 @ sk_D)
% 30.92/31.16        | ~ (v1_funct_1 @ sk_D)
% 30.92/31.16        | ~ (v2_funct_1 @ sk_D)
% 30.92/31.16        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 30.92/31.16        | ((sk_C) = (k2_funct_1 @ sk_D))
% 30.92/31.16        | ~ (v1_funct_1 @ sk_C)
% 30.92/31.16        | ~ (v1_relat_1 @ sk_C))),
% 30.92/31.16      inference('sup-', [status(thm)], ['29', '30'])).
% 30.92/31.16  thf('32', plain,
% 30.92/31.16      ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.92/31.16        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 30.92/31.16        (k6_relat_1 @ sk_A))),
% 30.92/31.16      inference('demod', [status(thm)], ['0', '1'])).
% 30.92/31.16  thf('33', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf(t24_funct_2, axiom,
% 30.92/31.16    (![A:$i,B:$i,C:$i]:
% 30.92/31.16     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 30.92/31.16         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.92/31.16       ( ![D:$i]:
% 30.92/31.16         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 30.92/31.16             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 30.92/31.16           ( ( r2_relset_1 @
% 30.92/31.16               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 30.92/31.16               ( k6_partfun1 @ B ) ) =>
% 30.92/31.16             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 30.92/31.16  thf('34', plain,
% 30.92/31.16      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 30.92/31.16         (~ (v1_funct_1 @ X40)
% 30.92/31.16          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 30.92/31.16          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 30.92/31.16          | ~ (r2_relset_1 @ X41 @ X41 @ 
% 30.92/31.16               (k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43) @ 
% 30.92/31.16               (k6_partfun1 @ X41))
% 30.92/31.16          | ((k2_relset_1 @ X42 @ X41 @ X43) = (X41))
% 30.92/31.16          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 30.92/31.16          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 30.92/31.16          | ~ (v1_funct_1 @ X43))),
% 30.92/31.16      inference('cnf', [status(esa)], [t24_funct_2])).
% 30.92/31.16  thf('35', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 30.92/31.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.92/31.16  thf('36', plain,
% 30.92/31.16      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 30.92/31.16         (~ (v1_funct_1 @ X40)
% 30.92/31.16          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 30.92/31.16          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 30.92/31.16          | ~ (r2_relset_1 @ X41 @ X41 @ 
% 30.92/31.16               (k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43) @ 
% 30.92/31.16               (k6_relat_1 @ X41))
% 30.92/31.16          | ((k2_relset_1 @ X42 @ X41 @ X43) = (X41))
% 30.92/31.16          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 30.92/31.16          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 30.92/31.16          | ~ (v1_funct_1 @ X43))),
% 30.92/31.16      inference('demod', [status(thm)], ['34', '35'])).
% 30.92/31.16  thf('37', plain,
% 30.92/31.16      (![X0 : $i]:
% 30.92/31.16         (~ (v1_funct_1 @ X0)
% 30.92/31.16          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 30.92/31.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 30.92/31.16          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 30.92/31.16          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.92/31.16               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 30.92/31.16               (k6_relat_1 @ sk_A))
% 30.92/31.16          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 30.92/31.16          | ~ (v1_funct_1 @ sk_C))),
% 30.92/31.16      inference('sup-', [status(thm)], ['33', '36'])).
% 30.92/31.16  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('40', plain,
% 30.92/31.16      (![X0 : $i]:
% 30.92/31.16         (~ (v1_funct_1 @ X0)
% 30.92/31.16          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 30.92/31.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 30.92/31.16          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 30.92/31.16          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.92/31.16               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 30.92/31.16               (k6_relat_1 @ sk_A)))),
% 30.92/31.16      inference('demod', [status(thm)], ['37', '38', '39'])).
% 30.92/31.16  thf('41', plain,
% 30.92/31.16      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 30.92/31.16        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 30.92/31.16        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 30.92/31.16        | ~ (v1_funct_1 @ sk_D))),
% 30.92/31.16      inference('sup-', [status(thm)], ['32', '40'])).
% 30.92/31.16  thf('42', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf(redefinition_k2_relset_1, axiom,
% 30.92/31.16    (![A:$i,B:$i,C:$i]:
% 30.92/31.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.92/31.16       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 30.92/31.16  thf('43', plain,
% 30.92/31.16      (![X10 : $i, X11 : $i, X12 : $i]:
% 30.92/31.16         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 30.92/31.16          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 30.92/31.16      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 30.92/31.16  thf('44', plain,
% 30.92/31.16      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 30.92/31.16      inference('sup-', [status(thm)], ['42', '43'])).
% 30.92/31.16  thf('45', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 30.92/31.16      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 30.92/31.16  thf('49', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf(cc1_relset_1, axiom,
% 30.92/31.16    (![A:$i,B:$i,C:$i]:
% 30.92/31.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.92/31.16       ( v1_relat_1 @ C ) ))).
% 30.92/31.16  thf('50', plain,
% 30.92/31.16      (![X4 : $i, X5 : $i, X6 : $i]:
% 30.92/31.16         ((v1_relat_1 @ X4)
% 30.92/31.16          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 30.92/31.16      inference('cnf', [status(esa)], [cc1_relset_1])).
% 30.92/31.16  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 30.92/31.16      inference('sup-', [status(thm)], ['49', '50'])).
% 30.92/31.16  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('53', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('54', plain,
% 30.92/31.16      (![X10 : $i, X11 : $i, X12 : $i]:
% 30.92/31.16         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 30.92/31.16          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 30.92/31.16      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 30.92/31.16  thf('55', plain,
% 30.92/31.16      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 30.92/31.16      inference('sup-', [status(thm)], ['53', '54'])).
% 30.92/31.16  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('57', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 30.92/31.16      inference('sup+', [status(thm)], ['55', '56'])).
% 30.92/31.16  thf('58', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf(d1_funct_2, axiom,
% 30.92/31.16    (![A:$i,B:$i,C:$i]:
% 30.92/31.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.92/31.16       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 30.92/31.16           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 30.92/31.16             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 30.92/31.16         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 30.92/31.16           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 30.92/31.16             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 30.92/31.16  thf(zf_stmt_1, axiom,
% 30.92/31.16    (![C:$i,B:$i,A:$i]:
% 30.92/31.16     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 30.92/31.16       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 30.92/31.16  thf('59', plain,
% 30.92/31.16      (![X19 : $i, X20 : $i, X21 : $i]:
% 30.92/31.16         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 30.92/31.16          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 30.92/31.16          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_1])).
% 30.92/31.16  thf('60', plain,
% 30.92/31.16      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 30.92/31.16        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 30.92/31.16      inference('sup-', [status(thm)], ['58', '59'])).
% 30.92/31.16  thf('61', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf(redefinition_k1_relset_1, axiom,
% 30.92/31.16    (![A:$i,B:$i,C:$i]:
% 30.92/31.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.92/31.16       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 30.92/31.16  thf('62', plain,
% 30.92/31.16      (![X7 : $i, X8 : $i, X9 : $i]:
% 30.92/31.16         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 30.92/31.16          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 30.92/31.16      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 30.92/31.16  thf('63', plain,
% 30.92/31.16      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 30.92/31.16      inference('sup-', [status(thm)], ['61', '62'])).
% 30.92/31.16  thf('64', plain,
% 30.92/31.16      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 30.92/31.16      inference('demod', [status(thm)], ['60', '63'])).
% 30.92/31.16  thf(zf_stmt_2, axiom,
% 30.92/31.16    (![B:$i,A:$i]:
% 30.92/31.16     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 30.92/31.16       ( zip_tseitin_0 @ B @ A ) ))).
% 30.92/31.16  thf('65', plain,
% 30.92/31.16      (![X17 : $i, X18 : $i]:
% 30.92/31.16         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 30.92/31.16  thf('66', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 30.92/31.16  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 30.92/31.16  thf(zf_stmt_5, axiom,
% 30.92/31.16    (![A:$i,B:$i,C:$i]:
% 30.92/31.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.92/31.16       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 30.92/31.16         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 30.92/31.16           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 30.92/31.16             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 30.92/31.16  thf('67', plain,
% 30.92/31.16      (![X22 : $i, X23 : $i, X24 : $i]:
% 30.92/31.16         (~ (zip_tseitin_0 @ X22 @ X23)
% 30.92/31.16          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 30.92/31.16          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_5])).
% 30.92/31.16  thf('68', plain,
% 30.92/31.16      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 30.92/31.16      inference('sup-', [status(thm)], ['66', '67'])).
% 30.92/31.16  thf('69', plain,
% 30.92/31.16      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 30.92/31.16      inference('sup-', [status(thm)], ['65', '68'])).
% 30.92/31.16  thf('70', plain, (((sk_A) != (k1_xboole_0))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('71', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 30.92/31.16      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 30.92/31.16  thf('72', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 30.92/31.16      inference('demod', [status(thm)], ['64', '71'])).
% 30.92/31.16  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('74', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('75', plain,
% 30.92/31.16      (![X4 : $i, X5 : $i, X6 : $i]:
% 30.92/31.16         ((v1_relat_1 @ X4)
% 30.92/31.16          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 30.92/31.16      inference('cnf', [status(esa)], [cc1_relset_1])).
% 30.92/31.16  thf('76', plain, ((v1_relat_1 @ sk_C)),
% 30.92/31.16      inference('sup-', [status(thm)], ['74', '75'])).
% 30.92/31.16  thf('77', plain,
% 30.92/31.16      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 30.92/31.16        | ~ (v2_funct_1 @ sk_D)
% 30.92/31.16        | ((sk_B) != (sk_B))
% 30.92/31.16        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 30.92/31.16      inference('demod', [status(thm)],
% 30.92/31.16                ['31', '48', '51', '52', '57', '72', '73', '76'])).
% 30.92/31.16  thf('78', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 30.92/31.16      inference('simplify', [status(thm)], ['77'])).
% 30.92/31.16  thf('79', plain,
% 30.92/31.16      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 30.92/31.16         = (k5_relat_1 @ sk_C @ sk_D))),
% 30.92/31.16      inference('demod', [status(thm)], ['9', '10'])).
% 30.92/31.16  thf('80', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 30.92/31.16      inference('demod', [status(thm)], ['25', '28'])).
% 30.92/31.16  thf('81', plain,
% 30.92/31.16      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 30.92/31.16         = (k6_relat_1 @ sk_A))),
% 30.92/31.16      inference('demod', [status(thm)], ['79', '80'])).
% 30.92/31.16  thf('82', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf(t30_funct_2, axiom,
% 30.92/31.16    (![A:$i,B:$i,C:$i,D:$i]:
% 30.92/31.16     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 30.92/31.16         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 30.92/31.16       ( ![E:$i]:
% 30.92/31.16         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 30.92/31.16             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 30.92/31.16           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 30.92/31.16               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 30.92/31.16             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 30.92/31.16               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 30.92/31.16  thf(zf_stmt_6, type, zip_tseitin_3 : $i > $i > $o).
% 30.92/31.16  thf(zf_stmt_7, axiom,
% 30.92/31.16    (![C:$i,B:$i]:
% 30.92/31.16     ( ( zip_tseitin_3 @ C @ B ) =>
% 30.92/31.16       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 30.92/31.16  thf(zf_stmt_8, type, zip_tseitin_2 : $i > $i > $o).
% 30.92/31.16  thf(zf_stmt_9, axiom,
% 30.92/31.16    (![E:$i,D:$i]:
% 30.92/31.16     ( ( zip_tseitin_2 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 30.92/31.16  thf(zf_stmt_10, axiom,
% 30.92/31.16    (![A:$i,B:$i,C:$i,D:$i]:
% 30.92/31.16     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 30.92/31.16         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.92/31.16       ( ![E:$i]:
% 30.92/31.16         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 30.92/31.16             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 30.92/31.16           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 30.92/31.16               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 30.92/31.16             ( ( zip_tseitin_3 @ C @ B ) | ( zip_tseitin_2 @ E @ D ) ) ) ) ) ))).
% 30.92/31.16  thf('83', plain,
% 30.92/31.16      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 30.92/31.16         (~ (v1_funct_1 @ X48)
% 30.92/31.16          | ~ (v1_funct_2 @ X48 @ X49 @ X50)
% 30.92/31.16          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 30.92/31.16          | (zip_tseitin_2 @ X48 @ X51)
% 30.92/31.16          | ~ (v2_funct_1 @ (k1_partfun1 @ X52 @ X49 @ X49 @ X50 @ X51 @ X48))
% 30.92/31.16          | (zip_tseitin_3 @ X50 @ X49)
% 30.92/31.16          | ((k2_relset_1 @ X52 @ X49 @ X51) != (X49))
% 30.92/31.16          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X49)))
% 30.92/31.16          | ~ (v1_funct_2 @ X51 @ X52 @ X49)
% 30.92/31.16          | ~ (v1_funct_1 @ X51))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_10])).
% 30.92/31.16  thf('84', plain,
% 30.92/31.16      (![X0 : $i, X1 : $i]:
% 30.92/31.16         (~ (v1_funct_1 @ X0)
% 30.92/31.16          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 30.92/31.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 30.92/31.16          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 30.92/31.16          | (zip_tseitin_3 @ sk_A @ sk_B)
% 30.92/31.16          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 30.92/31.16          | (zip_tseitin_2 @ sk_D @ X0)
% 30.92/31.16          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 30.92/31.16          | ~ (v1_funct_1 @ sk_D))),
% 30.92/31.16      inference('sup-', [status(thm)], ['82', '83'])).
% 30.92/31.16  thf('85', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('86', plain, ((v1_funct_1 @ sk_D)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('87', plain,
% 30.92/31.16      (![X0 : $i, X1 : $i]:
% 30.92/31.16         (~ (v1_funct_1 @ X0)
% 30.92/31.16          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 30.92/31.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 30.92/31.16          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 30.92/31.16          | (zip_tseitin_3 @ sk_A @ sk_B)
% 30.92/31.16          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 30.92/31.16          | (zip_tseitin_2 @ sk_D @ X0))),
% 30.92/31.16      inference('demod', [status(thm)], ['84', '85', '86'])).
% 30.92/31.16  thf('88', plain,
% 30.92/31.16      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 30.92/31.16        | (zip_tseitin_2 @ sk_D @ sk_C)
% 30.92/31.16        | (zip_tseitin_3 @ sk_A @ sk_B)
% 30.92/31.16        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 30.92/31.16        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 30.92/31.16        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 30.92/31.16        | ~ (v1_funct_1 @ sk_C))),
% 30.92/31.16      inference('sup-', [status(thm)], ['81', '87'])).
% 30.92/31.16  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 30.92/31.16  thf('89', plain, (![X0 : $i]: (v2_funct_1 @ (k6_relat_1 @ X0))),
% 30.92/31.16      inference('cnf', [status(esa)], [t52_funct_1])).
% 30.92/31.16  thf('90', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('91', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('92', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('94', plain,
% 30.92/31.16      (((zip_tseitin_2 @ sk_D @ sk_C)
% 30.92/31.16        | (zip_tseitin_3 @ sk_A @ sk_B)
% 30.92/31.16        | ((sk_B) != (sk_B)))),
% 30.92/31.16      inference('demod', [status(thm)], ['88', '89', '90', '91', '92', '93'])).
% 30.92/31.16  thf('95', plain,
% 30.92/31.16      (((zip_tseitin_3 @ sk_A @ sk_B) | (zip_tseitin_2 @ sk_D @ sk_C))),
% 30.92/31.16      inference('simplify', [status(thm)], ['94'])).
% 30.92/31.16  thf('96', plain,
% 30.92/31.16      (![X46 : $i, X47 : $i]:
% 30.92/31.16         (((X46) = (k1_xboole_0)) | ~ (zip_tseitin_3 @ X46 @ X47))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_7])).
% 30.92/31.16  thf('97', plain,
% 30.92/31.16      (((zip_tseitin_2 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 30.92/31.16      inference('sup-', [status(thm)], ['95', '96'])).
% 30.92/31.16  thf('98', plain, (((sk_A) != (k1_xboole_0))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('99', plain, ((zip_tseitin_2 @ sk_D @ sk_C)),
% 30.92/31.16      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 30.92/31.16  thf('100', plain,
% 30.92/31.16      (![X44 : $i, X45 : $i]:
% 30.92/31.16         ((v2_funct_1 @ X45) | ~ (zip_tseitin_2 @ X45 @ X44))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_9])).
% 30.92/31.16  thf('101', plain, ((v2_funct_1 @ sk_D)),
% 30.92/31.16      inference('sup-', [status(thm)], ['99', '100'])).
% 30.92/31.16  thf('102', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 30.92/31.16      inference('demod', [status(thm)], ['78', '101'])).
% 30.92/31.16  thf(t61_funct_1, axiom,
% 30.92/31.16    (![A:$i]:
% 30.92/31.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 30.92/31.16       ( ( v2_funct_1 @ A ) =>
% 30.92/31.16         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 30.92/31.16             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 30.92/31.16           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 30.92/31.16             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 30.92/31.16  thf('103', plain,
% 30.92/31.16      (![X1 : $i]:
% 30.92/31.16         (~ (v2_funct_1 @ X1)
% 30.92/31.16          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 30.92/31.16              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 30.92/31.16          | ~ (v1_funct_1 @ X1)
% 30.92/31.16          | ~ (v1_relat_1 @ X1))),
% 30.92/31.16      inference('cnf', [status(esa)], [t61_funct_1])).
% 30.92/31.16  thf('104', plain,
% 30.92/31.16      (![X2 : $i, X3 : $i]:
% 30.92/31.16         (~ (v1_relat_1 @ X2)
% 30.92/31.16          | ~ (v1_funct_1 @ X2)
% 30.92/31.16          | ((X2) = (k2_funct_1 @ X3))
% 30.92/31.16          | ((k5_relat_1 @ X2 @ X3) != (k6_relat_1 @ (k2_relat_1 @ X3)))
% 30.92/31.16          | ((k2_relat_1 @ X2) != (k1_relat_1 @ X3))
% 30.92/31.16          | ~ (v2_funct_1 @ X3)
% 30.92/31.16          | ~ (v1_funct_1 @ X3)
% 30.92/31.16          | ~ (v1_relat_1 @ X3))),
% 30.92/31.16      inference('cnf', [status(esa)], [t64_funct_1])).
% 30.92/31.16  thf('105', plain,
% 30.92/31.16      (![X0 : $i]:
% 30.92/31.16         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 30.92/31.16            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 30.92/31.16          | ~ (v1_relat_1 @ X0)
% 30.92/31.16          | ~ (v1_funct_1 @ X0)
% 30.92/31.16          | ~ (v2_funct_1 @ X0)
% 30.92/31.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 30.92/31.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 30.92/31.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 30.92/31.16          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 30.92/31.16          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 30.92/31.16          | ~ (v1_funct_1 @ X0)
% 30.92/31.16          | ~ (v1_relat_1 @ X0))),
% 30.92/31.16      inference('sup-', [status(thm)], ['103', '104'])).
% 30.92/31.16  thf('106', plain,
% 30.92/31.16      (![X0 : $i]:
% 30.92/31.16         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 30.92/31.16          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 30.92/31.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 30.92/31.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 30.92/31.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 30.92/31.16          | ~ (v2_funct_1 @ X0)
% 30.92/31.16          | ~ (v1_funct_1 @ X0)
% 30.92/31.16          | ~ (v1_relat_1 @ X0)
% 30.92/31.16          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 30.92/31.16              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 30.92/31.16      inference('simplify', [status(thm)], ['105'])).
% 30.92/31.16  thf('107', plain,
% 30.92/31.16      ((((k6_relat_1 @ (k1_relat_1 @ sk_D))
% 30.92/31.16          != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 30.92/31.16        | ~ (v1_relat_1 @ sk_D)
% 30.92/31.16        | ~ (v1_funct_1 @ sk_D)
% 30.92/31.16        | ~ (v2_funct_1 @ sk_D)
% 30.92/31.16        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 30.92/31.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 30.92/31.16        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 30.92/31.16        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 30.92/31.16        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 30.92/31.16      inference('sup-', [status(thm)], ['102', '106'])).
% 30.92/31.16  thf('108', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 30.92/31.16      inference('demod', [status(thm)], ['64', '71'])).
% 30.92/31.16  thf('109', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 30.92/31.16      inference('sup+', [status(thm)], ['55', '56'])).
% 30.92/31.16  thf('110', plain, ((v1_relat_1 @ sk_D)),
% 30.92/31.16      inference('sup-', [status(thm)], ['49', '50'])).
% 30.92/31.16  thf('111', plain, ((v1_funct_1 @ sk_D)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('112', plain, ((v2_funct_1 @ sk_D)),
% 30.92/31.16      inference('sup-', [status(thm)], ['99', '100'])).
% 30.92/31.16  thf('113', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 30.92/31.16      inference('demod', [status(thm)], ['78', '101'])).
% 30.92/31.16  thf('114', plain, ((v1_relat_1 @ sk_C)),
% 30.92/31.16      inference('sup-', [status(thm)], ['74', '75'])).
% 30.92/31.16  thf('115', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 30.92/31.16      inference('demod', [status(thm)], ['78', '101'])).
% 30.92/31.16  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('117', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 30.92/31.16      inference('demod', [status(thm)], ['78', '101'])).
% 30.92/31.16  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('119', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 30.92/31.16      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 30.92/31.16  thf('120', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 30.92/31.16      inference('demod', [status(thm)], ['78', '101'])).
% 30.92/31.16  thf('121', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('122', plain,
% 30.92/31.16      (![X19 : $i, X20 : $i, X21 : $i]:
% 30.92/31.16         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 30.92/31.16          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 30.92/31.16          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_1])).
% 30.92/31.16  thf('123', plain,
% 30.92/31.16      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 30.92/31.16        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 30.92/31.16      inference('sup-', [status(thm)], ['121', '122'])).
% 30.92/31.16  thf('124', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('125', plain,
% 30.92/31.16      (![X7 : $i, X8 : $i, X9 : $i]:
% 30.92/31.16         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 30.92/31.16          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 30.92/31.16      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 30.92/31.16  thf('126', plain,
% 30.92/31.16      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 30.92/31.16      inference('sup-', [status(thm)], ['124', '125'])).
% 30.92/31.16  thf('127', plain,
% 30.92/31.16      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 30.92/31.16      inference('demod', [status(thm)], ['123', '126'])).
% 30.92/31.16  thf('128', plain,
% 30.92/31.16      (![X17 : $i, X18 : $i]:
% 30.92/31.16         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 30.92/31.16  thf('129', plain,
% 30.92/31.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('130', plain,
% 30.92/31.16      (![X22 : $i, X23 : $i, X24 : $i]:
% 30.92/31.16         (~ (zip_tseitin_0 @ X22 @ X23)
% 30.92/31.16          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 30.92/31.16          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_5])).
% 30.92/31.16  thf('131', plain,
% 30.92/31.16      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 30.92/31.16      inference('sup-', [status(thm)], ['129', '130'])).
% 30.92/31.16  thf('132', plain,
% 30.92/31.16      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 30.92/31.16      inference('sup-', [status(thm)], ['128', '131'])).
% 30.92/31.16  thf('133', plain, (((sk_B) != (k1_xboole_0))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('134', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 30.92/31.16      inference('simplify_reflect-', [status(thm)], ['132', '133'])).
% 30.92/31.16  thf('135', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 30.92/31.16      inference('demod', [status(thm)], ['127', '134'])).
% 30.92/31.16  thf('136', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 30.92/31.16      inference('demod', [status(thm)], ['78', '101'])).
% 30.92/31.16  thf('137', plain,
% 30.92/31.16      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 30.92/31.16        | ((sk_A) != (sk_A))
% 30.92/31.16        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 30.92/31.16      inference('demod', [status(thm)],
% 30.92/31.16                ['107', '108', '109', '110', '111', '112', '113', '114', 
% 30.92/31.16                 '115', '116', '117', '118', '119', '120', '135', '136'])).
% 30.92/31.16  thf('138', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 30.92/31.16      inference('simplify', [status(thm)], ['137'])).
% 30.92/31.16  thf('139', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 30.92/31.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.16  thf('140', plain, ($false),
% 30.92/31.16      inference('simplify_reflect-', [status(thm)], ['138', '139'])).
% 30.92/31.16  
% 30.92/31.16  % SZS output end Refutation
% 30.92/31.16  
% 30.92/31.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
