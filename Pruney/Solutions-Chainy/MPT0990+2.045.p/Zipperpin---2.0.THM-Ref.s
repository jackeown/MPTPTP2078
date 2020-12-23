%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.86YRDPKIbr

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:01 EST 2020

% Result     : Theorem 18.80s
% Output     : Refutation 18.80s
% Verified   : 
% Statistics : Number of formulae       :  193 (1814 expanded)
%              Number of leaves         :   51 ( 562 expanded)
%              Depth                    :   20
%              Number of atoms          : 1932 (46978 expanded)
%              Number of equality atoms :  130 (3114 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 )
        = ( k5_relat_1 @ X33 @ X36 ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X32 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( X14 = X17 )
      | ~ ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 ) ) ),
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
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k2_funct_1 @ X4 ) )
      | ( ( k5_relat_1 @ X3 @ X4 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('27',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k2_funct_1 @ X4 ) )
      | ( ( k5_relat_1 @ X3 @ X4 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X4 ) ) )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 )
      | ( X14 != X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('50',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('69',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('70',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['60','67','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','48','51','52','57','71','72','75'])).

thf('77',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('79',plain,(
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

thf('80',plain,(
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

thf('81',plain,(
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
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_3 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_2 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_2 @ sk_D @ sk_C )
    | ( zip_tseitin_3 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('86',plain,(
    ! [X1: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('87',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('88',plain,(
    ! [X1: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( zip_tseitin_2 @ sk_D @ sk_C )
    | ( zip_tseitin_3 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['85','88','89','90','91','92'])).

thf('94',plain,
    ( ( zip_tseitin_3 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( zip_tseitin_3 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('96',plain,
    ( ( zip_tseitin_2 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    zip_tseitin_2 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X44: $i,X45: $i] :
      ( ( v2_funct_1 @ X45 )
      | ~ ( zip_tseitin_2 @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('100',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','100'])).

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
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X2 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('103',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('104',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X2 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k2_funct_1 @ X4 ) )
      | ( ( k5_relat_1 @ X3 @ X4 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X4 ) ) )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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

thf('108',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
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
    inference('sup-',[status(thm)],['101','107'])).

thf('109',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['60','67','70'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('111',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('112',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['98','99'])).

thf('114',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','100'])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['73','74'])).

thf('116',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','100'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','100'])).

thf('119',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','41','44','45','46','47'])).

thf('121',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','100'])).

thf('122',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('124',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('128',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['125','128'])).

thf('130',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['129','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('134',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['124','131','134'])).

thf('136',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','100'])).

thf('137',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['108','109','110','111','112','113','114','115','116','117','118','119','120','121','135','136'])).

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
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.86YRDPKIbr
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:58:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 18.80/19.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 18.80/19.01  % Solved by: fo/fo7.sh
% 18.80/19.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.80/19.01  % done 3423 iterations in 18.554s
% 18.80/19.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 18.80/19.01  % SZS output start Refutation
% 18.80/19.01  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 18.80/19.01  thf(sk_D_type, type, sk_D: $i).
% 18.80/19.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 18.80/19.01  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 18.80/19.01  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 18.80/19.01  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 18.80/19.01  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 18.80/19.01  thf(sk_B_type, type, sk_B: $i).
% 18.80/19.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 18.80/19.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 18.80/19.01  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 18.80/19.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 18.80/19.01  thf(sk_C_type, type, sk_C: $i).
% 18.80/19.01  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 18.80/19.01  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 18.80/19.01  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 18.80/19.01  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 18.80/19.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 18.80/19.01  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 18.80/19.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 18.80/19.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 18.80/19.01  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 18.80/19.01  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $o).
% 18.80/19.01  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 18.80/19.01  thf(sk_A_type, type, sk_A: $i).
% 18.80/19.01  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 18.80/19.01  thf(t36_funct_2, conjecture,
% 18.80/19.01    (![A:$i,B:$i,C:$i]:
% 18.80/19.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 18.80/19.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.80/19.01       ( ![D:$i]:
% 18.80/19.01         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 18.80/19.01             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 18.80/19.01           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 18.80/19.01               ( r2_relset_1 @
% 18.80/19.01                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 18.80/19.01                 ( k6_partfun1 @ A ) ) & 
% 18.80/19.01               ( v2_funct_1 @ C ) ) =>
% 18.80/19.01             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 18.80/19.01               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 18.80/19.01  thf(zf_stmt_0, negated_conjecture,
% 18.80/19.01    (~( ![A:$i,B:$i,C:$i]:
% 18.80/19.01        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 18.80/19.01            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.80/19.01          ( ![D:$i]:
% 18.80/19.01            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 18.80/19.01                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 18.80/19.01              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 18.80/19.01                  ( r2_relset_1 @
% 18.80/19.01                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 18.80/19.01                    ( k6_partfun1 @ A ) ) & 
% 18.80/19.01                  ( v2_funct_1 @ C ) ) =>
% 18.80/19.01                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 18.80/19.01                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 18.80/19.01    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 18.80/19.01  thf('0', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('1', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf(redefinition_k1_partfun1, axiom,
% 18.80/19.01    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 18.80/19.01     ( ( ( v1_funct_1 @ E ) & 
% 18.80/19.01         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 18.80/19.01         ( v1_funct_1 @ F ) & 
% 18.80/19.01         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 18.80/19.01       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 18.80/19.01  thf('2', plain,
% 18.80/19.01      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 18.80/19.01         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 18.80/19.01          | ~ (v1_funct_1 @ X33)
% 18.80/19.01          | ~ (v1_funct_1 @ X36)
% 18.80/19.01          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 18.80/19.01          | ((k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)
% 18.80/19.01              = (k5_relat_1 @ X33 @ X36)))),
% 18.80/19.01      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 18.80/19.01  thf('3', plain,
% 18.80/19.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.80/19.01         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 18.80/19.01            = (k5_relat_1 @ sk_C @ X0))
% 18.80/19.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 18.80/19.01          | ~ (v1_funct_1 @ X0)
% 18.80/19.01          | ~ (v1_funct_1 @ sk_C))),
% 18.80/19.01      inference('sup-', [status(thm)], ['1', '2'])).
% 18.80/19.01  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('5', plain,
% 18.80/19.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.80/19.01         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 18.80/19.01            = (k5_relat_1 @ sk_C @ X0))
% 18.80/19.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 18.80/19.01          | ~ (v1_funct_1 @ X0))),
% 18.80/19.01      inference('demod', [status(thm)], ['3', '4'])).
% 18.80/19.01  thf('6', plain,
% 18.80/19.01      ((~ (v1_funct_1 @ sk_D)
% 18.80/19.01        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 18.80/19.01            = (k5_relat_1 @ sk_C @ sk_D)))),
% 18.80/19.01      inference('sup-', [status(thm)], ['0', '5'])).
% 18.80/19.01  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('8', plain,
% 18.80/19.01      ((r2_relset_1 @ sk_A @ sk_A @ 
% 18.80/19.01        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 18.80/19.01        (k6_partfun1 @ sk_A))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('9', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('10', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf(dt_k1_partfun1, axiom,
% 18.80/19.01    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 18.80/19.01     ( ( ( v1_funct_1 @ E ) & 
% 18.80/19.01         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 18.80/19.01         ( v1_funct_1 @ F ) & 
% 18.80/19.01         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 18.80/19.01       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 18.80/19.01         ( m1_subset_1 @
% 18.80/19.01           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 18.80/19.01           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 18.80/19.01  thf('11', plain,
% 18.80/19.01      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 18.80/19.01         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 18.80/19.01          | ~ (v1_funct_1 @ X27)
% 18.80/19.01          | ~ (v1_funct_1 @ X30)
% 18.80/19.01          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 18.80/19.01          | (m1_subset_1 @ (k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30) @ 
% 18.80/19.01             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X32))))),
% 18.80/19.01      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 18.80/19.01  thf('12', plain,
% 18.80/19.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.80/19.01         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 18.80/19.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 18.80/19.01          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 18.80/19.01          | ~ (v1_funct_1 @ X1)
% 18.80/19.01          | ~ (v1_funct_1 @ sk_C))),
% 18.80/19.01      inference('sup-', [status(thm)], ['10', '11'])).
% 18.80/19.01  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('14', plain,
% 18.80/19.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.80/19.01         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 18.80/19.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 18.80/19.01          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 18.80/19.01          | ~ (v1_funct_1 @ X1))),
% 18.80/19.01      inference('demod', [status(thm)], ['12', '13'])).
% 18.80/19.01  thf('15', plain,
% 18.80/19.01      ((~ (v1_funct_1 @ sk_D)
% 18.80/19.01        | (m1_subset_1 @ 
% 18.80/19.01           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 18.80/19.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 18.80/19.01      inference('sup-', [status(thm)], ['9', '14'])).
% 18.80/19.01  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('17', plain,
% 18.80/19.01      ((m1_subset_1 @ 
% 18.80/19.01        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 18.80/19.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 18.80/19.01      inference('demod', [status(thm)], ['15', '16'])).
% 18.80/19.01  thf(redefinition_r2_relset_1, axiom,
% 18.80/19.01    (![A:$i,B:$i,C:$i,D:$i]:
% 18.80/19.01     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 18.80/19.01         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.80/19.01       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 18.80/19.01  thf('18', plain,
% 18.80/19.01      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 18.80/19.01         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 18.80/19.01          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 18.80/19.01          | ((X14) = (X17))
% 18.80/19.01          | ~ (r2_relset_1 @ X15 @ X16 @ X14 @ X17))),
% 18.80/19.01      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 18.80/19.01  thf('19', plain,
% 18.80/19.01      (![X0 : $i]:
% 18.80/19.01         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 18.80/19.01             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 18.80/19.01          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 18.80/19.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 18.80/19.01      inference('sup-', [status(thm)], ['17', '18'])).
% 18.80/19.01  thf('20', plain,
% 18.80/19.01      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 18.80/19.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 18.80/19.01        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 18.80/19.01            = (k6_partfun1 @ sk_A)))),
% 18.80/19.01      inference('sup-', [status(thm)], ['8', '19'])).
% 18.80/19.01  thf(t29_relset_1, axiom,
% 18.80/19.01    (![A:$i]:
% 18.80/19.01     ( m1_subset_1 @
% 18.80/19.01       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 18.80/19.01  thf('21', plain,
% 18.80/19.01      (![X18 : $i]:
% 18.80/19.01         (m1_subset_1 @ (k6_relat_1 @ X18) @ 
% 18.80/19.01          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 18.80/19.01      inference('cnf', [status(esa)], [t29_relset_1])).
% 18.80/19.01  thf(redefinition_k6_partfun1, axiom,
% 18.80/19.01    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 18.80/19.01  thf('22', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 18.80/19.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 18.80/19.01  thf('23', plain,
% 18.80/19.01      (![X18 : $i]:
% 18.80/19.01         (m1_subset_1 @ (k6_partfun1 @ X18) @ 
% 18.80/19.01          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 18.80/19.01      inference('demod', [status(thm)], ['21', '22'])).
% 18.80/19.01  thf('24', plain,
% 18.80/19.01      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 18.80/19.01         = (k6_partfun1 @ sk_A))),
% 18.80/19.01      inference('demod', [status(thm)], ['20', '23'])).
% 18.80/19.01  thf('25', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 18.80/19.01      inference('demod', [status(thm)], ['6', '7', '24'])).
% 18.80/19.01  thf(t64_funct_1, axiom,
% 18.80/19.01    (![A:$i]:
% 18.80/19.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 18.80/19.01       ( ![B:$i]:
% 18.80/19.01         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 18.80/19.01           ( ( ( v2_funct_1 @ A ) & 
% 18.80/19.01               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 18.80/19.01               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 18.80/19.01             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 18.80/19.01  thf('26', plain,
% 18.80/19.01      (![X3 : $i, X4 : $i]:
% 18.80/19.01         (~ (v1_relat_1 @ X3)
% 18.80/19.01          | ~ (v1_funct_1 @ X3)
% 18.80/19.01          | ((X3) = (k2_funct_1 @ X4))
% 18.80/19.01          | ((k5_relat_1 @ X3 @ X4) != (k6_relat_1 @ (k2_relat_1 @ X4)))
% 18.80/19.01          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 18.80/19.01          | ~ (v2_funct_1 @ X4)
% 18.80/19.01          | ~ (v1_funct_1 @ X4)
% 18.80/19.01          | ~ (v1_relat_1 @ X4))),
% 18.80/19.01      inference('cnf', [status(esa)], [t64_funct_1])).
% 18.80/19.01  thf('27', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 18.80/19.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 18.80/19.01  thf('28', plain,
% 18.80/19.01      (![X3 : $i, X4 : $i]:
% 18.80/19.01         (~ (v1_relat_1 @ X3)
% 18.80/19.01          | ~ (v1_funct_1 @ X3)
% 18.80/19.01          | ((X3) = (k2_funct_1 @ X4))
% 18.80/19.01          | ((k5_relat_1 @ X3 @ X4) != (k6_partfun1 @ (k2_relat_1 @ X4)))
% 18.80/19.01          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 18.80/19.01          | ~ (v2_funct_1 @ X4)
% 18.80/19.01          | ~ (v1_funct_1 @ X4)
% 18.80/19.01          | ~ (v1_relat_1 @ X4))),
% 18.80/19.01      inference('demod', [status(thm)], ['26', '27'])).
% 18.80/19.01  thf('29', plain,
% 18.80/19.01      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 18.80/19.01        | ~ (v1_relat_1 @ sk_D)
% 18.80/19.01        | ~ (v1_funct_1 @ sk_D)
% 18.80/19.01        | ~ (v2_funct_1 @ sk_D)
% 18.80/19.01        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 18.80/19.01        | ((sk_C) = (k2_funct_1 @ sk_D))
% 18.80/19.01        | ~ (v1_funct_1 @ sk_C)
% 18.80/19.01        | ~ (v1_relat_1 @ sk_C))),
% 18.80/19.01      inference('sup-', [status(thm)], ['25', '28'])).
% 18.80/19.01  thf('30', plain,
% 18.80/19.01      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 18.80/19.01         = (k6_partfun1 @ sk_A))),
% 18.80/19.01      inference('demod', [status(thm)], ['20', '23'])).
% 18.80/19.01  thf('31', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf(t24_funct_2, axiom,
% 18.80/19.01    (![A:$i,B:$i,C:$i]:
% 18.80/19.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 18.80/19.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.80/19.01       ( ![D:$i]:
% 18.80/19.01         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 18.80/19.01             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 18.80/19.01           ( ( r2_relset_1 @
% 18.80/19.01               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 18.80/19.01               ( k6_partfun1 @ B ) ) =>
% 18.80/19.01             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 18.80/19.01  thf('32', plain,
% 18.80/19.01      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 18.80/19.01         (~ (v1_funct_1 @ X40)
% 18.80/19.01          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 18.80/19.01          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 18.80/19.01          | ~ (r2_relset_1 @ X41 @ X41 @ 
% 18.80/19.01               (k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43) @ 
% 18.80/19.01               (k6_partfun1 @ X41))
% 18.80/19.01          | ((k2_relset_1 @ X42 @ X41 @ X43) = (X41))
% 18.80/19.01          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 18.80/19.01          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 18.80/19.01          | ~ (v1_funct_1 @ X43))),
% 18.80/19.01      inference('cnf', [status(esa)], [t24_funct_2])).
% 18.80/19.01  thf('33', plain,
% 18.80/19.01      (![X0 : $i]:
% 18.80/19.01         (~ (v1_funct_1 @ X0)
% 18.80/19.01          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 18.80/19.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 18.80/19.01          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 18.80/19.01          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 18.80/19.01               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 18.80/19.01               (k6_partfun1 @ sk_A))
% 18.80/19.01          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 18.80/19.01          | ~ (v1_funct_1 @ sk_C))),
% 18.80/19.01      inference('sup-', [status(thm)], ['31', '32'])).
% 18.80/19.01  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('36', plain,
% 18.80/19.01      (![X0 : $i]:
% 18.80/19.01         (~ (v1_funct_1 @ X0)
% 18.80/19.01          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 18.80/19.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 18.80/19.01          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 18.80/19.01          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 18.80/19.01               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 18.80/19.01               (k6_partfun1 @ sk_A)))),
% 18.80/19.01      inference('demod', [status(thm)], ['33', '34', '35'])).
% 18.80/19.01  thf('37', plain,
% 18.80/19.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 18.80/19.01           (k6_partfun1 @ sk_A))
% 18.80/19.01        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 18.80/19.01        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 18.80/19.01        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 18.80/19.01        | ~ (v1_funct_1 @ sk_D))),
% 18.80/19.01      inference('sup-', [status(thm)], ['30', '36'])).
% 18.80/19.01  thf('38', plain,
% 18.80/19.01      (![X18 : $i]:
% 18.80/19.01         (m1_subset_1 @ (k6_partfun1 @ X18) @ 
% 18.80/19.01          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 18.80/19.01      inference('demod', [status(thm)], ['21', '22'])).
% 18.80/19.01  thf('39', plain,
% 18.80/19.01      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 18.80/19.01         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 18.80/19.01          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 18.80/19.01          | (r2_relset_1 @ X15 @ X16 @ X14 @ X17)
% 18.80/19.01          | ((X14) != (X17)))),
% 18.80/19.01      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 18.80/19.01  thf('40', plain,
% 18.80/19.01      (![X15 : $i, X16 : $i, X17 : $i]:
% 18.80/19.01         ((r2_relset_1 @ X15 @ X16 @ X17 @ X17)
% 18.80/19.01          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 18.80/19.01      inference('simplify', [status(thm)], ['39'])).
% 18.80/19.01  thf('41', plain,
% 18.80/19.01      (![X0 : $i]:
% 18.80/19.01         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 18.80/19.01      inference('sup-', [status(thm)], ['38', '40'])).
% 18.80/19.01  thf('42', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf(redefinition_k2_relset_1, axiom,
% 18.80/19.01    (![A:$i,B:$i,C:$i]:
% 18.80/19.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.80/19.01       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 18.80/19.01  thf('43', plain,
% 18.80/19.01      (![X11 : $i, X12 : $i, X13 : $i]:
% 18.80/19.01         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 18.80/19.01          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 18.80/19.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 18.80/19.01  thf('44', plain,
% 18.80/19.01      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 18.80/19.01      inference('sup-', [status(thm)], ['42', '43'])).
% 18.80/19.01  thf('45', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 18.80/19.01      inference('demod', [status(thm)], ['37', '41', '44', '45', '46', '47'])).
% 18.80/19.01  thf('49', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf(cc1_relset_1, axiom,
% 18.80/19.01    (![A:$i,B:$i,C:$i]:
% 18.80/19.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.80/19.01       ( v1_relat_1 @ C ) ))).
% 18.80/19.01  thf('50', plain,
% 18.80/19.01      (![X5 : $i, X6 : $i, X7 : $i]:
% 18.80/19.01         ((v1_relat_1 @ X5)
% 18.80/19.01          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 18.80/19.01      inference('cnf', [status(esa)], [cc1_relset_1])).
% 18.80/19.01  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 18.80/19.01      inference('sup-', [status(thm)], ['49', '50'])).
% 18.80/19.01  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('53', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('54', plain,
% 18.80/19.01      (![X11 : $i, X12 : $i, X13 : $i]:
% 18.80/19.01         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 18.80/19.01          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 18.80/19.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 18.80/19.01  thf('55', plain,
% 18.80/19.01      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 18.80/19.01      inference('sup-', [status(thm)], ['53', '54'])).
% 18.80/19.01  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('57', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 18.80/19.01      inference('sup+', [status(thm)], ['55', '56'])).
% 18.80/19.01  thf('58', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf(d1_funct_2, axiom,
% 18.80/19.01    (![A:$i,B:$i,C:$i]:
% 18.80/19.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.80/19.01       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 18.80/19.01           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 18.80/19.01             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 18.80/19.01         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 18.80/19.01           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 18.80/19.01             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 18.80/19.01  thf(zf_stmt_1, axiom,
% 18.80/19.01    (![C:$i,B:$i,A:$i]:
% 18.80/19.01     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 18.80/19.01       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 18.80/19.01  thf('59', plain,
% 18.80/19.01      (![X21 : $i, X22 : $i, X23 : $i]:
% 18.80/19.01         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 18.80/19.01          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 18.80/19.01          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 18.80/19.01  thf('60', plain,
% 18.80/19.01      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 18.80/19.01        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 18.80/19.01      inference('sup-', [status(thm)], ['58', '59'])).
% 18.80/19.01  thf(zf_stmt_2, axiom,
% 18.80/19.01    (![B:$i,A:$i]:
% 18.80/19.01     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 18.80/19.01       ( zip_tseitin_0 @ B @ A ) ))).
% 18.80/19.01  thf('61', plain,
% 18.80/19.01      (![X19 : $i, X20 : $i]:
% 18.80/19.01         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_2])).
% 18.80/19.01  thf('62', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 18.80/19.01  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 18.80/19.01  thf(zf_stmt_5, axiom,
% 18.80/19.01    (![A:$i,B:$i,C:$i]:
% 18.80/19.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.80/19.01       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 18.80/19.01         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 18.80/19.01           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 18.80/19.01             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 18.80/19.01  thf('63', plain,
% 18.80/19.01      (![X24 : $i, X25 : $i, X26 : $i]:
% 18.80/19.01         (~ (zip_tseitin_0 @ X24 @ X25)
% 18.80/19.01          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 18.80/19.01          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 18.80/19.01  thf('64', plain,
% 18.80/19.01      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 18.80/19.01      inference('sup-', [status(thm)], ['62', '63'])).
% 18.80/19.01  thf('65', plain,
% 18.80/19.01      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 18.80/19.01      inference('sup-', [status(thm)], ['61', '64'])).
% 18.80/19.01  thf('66', plain, (((sk_A) != (k1_xboole_0))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('67', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 18.80/19.01      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 18.80/19.01  thf('68', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf(redefinition_k1_relset_1, axiom,
% 18.80/19.01    (![A:$i,B:$i,C:$i]:
% 18.80/19.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.80/19.01       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 18.80/19.01  thf('69', plain,
% 18.80/19.01      (![X8 : $i, X9 : $i, X10 : $i]:
% 18.80/19.01         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 18.80/19.01          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 18.80/19.01      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 18.80/19.01  thf('70', plain,
% 18.80/19.01      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 18.80/19.01      inference('sup-', [status(thm)], ['68', '69'])).
% 18.80/19.01  thf('71', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 18.80/19.01      inference('demod', [status(thm)], ['60', '67', '70'])).
% 18.80/19.01  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('73', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('74', plain,
% 18.80/19.01      (![X5 : $i, X6 : $i, X7 : $i]:
% 18.80/19.01         ((v1_relat_1 @ X5)
% 18.80/19.01          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 18.80/19.01      inference('cnf', [status(esa)], [cc1_relset_1])).
% 18.80/19.01  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 18.80/19.01      inference('sup-', [status(thm)], ['73', '74'])).
% 18.80/19.01  thf('76', plain,
% 18.80/19.01      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 18.80/19.01        | ~ (v2_funct_1 @ sk_D)
% 18.80/19.01        | ((sk_B) != (sk_B))
% 18.80/19.01        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 18.80/19.01      inference('demod', [status(thm)],
% 18.80/19.01                ['29', '48', '51', '52', '57', '71', '72', '75'])).
% 18.80/19.01  thf('77', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 18.80/19.01      inference('simplify', [status(thm)], ['76'])).
% 18.80/19.01  thf('78', plain,
% 18.80/19.01      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 18.80/19.01         = (k6_partfun1 @ sk_A))),
% 18.80/19.01      inference('demod', [status(thm)], ['20', '23'])).
% 18.80/19.01  thf('79', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf(t30_funct_2, axiom,
% 18.80/19.01    (![A:$i,B:$i,C:$i,D:$i]:
% 18.80/19.01     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 18.80/19.01         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 18.80/19.01       ( ![E:$i]:
% 18.80/19.01         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 18.80/19.01             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 18.80/19.01           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 18.80/19.01               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 18.80/19.01             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 18.80/19.01               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 18.80/19.01  thf(zf_stmt_6, type, zip_tseitin_3 : $i > $i > $o).
% 18.80/19.01  thf(zf_stmt_7, axiom,
% 18.80/19.01    (![C:$i,B:$i]:
% 18.80/19.01     ( ( zip_tseitin_3 @ C @ B ) =>
% 18.80/19.01       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 18.80/19.01  thf(zf_stmt_8, type, zip_tseitin_2 : $i > $i > $o).
% 18.80/19.01  thf(zf_stmt_9, axiom,
% 18.80/19.01    (![E:$i,D:$i]:
% 18.80/19.01     ( ( zip_tseitin_2 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 18.80/19.01  thf(zf_stmt_10, axiom,
% 18.80/19.01    (![A:$i,B:$i,C:$i,D:$i]:
% 18.80/19.01     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 18.80/19.01         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.80/19.01       ( ![E:$i]:
% 18.80/19.01         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 18.80/19.01             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 18.80/19.01           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 18.80/19.01               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 18.80/19.01             ( ( zip_tseitin_3 @ C @ B ) | ( zip_tseitin_2 @ E @ D ) ) ) ) ) ))).
% 18.80/19.01  thf('80', plain,
% 18.80/19.01      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 18.80/19.01         (~ (v1_funct_1 @ X48)
% 18.80/19.01          | ~ (v1_funct_2 @ X48 @ X49 @ X50)
% 18.80/19.01          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 18.80/19.01          | (zip_tseitin_2 @ X48 @ X51)
% 18.80/19.01          | ~ (v2_funct_1 @ (k1_partfun1 @ X52 @ X49 @ X49 @ X50 @ X51 @ X48))
% 18.80/19.01          | (zip_tseitin_3 @ X50 @ X49)
% 18.80/19.01          | ((k2_relset_1 @ X52 @ X49 @ X51) != (X49))
% 18.80/19.01          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X49)))
% 18.80/19.01          | ~ (v1_funct_2 @ X51 @ X52 @ X49)
% 18.80/19.01          | ~ (v1_funct_1 @ X51))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_10])).
% 18.80/19.01  thf('81', plain,
% 18.80/19.01      (![X0 : $i, X1 : $i]:
% 18.80/19.01         (~ (v1_funct_1 @ X0)
% 18.80/19.01          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 18.80/19.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 18.80/19.01          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 18.80/19.01          | (zip_tseitin_3 @ sk_A @ sk_B)
% 18.80/19.01          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 18.80/19.01          | (zip_tseitin_2 @ sk_D @ X0)
% 18.80/19.01          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 18.80/19.01          | ~ (v1_funct_1 @ sk_D))),
% 18.80/19.01      inference('sup-', [status(thm)], ['79', '80'])).
% 18.80/19.01  thf('82', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('83', plain, ((v1_funct_1 @ sk_D)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('84', plain,
% 18.80/19.01      (![X0 : $i, X1 : $i]:
% 18.80/19.01         (~ (v1_funct_1 @ X0)
% 18.80/19.01          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 18.80/19.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 18.80/19.01          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 18.80/19.01          | (zip_tseitin_3 @ sk_A @ sk_B)
% 18.80/19.01          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 18.80/19.01          | (zip_tseitin_2 @ sk_D @ X0))),
% 18.80/19.01      inference('demod', [status(thm)], ['81', '82', '83'])).
% 18.80/19.01  thf('85', plain,
% 18.80/19.01      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 18.80/19.01        | (zip_tseitin_2 @ sk_D @ sk_C)
% 18.80/19.01        | (zip_tseitin_3 @ sk_A @ sk_B)
% 18.80/19.01        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 18.80/19.01        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 18.80/19.01        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 18.80/19.01        | ~ (v1_funct_1 @ sk_C))),
% 18.80/19.01      inference('sup-', [status(thm)], ['78', '84'])).
% 18.80/19.01  thf(fc4_funct_1, axiom,
% 18.80/19.01    (![A:$i]:
% 18.80/19.01     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 18.80/19.01       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 18.80/19.01  thf('86', plain, (![X1 : $i]: (v2_funct_1 @ (k6_relat_1 @ X1))),
% 18.80/19.01      inference('cnf', [status(esa)], [fc4_funct_1])).
% 18.80/19.01  thf('87', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 18.80/19.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 18.80/19.01  thf('88', plain, (![X1 : $i]: (v2_funct_1 @ (k6_partfun1 @ X1))),
% 18.80/19.01      inference('demod', [status(thm)], ['86', '87'])).
% 18.80/19.01  thf('89', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('90', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('91', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('93', plain,
% 18.80/19.01      (((zip_tseitin_2 @ sk_D @ sk_C)
% 18.80/19.01        | (zip_tseitin_3 @ sk_A @ sk_B)
% 18.80/19.01        | ((sk_B) != (sk_B)))),
% 18.80/19.01      inference('demod', [status(thm)], ['85', '88', '89', '90', '91', '92'])).
% 18.80/19.01  thf('94', plain,
% 18.80/19.01      (((zip_tseitin_3 @ sk_A @ sk_B) | (zip_tseitin_2 @ sk_D @ sk_C))),
% 18.80/19.01      inference('simplify', [status(thm)], ['93'])).
% 18.80/19.01  thf('95', plain,
% 18.80/19.01      (![X46 : $i, X47 : $i]:
% 18.80/19.01         (((X46) = (k1_xboole_0)) | ~ (zip_tseitin_3 @ X46 @ X47))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_7])).
% 18.80/19.01  thf('96', plain,
% 18.80/19.01      (((zip_tseitin_2 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 18.80/19.01      inference('sup-', [status(thm)], ['94', '95'])).
% 18.80/19.01  thf('97', plain, (((sk_A) != (k1_xboole_0))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('98', plain, ((zip_tseitin_2 @ sk_D @ sk_C)),
% 18.80/19.01      inference('simplify_reflect-', [status(thm)], ['96', '97'])).
% 18.80/19.01  thf('99', plain,
% 18.80/19.01      (![X44 : $i, X45 : $i]:
% 18.80/19.01         ((v2_funct_1 @ X45) | ~ (zip_tseitin_2 @ X45 @ X44))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_9])).
% 18.80/19.01  thf('100', plain, ((v2_funct_1 @ sk_D)),
% 18.80/19.01      inference('sup-', [status(thm)], ['98', '99'])).
% 18.80/19.01  thf('101', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 18.80/19.01      inference('demod', [status(thm)], ['77', '100'])).
% 18.80/19.01  thf(t61_funct_1, axiom,
% 18.80/19.01    (![A:$i]:
% 18.80/19.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 18.80/19.01       ( ( v2_funct_1 @ A ) =>
% 18.80/19.01         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 18.80/19.01             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 18.80/19.01           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 18.80/19.01             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 18.80/19.01  thf('102', plain,
% 18.80/19.01      (![X2 : $i]:
% 18.80/19.01         (~ (v2_funct_1 @ X2)
% 18.80/19.01          | ((k5_relat_1 @ X2 @ (k2_funct_1 @ X2))
% 18.80/19.01              = (k6_relat_1 @ (k1_relat_1 @ X2)))
% 18.80/19.01          | ~ (v1_funct_1 @ X2)
% 18.80/19.01          | ~ (v1_relat_1 @ X2))),
% 18.80/19.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 18.80/19.01  thf('103', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 18.80/19.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 18.80/19.01  thf('104', plain,
% 18.80/19.01      (![X2 : $i]:
% 18.80/19.01         (~ (v2_funct_1 @ X2)
% 18.80/19.01          | ((k5_relat_1 @ X2 @ (k2_funct_1 @ X2))
% 18.80/19.01              = (k6_partfun1 @ (k1_relat_1 @ X2)))
% 18.80/19.01          | ~ (v1_funct_1 @ X2)
% 18.80/19.01          | ~ (v1_relat_1 @ X2))),
% 18.80/19.01      inference('demod', [status(thm)], ['102', '103'])).
% 18.80/19.01  thf('105', plain,
% 18.80/19.01      (![X3 : $i, X4 : $i]:
% 18.80/19.01         (~ (v1_relat_1 @ X3)
% 18.80/19.01          | ~ (v1_funct_1 @ X3)
% 18.80/19.01          | ((X3) = (k2_funct_1 @ X4))
% 18.80/19.01          | ((k5_relat_1 @ X3 @ X4) != (k6_partfun1 @ (k2_relat_1 @ X4)))
% 18.80/19.01          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 18.80/19.01          | ~ (v2_funct_1 @ X4)
% 18.80/19.01          | ~ (v1_funct_1 @ X4)
% 18.80/19.01          | ~ (v1_relat_1 @ X4))),
% 18.80/19.01      inference('demod', [status(thm)], ['26', '27'])).
% 18.80/19.01  thf('106', plain,
% 18.80/19.01      (![X0 : $i]:
% 18.80/19.01         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 18.80/19.01            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 18.80/19.01          | ~ (v1_relat_1 @ X0)
% 18.80/19.01          | ~ (v1_funct_1 @ X0)
% 18.80/19.01          | ~ (v2_funct_1 @ X0)
% 18.80/19.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 18.80/19.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 18.80/19.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 18.80/19.01          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 18.80/19.01          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 18.80/19.01          | ~ (v1_funct_1 @ X0)
% 18.80/19.01          | ~ (v1_relat_1 @ X0))),
% 18.80/19.01      inference('sup-', [status(thm)], ['104', '105'])).
% 18.80/19.01  thf('107', plain,
% 18.80/19.01      (![X0 : $i]:
% 18.80/19.01         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 18.80/19.01          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 18.80/19.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 18.80/19.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 18.80/19.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 18.80/19.01          | ~ (v2_funct_1 @ X0)
% 18.80/19.01          | ~ (v1_funct_1 @ X0)
% 18.80/19.01          | ~ (v1_relat_1 @ X0)
% 18.80/19.01          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 18.80/19.01              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 18.80/19.01      inference('simplify', [status(thm)], ['106'])).
% 18.80/19.01  thf('108', plain,
% 18.80/19.01      ((((k6_partfun1 @ (k1_relat_1 @ sk_D))
% 18.80/19.01          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 18.80/19.01        | ~ (v1_relat_1 @ sk_D)
% 18.80/19.01        | ~ (v1_funct_1 @ sk_D)
% 18.80/19.01        | ~ (v2_funct_1 @ sk_D)
% 18.80/19.01        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 18.80/19.01        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 18.80/19.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 18.80/19.01        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 18.80/19.01        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 18.80/19.01      inference('sup-', [status(thm)], ['101', '107'])).
% 18.80/19.01  thf('109', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 18.80/19.01      inference('demod', [status(thm)], ['60', '67', '70'])).
% 18.80/19.01  thf('110', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 18.80/19.01      inference('sup+', [status(thm)], ['55', '56'])).
% 18.80/19.01  thf('111', plain, ((v1_relat_1 @ sk_D)),
% 18.80/19.01      inference('sup-', [status(thm)], ['49', '50'])).
% 18.80/19.01  thf('112', plain, ((v1_funct_1 @ sk_D)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('113', plain, ((v2_funct_1 @ sk_D)),
% 18.80/19.01      inference('sup-', [status(thm)], ['98', '99'])).
% 18.80/19.01  thf('114', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 18.80/19.01      inference('demod', [status(thm)], ['77', '100'])).
% 18.80/19.01  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 18.80/19.01      inference('sup-', [status(thm)], ['73', '74'])).
% 18.80/19.01  thf('116', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 18.80/19.01      inference('demod', [status(thm)], ['77', '100'])).
% 18.80/19.01  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('118', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 18.80/19.01      inference('demod', [status(thm)], ['77', '100'])).
% 18.80/19.01  thf('119', plain, ((v2_funct_1 @ sk_C)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('120', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 18.80/19.01      inference('demod', [status(thm)], ['37', '41', '44', '45', '46', '47'])).
% 18.80/19.01  thf('121', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 18.80/19.01      inference('demod', [status(thm)], ['77', '100'])).
% 18.80/19.01  thf('122', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('123', plain,
% 18.80/19.01      (![X21 : $i, X22 : $i, X23 : $i]:
% 18.80/19.01         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 18.80/19.01          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 18.80/19.01          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 18.80/19.01  thf('124', plain,
% 18.80/19.01      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 18.80/19.01        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 18.80/19.01      inference('sup-', [status(thm)], ['122', '123'])).
% 18.80/19.01  thf('125', plain,
% 18.80/19.01      (![X19 : $i, X20 : $i]:
% 18.80/19.01         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_2])).
% 18.80/19.01  thf('126', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('127', plain,
% 18.80/19.01      (![X24 : $i, X25 : $i, X26 : $i]:
% 18.80/19.01         (~ (zip_tseitin_0 @ X24 @ X25)
% 18.80/19.01          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 18.80/19.01          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 18.80/19.01  thf('128', plain,
% 18.80/19.01      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 18.80/19.01      inference('sup-', [status(thm)], ['126', '127'])).
% 18.80/19.01  thf('129', plain,
% 18.80/19.01      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 18.80/19.01      inference('sup-', [status(thm)], ['125', '128'])).
% 18.80/19.01  thf('130', plain, (((sk_B) != (k1_xboole_0))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('131', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 18.80/19.01      inference('simplify_reflect-', [status(thm)], ['129', '130'])).
% 18.80/19.01  thf('132', plain,
% 18.80/19.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('133', plain,
% 18.80/19.01      (![X8 : $i, X9 : $i, X10 : $i]:
% 18.80/19.01         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 18.80/19.01          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 18.80/19.01      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 18.80/19.01  thf('134', plain,
% 18.80/19.01      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 18.80/19.01      inference('sup-', [status(thm)], ['132', '133'])).
% 18.80/19.01  thf('135', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 18.80/19.01      inference('demod', [status(thm)], ['124', '131', '134'])).
% 18.80/19.01  thf('136', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 18.80/19.01      inference('demod', [status(thm)], ['77', '100'])).
% 18.80/19.01  thf('137', plain,
% 18.80/19.01      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 18.80/19.01        | ((sk_A) != (sk_A))
% 18.80/19.01        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 18.80/19.01      inference('demod', [status(thm)],
% 18.80/19.01                ['108', '109', '110', '111', '112', '113', '114', '115', 
% 18.80/19.01                 '116', '117', '118', '119', '120', '121', '135', '136'])).
% 18.80/19.01  thf('138', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 18.80/19.01      inference('simplify', [status(thm)], ['137'])).
% 18.80/19.01  thf('139', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 18.80/19.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.80/19.01  thf('140', plain, ($false),
% 18.80/19.01      inference('simplify_reflect-', [status(thm)], ['138', '139'])).
% 18.80/19.01  
% 18.80/19.01  % SZS output end Refutation
% 18.80/19.01  
% 18.80/19.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
