%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7fKoP9QI7H

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:02 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 452 expanded)
%              Number of leaves         :   44 ( 154 expanded)
%              Depth                    :   17
%              Number of atoms          : 1379 (10838 expanded)
%              Number of equality atoms :   88 ( 737 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
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
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
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
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44 ) @ ( k6_partfun1 @ X42 ) )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
        = X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
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
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('39',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('80',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('81',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('82',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('83',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X2 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('85',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('87',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['60','67','70'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['73','74'])).

thf('90',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['80','83','84','85','86','87','88','89'])).

thf('91',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','91'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('93',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('94',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('96',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['90'])).

thf('98',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['98','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7fKoP9QI7H
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.22/2.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.22/2.43  % Solved by: fo/fo7.sh
% 2.22/2.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.22/2.43  % done 477 iterations in 1.980s
% 2.22/2.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.22/2.43  % SZS output start Refutation
% 2.22/2.43  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.22/2.43  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.22/2.43  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.22/2.43  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.22/2.43  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.22/2.43  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.22/2.43  thf(sk_B_type, type, sk_B: $i).
% 2.22/2.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.22/2.43  thf(sk_D_type, type, sk_D: $i).
% 2.22/2.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.22/2.43  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.22/2.43  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.22/2.43  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.22/2.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.22/2.43  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.22/2.43  thf(sk_A_type, type, sk_A: $i).
% 2.22/2.43  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.22/2.43  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.22/2.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.22/2.43  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.22/2.43  thf(sk_C_type, type, sk_C: $i).
% 2.22/2.43  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.22/2.43  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.22/2.43  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.22/2.43  thf(t36_funct_2, conjecture,
% 2.22/2.43    (![A:$i,B:$i,C:$i]:
% 2.22/2.43     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.22/2.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.43       ( ![D:$i]:
% 2.22/2.43         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.22/2.43             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.22/2.43           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.22/2.43               ( r2_relset_1 @
% 2.22/2.43                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.22/2.43                 ( k6_partfun1 @ A ) ) & 
% 2.22/2.43               ( v2_funct_1 @ C ) ) =>
% 2.22/2.43             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.22/2.43               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.22/2.43  thf(zf_stmt_0, negated_conjecture,
% 2.22/2.43    (~( ![A:$i,B:$i,C:$i]:
% 2.22/2.43        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.22/2.43            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.43          ( ![D:$i]:
% 2.22/2.43            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.22/2.43                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.22/2.43              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.22/2.43                  ( r2_relset_1 @
% 2.22/2.43                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.22/2.43                    ( k6_partfun1 @ A ) ) & 
% 2.22/2.43                  ( v2_funct_1 @ C ) ) =>
% 2.22/2.43                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.22/2.43                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.22/2.43    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.22/2.43  thf('0', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('1', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf(redefinition_k1_partfun1, axiom,
% 2.22/2.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.22/2.43     ( ( ( v1_funct_1 @ E ) & 
% 2.22/2.43         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.22/2.43         ( v1_funct_1 @ F ) & 
% 2.22/2.43         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.22/2.43       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.22/2.43  thf('2', plain,
% 2.22/2.43      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 2.22/2.43         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 2.22/2.43          | ~ (v1_funct_1 @ X34)
% 2.22/2.43          | ~ (v1_funct_1 @ X37)
% 2.22/2.43          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.22/2.43          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 2.22/2.43              = (k5_relat_1 @ X34 @ X37)))),
% 2.22/2.43      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.22/2.43  thf('3', plain,
% 2.22/2.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.43         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.22/2.43            = (k5_relat_1 @ sk_C @ X0))
% 2.22/2.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.22/2.43          | ~ (v1_funct_1 @ X0)
% 2.22/2.43          | ~ (v1_funct_1 @ sk_C))),
% 2.22/2.43      inference('sup-', [status(thm)], ['1', '2'])).
% 2.22/2.43  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('5', plain,
% 2.22/2.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.43         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.22/2.43            = (k5_relat_1 @ sk_C @ X0))
% 2.22/2.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.22/2.43          | ~ (v1_funct_1 @ X0))),
% 2.22/2.43      inference('demod', [status(thm)], ['3', '4'])).
% 2.22/2.43  thf('6', plain,
% 2.22/2.43      ((~ (v1_funct_1 @ sk_D)
% 2.22/2.43        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.22/2.43            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.22/2.43      inference('sup-', [status(thm)], ['0', '5'])).
% 2.22/2.43  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('8', plain,
% 2.22/2.43      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.22/2.43        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.22/2.43        (k6_partfun1 @ sk_A))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('9', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('10', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf(dt_k1_partfun1, axiom,
% 2.22/2.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.22/2.43     ( ( ( v1_funct_1 @ E ) & 
% 2.22/2.43         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.22/2.43         ( v1_funct_1 @ F ) & 
% 2.22/2.43         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.22/2.43       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.22/2.43         ( m1_subset_1 @
% 2.22/2.43           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.22/2.43           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.22/2.43  thf('11', plain,
% 2.22/2.43      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.22/2.43         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.22/2.43          | ~ (v1_funct_1 @ X28)
% 2.22/2.43          | ~ (v1_funct_1 @ X31)
% 2.22/2.43          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 2.22/2.43          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 2.22/2.43             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 2.22/2.43      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.22/2.43  thf('12', plain,
% 2.22/2.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.43         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.22/2.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.22/2.43          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.22/2.43          | ~ (v1_funct_1 @ X1)
% 2.22/2.43          | ~ (v1_funct_1 @ sk_C))),
% 2.22/2.43      inference('sup-', [status(thm)], ['10', '11'])).
% 2.22/2.43  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('14', plain,
% 2.22/2.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.43         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.22/2.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.22/2.43          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.22/2.43          | ~ (v1_funct_1 @ X1))),
% 2.22/2.43      inference('demod', [status(thm)], ['12', '13'])).
% 2.22/2.43  thf('15', plain,
% 2.22/2.43      ((~ (v1_funct_1 @ sk_D)
% 2.22/2.43        | (m1_subset_1 @ 
% 2.22/2.43           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.22/2.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.22/2.43      inference('sup-', [status(thm)], ['9', '14'])).
% 2.22/2.43  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('17', plain,
% 2.22/2.43      ((m1_subset_1 @ 
% 2.22/2.43        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.22/2.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.22/2.43      inference('demod', [status(thm)], ['15', '16'])).
% 2.22/2.43  thf(redefinition_r2_relset_1, axiom,
% 2.22/2.43    (![A:$i,B:$i,C:$i,D:$i]:
% 2.22/2.43     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.22/2.43         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.43       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.22/2.43  thf('18', plain,
% 2.22/2.43      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 2.22/2.43         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 2.22/2.43          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 2.22/2.43          | ((X15) = (X18))
% 2.22/2.43          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 2.22/2.43      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.22/2.43  thf('19', plain,
% 2.22/2.43      (![X0 : $i]:
% 2.22/2.43         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.22/2.43             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.22/2.43          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.22/2.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.22/2.43      inference('sup-', [status(thm)], ['17', '18'])).
% 2.22/2.43  thf('20', plain,
% 2.22/2.43      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.22/2.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.22/2.43        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.22/2.43            = (k6_partfun1 @ sk_A)))),
% 2.22/2.43      inference('sup-', [status(thm)], ['8', '19'])).
% 2.22/2.43  thf(t29_relset_1, axiom,
% 2.22/2.43    (![A:$i]:
% 2.22/2.43     ( m1_subset_1 @
% 2.22/2.43       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.22/2.43  thf('21', plain,
% 2.22/2.43      (![X19 : $i]:
% 2.22/2.43         (m1_subset_1 @ (k6_relat_1 @ X19) @ 
% 2.22/2.43          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 2.22/2.43      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.22/2.43  thf(redefinition_k6_partfun1, axiom,
% 2.22/2.43    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.22/2.43  thf('22', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 2.22/2.43      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.22/2.43  thf('23', plain,
% 2.22/2.43      (![X19 : $i]:
% 2.22/2.43         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 2.22/2.43          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 2.22/2.43      inference('demod', [status(thm)], ['21', '22'])).
% 2.22/2.43  thf('24', plain,
% 2.22/2.43      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.22/2.43         = (k6_partfun1 @ sk_A))),
% 2.22/2.43      inference('demod', [status(thm)], ['20', '23'])).
% 2.22/2.43  thf('25', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 2.22/2.43      inference('demod', [status(thm)], ['6', '7', '24'])).
% 2.22/2.43  thf(t64_funct_1, axiom,
% 2.22/2.43    (![A:$i]:
% 2.22/2.43     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.22/2.43       ( ![B:$i]:
% 2.22/2.43         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.22/2.43           ( ( ( v2_funct_1 @ A ) & 
% 2.22/2.43               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 2.22/2.43               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 2.22/2.43             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.22/2.43  thf('26', plain,
% 2.22/2.43      (![X3 : $i, X4 : $i]:
% 2.22/2.43         (~ (v1_relat_1 @ X3)
% 2.22/2.43          | ~ (v1_funct_1 @ X3)
% 2.22/2.43          | ((X3) = (k2_funct_1 @ X4))
% 2.22/2.43          | ((k5_relat_1 @ X3 @ X4) != (k6_relat_1 @ (k2_relat_1 @ X4)))
% 2.22/2.43          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 2.22/2.43          | ~ (v2_funct_1 @ X4)
% 2.22/2.43          | ~ (v1_funct_1 @ X4)
% 2.22/2.43          | ~ (v1_relat_1 @ X4))),
% 2.22/2.43      inference('cnf', [status(esa)], [t64_funct_1])).
% 2.22/2.43  thf('27', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 2.22/2.43      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.22/2.43  thf('28', plain,
% 2.22/2.43      (![X3 : $i, X4 : $i]:
% 2.22/2.43         (~ (v1_relat_1 @ X3)
% 2.22/2.43          | ~ (v1_funct_1 @ X3)
% 2.22/2.43          | ((X3) = (k2_funct_1 @ X4))
% 2.22/2.43          | ((k5_relat_1 @ X3 @ X4) != (k6_partfun1 @ (k2_relat_1 @ X4)))
% 2.22/2.43          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 2.22/2.43          | ~ (v2_funct_1 @ X4)
% 2.22/2.43          | ~ (v1_funct_1 @ X4)
% 2.22/2.43          | ~ (v1_relat_1 @ X4))),
% 2.22/2.43      inference('demod', [status(thm)], ['26', '27'])).
% 2.22/2.43  thf('29', plain,
% 2.22/2.43      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 2.22/2.43        | ~ (v1_relat_1 @ sk_D)
% 2.22/2.43        | ~ (v1_funct_1 @ sk_D)
% 2.22/2.43        | ~ (v2_funct_1 @ sk_D)
% 2.22/2.43        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 2.22/2.43        | ((sk_C) = (k2_funct_1 @ sk_D))
% 2.22/2.43        | ~ (v1_funct_1 @ sk_C)
% 2.22/2.43        | ~ (v1_relat_1 @ sk_C))),
% 2.22/2.43      inference('sup-', [status(thm)], ['25', '28'])).
% 2.22/2.43  thf('30', plain,
% 2.22/2.43      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.22/2.43         = (k6_partfun1 @ sk_A))),
% 2.22/2.43      inference('demod', [status(thm)], ['20', '23'])).
% 2.22/2.43  thf('31', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf(t24_funct_2, axiom,
% 2.22/2.43    (![A:$i,B:$i,C:$i]:
% 2.22/2.43     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.22/2.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.43       ( ![D:$i]:
% 2.22/2.43         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.22/2.43             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.22/2.43           ( ( r2_relset_1 @
% 2.22/2.43               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.22/2.43               ( k6_partfun1 @ B ) ) =>
% 2.22/2.43             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.22/2.43  thf('32', plain,
% 2.22/2.43      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 2.22/2.43         (~ (v1_funct_1 @ X41)
% 2.22/2.43          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 2.22/2.43          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 2.22/2.43          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 2.22/2.43               (k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44) @ 
% 2.22/2.43               (k6_partfun1 @ X42))
% 2.22/2.43          | ((k2_relset_1 @ X43 @ X42 @ X44) = (X42))
% 2.22/2.43          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 2.22/2.43          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 2.22/2.43          | ~ (v1_funct_1 @ X44))),
% 2.22/2.43      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.22/2.43  thf('33', plain,
% 2.22/2.43      (![X0 : $i]:
% 2.22/2.43         (~ (v1_funct_1 @ X0)
% 2.22/2.43          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.22/2.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.22/2.43          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.22/2.43          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.22/2.43               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.22/2.43               (k6_partfun1 @ sk_A))
% 2.22/2.43          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.22/2.43          | ~ (v1_funct_1 @ sk_C))),
% 2.22/2.43      inference('sup-', [status(thm)], ['31', '32'])).
% 2.22/2.43  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('36', plain,
% 2.22/2.43      (![X0 : $i]:
% 2.22/2.43         (~ (v1_funct_1 @ X0)
% 2.22/2.43          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.22/2.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.22/2.43          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.22/2.43          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.22/2.43               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.22/2.43               (k6_partfun1 @ sk_A)))),
% 2.22/2.43      inference('demod', [status(thm)], ['33', '34', '35'])).
% 2.22/2.43  thf('37', plain,
% 2.22/2.43      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 2.22/2.43           (k6_partfun1 @ sk_A))
% 2.22/2.43        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.22/2.43        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.22/2.43        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.22/2.43        | ~ (v1_funct_1 @ sk_D))),
% 2.22/2.43      inference('sup-', [status(thm)], ['30', '36'])).
% 2.22/2.43  thf('38', plain,
% 2.22/2.43      (![X19 : $i]:
% 2.22/2.43         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 2.22/2.43          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 2.22/2.43      inference('demod', [status(thm)], ['21', '22'])).
% 2.22/2.43  thf('39', plain,
% 2.22/2.43      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 2.22/2.43         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 2.22/2.43          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 2.22/2.43          | (r2_relset_1 @ X16 @ X17 @ X15 @ X18)
% 2.22/2.43          | ((X15) != (X18)))),
% 2.22/2.43      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.22/2.43  thf('40', plain,
% 2.22/2.43      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.22/2.43         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 2.22/2.43          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.22/2.43      inference('simplify', [status(thm)], ['39'])).
% 2.22/2.43  thf('41', plain,
% 2.22/2.43      (![X0 : $i]:
% 2.22/2.43         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 2.22/2.43      inference('sup-', [status(thm)], ['38', '40'])).
% 2.22/2.43  thf('42', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf(redefinition_k2_relset_1, axiom,
% 2.22/2.43    (![A:$i,B:$i,C:$i]:
% 2.22/2.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.43       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.22/2.43  thf('43', plain,
% 2.22/2.43      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.22/2.43         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 2.22/2.43          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.22/2.44      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.22/2.44  thf('44', plain,
% 2.22/2.44      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.22/2.44      inference('sup-', [status(thm)], ['42', '43'])).
% 2.22/2.44  thf('45', plain,
% 2.22/2.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.22/2.44      inference('demod', [status(thm)], ['37', '41', '44', '45', '46', '47'])).
% 2.22/2.44  thf('49', plain,
% 2.22/2.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf(cc1_relset_1, axiom,
% 2.22/2.44    (![A:$i,B:$i,C:$i]:
% 2.22/2.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.44       ( v1_relat_1 @ C ) ))).
% 2.22/2.44  thf('50', plain,
% 2.22/2.44      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.22/2.44         ((v1_relat_1 @ X6)
% 2.22/2.44          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.22/2.44      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.22/2.44  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 2.22/2.44      inference('sup-', [status(thm)], ['49', '50'])).
% 2.22/2.44  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('53', plain,
% 2.22/2.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('54', plain,
% 2.22/2.44      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.22/2.44         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 2.22/2.44          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.22/2.44      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.22/2.44  thf('55', plain,
% 2.22/2.44      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.22/2.44      inference('sup-', [status(thm)], ['53', '54'])).
% 2.22/2.44  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('57', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.22/2.44      inference('sup+', [status(thm)], ['55', '56'])).
% 2.22/2.44  thf('58', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf(d1_funct_2, axiom,
% 2.22/2.44    (![A:$i,B:$i,C:$i]:
% 2.22/2.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.44       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.22/2.44           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.22/2.44             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.22/2.44         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.22/2.44           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.22/2.44             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.22/2.44  thf(zf_stmt_1, axiom,
% 2.22/2.44    (![C:$i,B:$i,A:$i]:
% 2.22/2.44     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.22/2.44       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.22/2.44  thf('59', plain,
% 2.22/2.44      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.22/2.44         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 2.22/2.44          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 2.22/2.44          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.44  thf('60', plain,
% 2.22/2.44      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 2.22/2.44        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 2.22/2.44      inference('sup-', [status(thm)], ['58', '59'])).
% 2.22/2.44  thf(zf_stmt_2, axiom,
% 2.22/2.44    (![B:$i,A:$i]:
% 2.22/2.44     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.22/2.44       ( zip_tseitin_0 @ B @ A ) ))).
% 2.22/2.44  thf('61', plain,
% 2.22/2.44      (![X20 : $i, X21 : $i]:
% 2.22/2.44         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.22/2.44  thf('62', plain,
% 2.22/2.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.22/2.44  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.22/2.44  thf(zf_stmt_5, axiom,
% 2.22/2.44    (![A:$i,B:$i,C:$i]:
% 2.22/2.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.44       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.22/2.44         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.22/2.44           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.22/2.44             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.22/2.44  thf('63', plain,
% 2.22/2.44      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.22/2.44         (~ (zip_tseitin_0 @ X25 @ X26)
% 2.22/2.44          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 2.22/2.44          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.22/2.44  thf('64', plain,
% 2.22/2.44      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 2.22/2.44      inference('sup-', [status(thm)], ['62', '63'])).
% 2.22/2.44  thf('65', plain,
% 2.22/2.44      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 2.22/2.44      inference('sup-', [status(thm)], ['61', '64'])).
% 2.22/2.44  thf('66', plain, (((sk_A) != (k1_xboole_0))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('67', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 2.22/2.44      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 2.22/2.44  thf('68', plain,
% 2.22/2.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf(redefinition_k1_relset_1, axiom,
% 2.22/2.44    (![A:$i,B:$i,C:$i]:
% 2.22/2.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.44       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.22/2.44  thf('69', plain,
% 2.22/2.44      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.22/2.44         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 2.22/2.44          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.22/2.44      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.22/2.44  thf('70', plain,
% 2.22/2.44      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.22/2.44      inference('sup-', [status(thm)], ['68', '69'])).
% 2.22/2.44  thf('71', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.22/2.44      inference('demod', [status(thm)], ['60', '67', '70'])).
% 2.22/2.44  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('73', plain,
% 2.22/2.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('74', plain,
% 2.22/2.44      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.22/2.44         ((v1_relat_1 @ X6)
% 2.22/2.44          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.22/2.44      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.22/2.44  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.44      inference('sup-', [status(thm)], ['73', '74'])).
% 2.22/2.44  thf('76', plain,
% 2.22/2.44      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 2.22/2.44        | ~ (v2_funct_1 @ sk_D)
% 2.22/2.44        | ((sk_B) != (sk_B))
% 2.22/2.44        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 2.22/2.44      inference('demod', [status(thm)],
% 2.22/2.44                ['29', '48', '51', '52', '57', '71', '72', '75'])).
% 2.22/2.44  thf('77', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 2.22/2.44      inference('simplify', [status(thm)], ['76'])).
% 2.22/2.44  thf('78', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 2.22/2.44      inference('demod', [status(thm)], ['6', '7', '24'])).
% 2.22/2.44  thf(t48_funct_1, axiom,
% 2.22/2.44    (![A:$i]:
% 2.22/2.44     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.22/2.44       ( ![B:$i]:
% 2.22/2.44         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.22/2.44           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 2.22/2.44               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 2.22/2.44             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 2.22/2.44  thf('79', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         (~ (v1_relat_1 @ X0)
% 2.22/2.44          | ~ (v1_funct_1 @ X0)
% 2.22/2.44          | (v2_funct_1 @ X1)
% 2.22/2.44          | ((k2_relat_1 @ X0) != (k1_relat_1 @ X1))
% 2.22/2.44          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 2.22/2.44          | ~ (v1_funct_1 @ X1)
% 2.22/2.44          | ~ (v1_relat_1 @ X1))),
% 2.22/2.44      inference('cnf', [status(esa)], [t48_funct_1])).
% 2.22/2.44  thf('80', plain,
% 2.22/2.44      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 2.22/2.44        | ~ (v1_relat_1 @ sk_D)
% 2.22/2.44        | ~ (v1_funct_1 @ sk_D)
% 2.22/2.44        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 2.22/2.44        | (v2_funct_1 @ sk_D)
% 2.22/2.44        | ~ (v1_funct_1 @ sk_C)
% 2.22/2.44        | ~ (v1_relat_1 @ sk_C))),
% 2.22/2.44      inference('sup-', [status(thm)], ['78', '79'])).
% 2.22/2.44  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 2.22/2.44  thf('81', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 2.22/2.44      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.22/2.44  thf('82', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 2.22/2.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.22/2.44  thf('83', plain, (![X2 : $i]: (v2_funct_1 @ (k6_partfun1 @ X2))),
% 2.22/2.44      inference('demod', [status(thm)], ['81', '82'])).
% 2.22/2.44  thf('84', plain, ((v1_relat_1 @ sk_D)),
% 2.22/2.44      inference('sup-', [status(thm)], ['49', '50'])).
% 2.22/2.44  thf('85', plain, ((v1_funct_1 @ sk_D)),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('86', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.22/2.44      inference('sup+', [status(thm)], ['55', '56'])).
% 2.22/2.44  thf('87', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.22/2.44      inference('demod', [status(thm)], ['60', '67', '70'])).
% 2.22/2.44  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.44      inference('sup-', [status(thm)], ['73', '74'])).
% 2.22/2.44  thf('90', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 2.22/2.44      inference('demod', [status(thm)],
% 2.22/2.44                ['80', '83', '84', '85', '86', '87', '88', '89'])).
% 2.22/2.44  thf('91', plain, ((v2_funct_1 @ sk_D)),
% 2.22/2.44      inference('simplify', [status(thm)], ['90'])).
% 2.22/2.44  thf('92', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 2.22/2.44      inference('demod', [status(thm)], ['77', '91'])).
% 2.22/2.44  thf(t65_funct_1, axiom,
% 2.22/2.44    (![A:$i]:
% 2.22/2.44     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.22/2.44       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 2.22/2.44  thf('93', plain,
% 2.22/2.44      (![X5 : $i]:
% 2.22/2.44         (~ (v2_funct_1 @ X5)
% 2.22/2.44          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 2.22/2.44          | ~ (v1_funct_1 @ X5)
% 2.22/2.44          | ~ (v1_relat_1 @ X5))),
% 2.22/2.44      inference('cnf', [status(esa)], [t65_funct_1])).
% 2.22/2.44  thf('94', plain,
% 2.22/2.44      ((((k2_funct_1 @ sk_C) = (sk_D))
% 2.22/2.44        | ~ (v1_relat_1 @ sk_D)
% 2.22/2.44        | ~ (v1_funct_1 @ sk_D)
% 2.22/2.44        | ~ (v2_funct_1 @ sk_D))),
% 2.22/2.44      inference('sup+', [status(thm)], ['92', '93'])).
% 2.22/2.44  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 2.22/2.44      inference('sup-', [status(thm)], ['49', '50'])).
% 2.22/2.44  thf('96', plain, ((v1_funct_1 @ sk_D)),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('97', plain, ((v2_funct_1 @ sk_D)),
% 2.22/2.44      inference('simplify', [status(thm)], ['90'])).
% 2.22/2.44  thf('98', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 2.22/2.44      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 2.22/2.44  thf('99', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('100', plain, ($false),
% 2.22/2.44      inference('simplify_reflect-', [status(thm)], ['98', '99'])).
% 2.22/2.44  
% 2.22/2.44  % SZS output end Refutation
% 2.22/2.44  
% 2.22/2.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
