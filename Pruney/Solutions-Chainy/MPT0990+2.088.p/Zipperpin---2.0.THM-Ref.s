%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ybfNrGWx5p

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:09 EST 2020

% Result     : Theorem 27.52s
% Output     : Refutation 27.52s
% Verified   : 
% Statistics : Number of formulae       :  270 (1080 expanded)
%              Number of leaves         :   47 ( 344 expanded)
%              Depth                    :   24
%              Number of atoms          : 2688 (25103 expanded)
%              Number of equality atoms :  176 (1777 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_partfun1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','5','6','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('24',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39 ) @ ( k6_partfun1 @ X37 ) )
      | ( ( k2_relset_1 @ X38 @ X37 @ X39 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['34','38','39','40','41','42'])).

thf('44',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','43'])).

thf('45',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( zip_tseitin_0 @ X44 @ X47 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X48 @ X45 @ X45 @ X46 @ X47 @ X44 ) )
      | ( zip_tseitin_1 @ X46 @ X45 )
      | ( ( k2_relset_1 @ X48 @ X45 @ X47 )
       != X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X45 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('49',plain,(
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
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['56','57'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('59',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ X6 @ ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('60',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('61',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ X6 @ ( k6_partfun1 @ ( k2_relat_1 @ X6 ) ) )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('64',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['62','65'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('67',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('68',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('69',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('74',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['66','76'])).

thf('78',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['62','65'])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('80',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('81',plain,
    ( sk_C
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

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

thf('82',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('83',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('87',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('88',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('89',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('91',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','89','90'])).

thf('92',plain,
    ( ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_partfun1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('95',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('104',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('105',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('107',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('111',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('123',plain,(
    v1_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    v2_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['112','123'])).

thf('125',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['53','124','125','126','127','128'])).

thf('130',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('132',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v2_funct_1 @ X41 )
      | ~ ( zip_tseitin_0 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('136',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','136'])).

thf('138',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('139',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('141',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('143',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['134','135'])).

thf('146',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['139','140','143','144','145'])).

thf('147',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('148',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
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

thf('151',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['149','154'])).

thf('156',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('158',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('159',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('160',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X50 ) @ X50 )
        = ( k6_partfun1 @ X49 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('162',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['162','163','164','165','166'])).

thf('168',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['159','174'])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('177',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['158','178'])).

thf('180',plain,(
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

thf('181',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('182',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ X6 @ ( k6_partfun1 @ ( k2_relat_1 @ X6 ) ) )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['180','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('187',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['56','57'])).

thf('188',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('189',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('190',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['188','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['187','193'])).

thf('195',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('196',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['194','195','196','197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['186','202'])).

thf('204',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('205',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['203','204','205'])).

thf('207',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['185','206'])).

thf('208',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['194','195','196','197'])).

thf('209',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('210',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('213',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['207','208','209','210','211','212'])).

thf('214',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('215',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['141','142'])).

thf('217',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','215','216'])).

thf('218',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['141','142'])).

thf('219',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['148','217','218'])).

thf('220',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['219','220'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ybfNrGWx5p
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 27.52/27.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 27.52/27.76  % Solved by: fo/fo7.sh
% 27.52/27.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 27.52/27.76  % done 5762 iterations in 27.300s
% 27.52/27.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 27.52/27.76  % SZS output start Refutation
% 27.52/27.76  thf(sk_D_type, type, sk_D: $i).
% 27.52/27.76  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 27.52/27.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 27.52/27.76  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 27.52/27.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 27.52/27.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 27.52/27.76  thf(sk_B_type, type, sk_B: $i).
% 27.52/27.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 27.52/27.76  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 27.52/27.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 27.52/27.76  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 27.52/27.76  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 27.52/27.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 27.52/27.76  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 27.52/27.76  thf(sk_C_type, type, sk_C: $i).
% 27.52/27.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 27.52/27.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 27.52/27.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 27.52/27.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 27.52/27.76  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 27.52/27.76  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 27.52/27.76  thf(sk_A_type, type, sk_A: $i).
% 27.52/27.76  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 27.52/27.76  thf(t36_funct_2, conjecture,
% 27.52/27.76    (![A:$i,B:$i,C:$i]:
% 27.52/27.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 27.52/27.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 27.52/27.76       ( ![D:$i]:
% 27.52/27.76         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 27.52/27.76             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 27.52/27.76           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 27.52/27.76               ( r2_relset_1 @
% 27.52/27.76                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 27.52/27.76                 ( k6_partfun1 @ A ) ) & 
% 27.52/27.76               ( v2_funct_1 @ C ) ) =>
% 27.52/27.76             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 27.52/27.76               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 27.52/27.76  thf(zf_stmt_0, negated_conjecture,
% 27.52/27.76    (~( ![A:$i,B:$i,C:$i]:
% 27.52/27.76        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 27.52/27.76            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 27.52/27.76          ( ![D:$i]:
% 27.52/27.76            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 27.52/27.76                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 27.52/27.76              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 27.52/27.76                  ( r2_relset_1 @
% 27.52/27.76                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 27.52/27.76                    ( k6_partfun1 @ A ) ) & 
% 27.52/27.76                  ( v2_funct_1 @ C ) ) =>
% 27.52/27.76                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 27.52/27.76                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 27.52/27.76    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 27.52/27.76  thf('0', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf(t35_funct_2, axiom,
% 27.52/27.76    (![A:$i,B:$i,C:$i]:
% 27.52/27.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 27.52/27.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 27.52/27.76       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 27.52/27.76         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 27.52/27.76           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 27.52/27.76             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 27.52/27.76  thf('1', plain,
% 27.52/27.76      (![X49 : $i, X50 : $i, X51 : $i]:
% 27.52/27.76         (((X49) = (k1_xboole_0))
% 27.52/27.76          | ~ (v1_funct_1 @ X50)
% 27.52/27.76          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 27.52/27.76          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 27.52/27.76          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_partfun1 @ X51))
% 27.52/27.76          | ~ (v2_funct_1 @ X50)
% 27.52/27.76          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 27.52/27.76      inference('cnf', [status(esa)], [t35_funct_2])).
% 27.52/27.76  thf('2', plain,
% 27.52/27.76      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 27.52/27.76        | ~ (v2_funct_1 @ sk_D)
% 27.52/27.76        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 27.52/27.76        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 27.52/27.76        | ~ (v1_funct_1 @ sk_D)
% 27.52/27.76        | ((sk_A) = (k1_xboole_0)))),
% 27.52/27.76      inference('sup-', [status(thm)], ['0', '1'])).
% 27.52/27.76  thf('3', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf(redefinition_k2_relset_1, axiom,
% 27.52/27.76    (![A:$i,B:$i,C:$i]:
% 27.52/27.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 27.52/27.76       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 27.52/27.76  thf('4', plain,
% 27.52/27.76      (![X15 : $i, X16 : $i, X17 : $i]:
% 27.52/27.76         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 27.52/27.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 27.52/27.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 27.52/27.76  thf('5', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 27.52/27.76      inference('sup-', [status(thm)], ['3', '4'])).
% 27.52/27.76  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('8', plain,
% 27.52/27.76      ((((k2_relat_1 @ sk_D) != (sk_A))
% 27.52/27.76        | ~ (v2_funct_1 @ sk_D)
% 27.52/27.76        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 27.52/27.76        | ((sk_A) = (k1_xboole_0)))),
% 27.52/27.76      inference('demod', [status(thm)], ['2', '5', '6', '7'])).
% 27.52/27.76  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('10', plain,
% 27.52/27.76      ((((k2_relat_1 @ sk_D) != (sk_A))
% 27.52/27.76        | ~ (v2_funct_1 @ sk_D)
% 27.52/27.76        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 27.52/27.76      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 27.52/27.76  thf('11', plain,
% 27.52/27.76      ((r2_relset_1 @ sk_A @ sk_A @ 
% 27.52/27.76        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 27.52/27.76        (k6_partfun1 @ sk_A))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('12', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('13', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf(dt_k1_partfun1, axiom,
% 27.52/27.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 27.52/27.76     ( ( ( v1_funct_1 @ E ) & 
% 27.52/27.76         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 27.52/27.76         ( v1_funct_1 @ F ) & 
% 27.52/27.76         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 27.52/27.76       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 27.52/27.76         ( m1_subset_1 @
% 27.52/27.76           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 27.52/27.76           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 27.52/27.76  thf('14', plain,
% 27.52/27.76      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 27.52/27.76         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 27.52/27.76          | ~ (v1_funct_1 @ X23)
% 27.52/27.76          | ~ (v1_funct_1 @ X26)
% 27.52/27.76          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 27.52/27.76          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 27.52/27.76             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 27.52/27.76      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 27.52/27.76  thf('15', plain,
% 27.52/27.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.52/27.76         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 27.52/27.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 27.52/27.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 27.52/27.76          | ~ (v1_funct_1 @ X1)
% 27.52/27.76          | ~ (v1_funct_1 @ sk_C))),
% 27.52/27.76      inference('sup-', [status(thm)], ['13', '14'])).
% 27.52/27.76  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('17', plain,
% 27.52/27.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.52/27.76         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 27.52/27.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 27.52/27.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 27.52/27.76          | ~ (v1_funct_1 @ X1))),
% 27.52/27.76      inference('demod', [status(thm)], ['15', '16'])).
% 27.52/27.76  thf('18', plain,
% 27.52/27.76      ((~ (v1_funct_1 @ sk_D)
% 27.52/27.76        | (m1_subset_1 @ 
% 27.52/27.76           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 27.52/27.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 27.52/27.76      inference('sup-', [status(thm)], ['12', '17'])).
% 27.52/27.76  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('20', plain,
% 27.52/27.76      ((m1_subset_1 @ 
% 27.52/27.76        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 27.52/27.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 27.52/27.76      inference('demod', [status(thm)], ['18', '19'])).
% 27.52/27.76  thf(redefinition_r2_relset_1, axiom,
% 27.52/27.76    (![A:$i,B:$i,C:$i,D:$i]:
% 27.52/27.76     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 27.52/27.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 27.52/27.76       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 27.52/27.76  thf('21', plain,
% 27.52/27.76      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 27.52/27.76         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 27.52/27.76          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 27.52/27.76          | ((X18) = (X21))
% 27.52/27.76          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 27.52/27.76      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 27.52/27.76  thf('22', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 27.52/27.76             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 27.52/27.76          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 27.52/27.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 27.52/27.76      inference('sup-', [status(thm)], ['20', '21'])).
% 27.52/27.76  thf('23', plain,
% 27.52/27.76      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 27.52/27.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 27.52/27.76        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 27.52/27.76            = (k6_partfun1 @ sk_A)))),
% 27.52/27.76      inference('sup-', [status(thm)], ['11', '22'])).
% 27.52/27.76  thf(t29_relset_1, axiom,
% 27.52/27.76    (![A:$i]:
% 27.52/27.76     ( m1_subset_1 @
% 27.52/27.76       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 27.52/27.76  thf('24', plain,
% 27.52/27.76      (![X22 : $i]:
% 27.52/27.76         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 27.52/27.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 27.52/27.76      inference('cnf', [status(esa)], [t29_relset_1])).
% 27.52/27.76  thf(redefinition_k6_partfun1, axiom,
% 27.52/27.76    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 27.52/27.76  thf('25', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 27.52/27.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 27.52/27.76  thf('26', plain,
% 27.52/27.76      (![X22 : $i]:
% 27.52/27.76         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 27.52/27.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 27.52/27.76      inference('demod', [status(thm)], ['24', '25'])).
% 27.52/27.76  thf('27', plain,
% 27.52/27.76      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 27.52/27.76         = (k6_partfun1 @ sk_A))),
% 27.52/27.76      inference('demod', [status(thm)], ['23', '26'])).
% 27.52/27.76  thf('28', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf(t24_funct_2, axiom,
% 27.52/27.76    (![A:$i,B:$i,C:$i]:
% 27.52/27.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 27.52/27.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 27.52/27.76       ( ![D:$i]:
% 27.52/27.76         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 27.52/27.76             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 27.52/27.76           ( ( r2_relset_1 @
% 27.52/27.76               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 27.52/27.76               ( k6_partfun1 @ B ) ) =>
% 27.52/27.76             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 27.52/27.76  thf('29', plain,
% 27.52/27.76      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 27.52/27.76         (~ (v1_funct_1 @ X36)
% 27.52/27.76          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 27.52/27.76          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 27.52/27.76          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 27.52/27.76               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 27.52/27.76               (k6_partfun1 @ X37))
% 27.52/27.76          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 27.52/27.76          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 27.52/27.76          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 27.52/27.76          | ~ (v1_funct_1 @ X39))),
% 27.52/27.76      inference('cnf', [status(esa)], [t24_funct_2])).
% 27.52/27.76  thf('30', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (~ (v1_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 27.52/27.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 27.52/27.76          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 27.52/27.76          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 27.52/27.76               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 27.52/27.76               (k6_partfun1 @ sk_A))
% 27.52/27.76          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 27.52/27.76          | ~ (v1_funct_1 @ sk_C))),
% 27.52/27.76      inference('sup-', [status(thm)], ['28', '29'])).
% 27.52/27.76  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('33', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (~ (v1_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 27.52/27.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 27.52/27.76          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 27.52/27.76          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 27.52/27.76               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 27.52/27.76               (k6_partfun1 @ sk_A)))),
% 27.52/27.76      inference('demod', [status(thm)], ['30', '31', '32'])).
% 27.52/27.76  thf('34', plain,
% 27.52/27.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 27.52/27.76           (k6_partfun1 @ sk_A))
% 27.52/27.76        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 27.52/27.76        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 27.52/27.76        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 27.52/27.76        | ~ (v1_funct_1 @ sk_D))),
% 27.52/27.76      inference('sup-', [status(thm)], ['27', '33'])).
% 27.52/27.76  thf('35', plain,
% 27.52/27.76      (![X22 : $i]:
% 27.52/27.76         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 27.52/27.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 27.52/27.76      inference('demod', [status(thm)], ['24', '25'])).
% 27.52/27.76  thf('36', plain,
% 27.52/27.76      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 27.52/27.76         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 27.52/27.76          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 27.52/27.76          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 27.52/27.76          | ((X18) != (X21)))),
% 27.52/27.76      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 27.52/27.76  thf('37', plain,
% 27.52/27.76      (![X19 : $i, X20 : $i, X21 : $i]:
% 27.52/27.76         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 27.52/27.76          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 27.52/27.76      inference('simplify', [status(thm)], ['36'])).
% 27.52/27.76  thf('38', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 27.52/27.76      inference('sup-', [status(thm)], ['35', '37'])).
% 27.52/27.76  thf('39', plain,
% 27.52/27.76      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 27.52/27.76      inference('sup-', [status(thm)], ['3', '4'])).
% 27.52/27.76  thf('40', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('41', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('42', plain, ((v1_funct_1 @ sk_D)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('43', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 27.52/27.76      inference('demod', [status(thm)], ['34', '38', '39', '40', '41', '42'])).
% 27.52/27.76  thf('44', plain,
% 27.52/27.76      ((((sk_A) != (sk_A))
% 27.52/27.76        | ~ (v2_funct_1 @ sk_D)
% 27.52/27.76        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 27.52/27.76      inference('demod', [status(thm)], ['10', '43'])).
% 27.52/27.76  thf('45', plain,
% 27.52/27.76      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 27.52/27.76        | ~ (v2_funct_1 @ sk_D))),
% 27.52/27.76      inference('simplify', [status(thm)], ['44'])).
% 27.52/27.76  thf('46', plain,
% 27.52/27.76      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 27.52/27.76         = (k6_partfun1 @ sk_A))),
% 27.52/27.76      inference('demod', [status(thm)], ['23', '26'])).
% 27.52/27.76  thf('47', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf(t30_funct_2, axiom,
% 27.52/27.76    (![A:$i,B:$i,C:$i,D:$i]:
% 27.52/27.76     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 27.52/27.76         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 27.52/27.76       ( ![E:$i]:
% 27.52/27.76         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 27.52/27.76             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 27.52/27.76           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 27.52/27.76               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 27.52/27.76             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 27.52/27.76               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 27.52/27.76  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 27.52/27.76  thf(zf_stmt_2, axiom,
% 27.52/27.76    (![C:$i,B:$i]:
% 27.52/27.76     ( ( zip_tseitin_1 @ C @ B ) =>
% 27.52/27.76       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 27.52/27.76  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 27.52/27.76  thf(zf_stmt_4, axiom,
% 27.52/27.76    (![E:$i,D:$i]:
% 27.52/27.76     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 27.52/27.76  thf(zf_stmt_5, axiom,
% 27.52/27.76    (![A:$i,B:$i,C:$i,D:$i]:
% 27.52/27.76     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 27.52/27.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 27.52/27.76       ( ![E:$i]:
% 27.52/27.76         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 27.52/27.76             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 27.52/27.76           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 27.52/27.76               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 27.52/27.76             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 27.52/27.76  thf('48', plain,
% 27.52/27.76      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 27.52/27.76         (~ (v1_funct_1 @ X44)
% 27.52/27.76          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 27.52/27.76          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 27.52/27.76          | (zip_tseitin_0 @ X44 @ X47)
% 27.52/27.76          | ~ (v2_funct_1 @ (k1_partfun1 @ X48 @ X45 @ X45 @ X46 @ X47 @ X44))
% 27.52/27.76          | (zip_tseitin_1 @ X46 @ X45)
% 27.52/27.76          | ((k2_relset_1 @ X48 @ X45 @ X47) != (X45))
% 27.52/27.76          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X45)))
% 27.52/27.76          | ~ (v1_funct_2 @ X47 @ X48 @ X45)
% 27.52/27.76          | ~ (v1_funct_1 @ X47))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 27.52/27.76  thf('49', plain,
% 27.52/27.76      (![X0 : $i, X1 : $i]:
% 27.52/27.76         (~ (v1_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 27.52/27.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 27.52/27.76          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 27.52/27.76          | (zip_tseitin_1 @ sk_A @ sk_B)
% 27.52/27.76          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 27.52/27.76          | (zip_tseitin_0 @ sk_D @ X0)
% 27.52/27.76          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 27.52/27.76          | ~ (v1_funct_1 @ sk_D))),
% 27.52/27.76      inference('sup-', [status(thm)], ['47', '48'])).
% 27.52/27.76  thf('50', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('52', plain,
% 27.52/27.76      (![X0 : $i, X1 : $i]:
% 27.52/27.76         (~ (v1_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 27.52/27.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 27.52/27.76          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 27.52/27.76          | (zip_tseitin_1 @ sk_A @ sk_B)
% 27.52/27.76          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 27.52/27.76          | (zip_tseitin_0 @ sk_D @ X0))),
% 27.52/27.76      inference('demod', [status(thm)], ['49', '50', '51'])).
% 27.52/27.76  thf('53', plain,
% 27.52/27.76      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 27.52/27.76        | (zip_tseitin_0 @ sk_D @ sk_C)
% 27.52/27.76        | (zip_tseitin_1 @ sk_A @ sk_B)
% 27.52/27.76        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 27.52/27.76        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 27.52/27.76        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 27.52/27.76        | ~ (v1_funct_1 @ sk_C))),
% 27.52/27.76      inference('sup-', [status(thm)], ['46', '52'])).
% 27.52/27.76  thf('54', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('55', plain,
% 27.52/27.76      (![X15 : $i, X16 : $i, X17 : $i]:
% 27.52/27.76         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 27.52/27.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 27.52/27.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 27.52/27.76  thf('56', plain,
% 27.52/27.76      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 27.52/27.76      inference('sup-', [status(thm)], ['54', '55'])).
% 27.52/27.76  thf('57', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('58', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 27.52/27.76      inference('sup+', [status(thm)], ['56', '57'])).
% 27.52/27.76  thf(t80_relat_1, axiom,
% 27.52/27.76    (![A:$i]:
% 27.52/27.76     ( ( v1_relat_1 @ A ) =>
% 27.52/27.76       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 27.52/27.76  thf('59', plain,
% 27.52/27.76      (![X6 : $i]:
% 27.52/27.76         (((k5_relat_1 @ X6 @ (k6_relat_1 @ (k2_relat_1 @ X6))) = (X6))
% 27.52/27.76          | ~ (v1_relat_1 @ X6))),
% 27.52/27.76      inference('cnf', [status(esa)], [t80_relat_1])).
% 27.52/27.76  thf('60', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 27.52/27.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 27.52/27.76  thf('61', plain,
% 27.52/27.76      (![X6 : $i]:
% 27.52/27.76         (((k5_relat_1 @ X6 @ (k6_partfun1 @ (k2_relat_1 @ X6))) = (X6))
% 27.52/27.76          | ~ (v1_relat_1 @ X6))),
% 27.52/27.76      inference('demod', [status(thm)], ['59', '60'])).
% 27.52/27.76  thf('62', plain,
% 27.52/27.76      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 27.52/27.76        | ~ (v1_relat_1 @ sk_C))),
% 27.52/27.76      inference('sup+', [status(thm)], ['58', '61'])).
% 27.52/27.76  thf('63', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf(cc1_relset_1, axiom,
% 27.52/27.76    (![A:$i,B:$i,C:$i]:
% 27.52/27.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 27.52/27.76       ( v1_relat_1 @ C ) ))).
% 27.52/27.76  thf('64', plain,
% 27.52/27.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 27.52/27.76         ((v1_relat_1 @ X12)
% 27.52/27.76          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 27.52/27.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 27.52/27.76  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 27.52/27.76      inference('sup-', [status(thm)], ['63', '64'])).
% 27.52/27.76  thf('66', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 27.52/27.76      inference('demod', [status(thm)], ['62', '65'])).
% 27.52/27.76  thf(t78_relat_1, axiom,
% 27.52/27.76    (![A:$i]:
% 27.52/27.76     ( ( v1_relat_1 @ A ) =>
% 27.52/27.76       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 27.52/27.76  thf('67', plain,
% 27.52/27.76      (![X5 : $i]:
% 27.52/27.76         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 27.52/27.76          | ~ (v1_relat_1 @ X5))),
% 27.52/27.76      inference('cnf', [status(esa)], [t78_relat_1])).
% 27.52/27.76  thf('68', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 27.52/27.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 27.52/27.76  thf('69', plain,
% 27.52/27.76      (![X5 : $i]:
% 27.52/27.76         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 27.52/27.76          | ~ (v1_relat_1 @ X5))),
% 27.52/27.76      inference('demod', [status(thm)], ['67', '68'])).
% 27.52/27.76  thf(t55_relat_1, axiom,
% 27.52/27.76    (![A:$i]:
% 27.52/27.76     ( ( v1_relat_1 @ A ) =>
% 27.52/27.76       ( ![B:$i]:
% 27.52/27.76         ( ( v1_relat_1 @ B ) =>
% 27.52/27.76           ( ![C:$i]:
% 27.52/27.76             ( ( v1_relat_1 @ C ) =>
% 27.52/27.76               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 27.52/27.76                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 27.52/27.76  thf('70', plain,
% 27.52/27.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.52/27.76         (~ (v1_relat_1 @ X0)
% 27.52/27.76          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 27.52/27.76              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 27.52/27.76          | ~ (v1_relat_1 @ X2)
% 27.52/27.76          | ~ (v1_relat_1 @ X1))),
% 27.52/27.76      inference('cnf', [status(esa)], [t55_relat_1])).
% 27.52/27.76  thf('71', plain,
% 27.52/27.76      (![X0 : $i, X1 : $i]:
% 27.52/27.76         (((k5_relat_1 @ X0 @ X1)
% 27.52/27.76            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 27.52/27.76               (k5_relat_1 @ X0 @ X1)))
% 27.52/27.76          | ~ (v1_relat_1 @ X0)
% 27.52/27.76          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 27.52/27.76          | ~ (v1_relat_1 @ X1)
% 27.52/27.76          | ~ (v1_relat_1 @ X0))),
% 27.52/27.76      inference('sup+', [status(thm)], ['69', '70'])).
% 27.52/27.76  thf('72', plain,
% 27.52/27.76      (![X0 : $i, X1 : $i]:
% 27.52/27.76         (~ (v1_relat_1 @ X1)
% 27.52/27.76          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 27.52/27.76          | ~ (v1_relat_1 @ X0)
% 27.52/27.76          | ((k5_relat_1 @ X0 @ X1)
% 27.52/27.76              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 27.52/27.76                 (k5_relat_1 @ X0 @ X1))))),
% 27.52/27.76      inference('simplify', [status(thm)], ['71'])).
% 27.52/27.76  thf('73', plain,
% 27.52/27.76      (![X22 : $i]:
% 27.52/27.76         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 27.52/27.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 27.52/27.76      inference('demod', [status(thm)], ['24', '25'])).
% 27.52/27.76  thf('74', plain,
% 27.52/27.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 27.52/27.76         ((v1_relat_1 @ X12)
% 27.52/27.76          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 27.52/27.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 27.52/27.76  thf('75', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 27.52/27.76      inference('sup-', [status(thm)], ['73', '74'])).
% 27.52/27.76  thf('76', plain,
% 27.52/27.76      (![X0 : $i, X1 : $i]:
% 27.52/27.76         (~ (v1_relat_1 @ X1)
% 27.52/27.76          | ~ (v1_relat_1 @ X0)
% 27.52/27.76          | ((k5_relat_1 @ X0 @ X1)
% 27.52/27.76              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 27.52/27.76                 (k5_relat_1 @ X0 @ X1))))),
% 27.52/27.76      inference('demod', [status(thm)], ['72', '75'])).
% 27.52/27.76  thf('77', plain,
% 27.52/27.76      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B))
% 27.52/27.76          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))
% 27.52/27.76        | ~ (v1_relat_1 @ sk_C)
% 27.52/27.76        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 27.52/27.76      inference('sup+', [status(thm)], ['66', '76'])).
% 27.52/27.76  thf('78', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 27.52/27.76      inference('demod', [status(thm)], ['62', '65'])).
% 27.52/27.76  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 27.52/27.76      inference('sup-', [status(thm)], ['63', '64'])).
% 27.52/27.76  thf('80', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 27.52/27.76      inference('sup-', [status(thm)], ['73', '74'])).
% 27.52/27.76  thf('81', plain,
% 27.52/27.76      (((sk_C) = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))),
% 27.52/27.76      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 27.52/27.76  thf(t48_funct_1, axiom,
% 27.52/27.76    (![A:$i]:
% 27.52/27.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 27.52/27.76       ( ![B:$i]:
% 27.52/27.76         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 27.52/27.76           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 27.52/27.76               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 27.52/27.76             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 27.52/27.76  thf('82', plain,
% 27.52/27.76      (![X8 : $i, X9 : $i]:
% 27.52/27.76         (~ (v1_relat_1 @ X8)
% 27.52/27.76          | ~ (v1_funct_1 @ X8)
% 27.52/27.76          | (v2_funct_1 @ X8)
% 27.52/27.76          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 27.52/27.76          | ~ (v2_funct_1 @ (k5_relat_1 @ X8 @ X9))
% 27.52/27.76          | ~ (v1_funct_1 @ X9)
% 27.52/27.76          | ~ (v1_relat_1 @ X9))),
% 27.52/27.76      inference('cnf', [status(esa)], [t48_funct_1])).
% 27.52/27.76  thf('83', plain,
% 27.52/27.76      ((~ (v2_funct_1 @ sk_C)
% 27.52/27.76        | ~ (v1_relat_1 @ sk_C)
% 27.52/27.76        | ~ (v1_funct_1 @ sk_C)
% 27.52/27.76        | ((k2_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 27.52/27.76            != (k1_relat_1 @ sk_C))
% 27.52/27.76        | (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 27.52/27.76        | ~ (v1_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 27.52/27.76        | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 27.52/27.76      inference('sup-', [status(thm)], ['81', '82'])).
% 27.52/27.76  thf('84', plain, ((v2_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 27.52/27.76      inference('sup-', [status(thm)], ['63', '64'])).
% 27.52/27.76  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf(t71_relat_1, axiom,
% 27.52/27.76    (![A:$i]:
% 27.52/27.76     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 27.52/27.76       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 27.52/27.76  thf('87', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 27.52/27.76      inference('cnf', [status(esa)], [t71_relat_1])).
% 27.52/27.76  thf('88', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 27.52/27.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 27.52/27.76  thf('89', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 27.52/27.76      inference('demod', [status(thm)], ['87', '88'])).
% 27.52/27.76  thf('90', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 27.52/27.76      inference('sup-', [status(thm)], ['73', '74'])).
% 27.52/27.76  thf('91', plain,
% 27.52/27.76      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 27.52/27.76        | (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 27.52/27.76        | ~ (v1_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 27.52/27.76      inference('demod', [status(thm)], ['83', '84', '85', '86', '89', '90'])).
% 27.52/27.76  thf('92', plain,
% 27.52/27.76      ((~ (v1_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 27.52/27.76        | (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 27.52/27.76      inference('simplify', [status(thm)], ['91'])).
% 27.52/27.76  thf('93', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('94', plain,
% 27.52/27.76      (![X49 : $i, X50 : $i, X51 : $i]:
% 27.52/27.76         (((X49) = (k1_xboole_0))
% 27.52/27.76          | ~ (v1_funct_1 @ X50)
% 27.52/27.76          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 27.52/27.76          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 27.52/27.76          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_partfun1 @ X51))
% 27.52/27.76          | ~ (v2_funct_1 @ X50)
% 27.52/27.76          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 27.52/27.76      inference('cnf', [status(esa)], [t35_funct_2])).
% 27.52/27.76  thf('95', plain,
% 27.52/27.76      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 27.52/27.76        | ~ (v2_funct_1 @ sk_C)
% 27.52/27.76        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 27.52/27.76        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 27.52/27.76        | ~ (v1_funct_1 @ sk_C)
% 27.52/27.76        | ((sk_B) = (k1_xboole_0)))),
% 27.52/27.76      inference('sup-', [status(thm)], ['93', '94'])).
% 27.52/27.76  thf('96', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('98', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('100', plain,
% 27.52/27.76      ((((sk_B) != (sk_B))
% 27.52/27.76        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 27.52/27.76        | ((sk_B) = (k1_xboole_0)))),
% 27.52/27.76      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 27.52/27.76  thf('101', plain,
% 27.52/27.76      ((((sk_B) = (k1_xboole_0))
% 27.52/27.76        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 27.52/27.76      inference('simplify', [status(thm)], ['100'])).
% 27.52/27.76  thf('102', plain, (((sk_B) != (k1_xboole_0))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('103', plain,
% 27.52/27.76      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 27.52/27.76      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 27.52/27.76  thf(t58_funct_1, axiom,
% 27.52/27.76    (![A:$i]:
% 27.52/27.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 27.52/27.76       ( ( v2_funct_1 @ A ) =>
% 27.52/27.76         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 27.52/27.76             ( k1_relat_1 @ A ) ) & 
% 27.52/27.76           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 27.52/27.76             ( k1_relat_1 @ A ) ) ) ) ))).
% 27.52/27.76  thf('104', plain,
% 27.52/27.76      (![X11 : $i]:
% 27.52/27.76         (~ (v2_funct_1 @ X11)
% 27.52/27.76          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ (k2_funct_1 @ X11)))
% 27.52/27.76              = (k1_relat_1 @ X11))
% 27.52/27.76          | ~ (v1_funct_1 @ X11)
% 27.52/27.76          | ~ (v1_relat_1 @ X11))),
% 27.52/27.76      inference('cnf', [status(esa)], [t58_funct_1])).
% 27.52/27.76  thf('105', plain,
% 27.52/27.76      ((((k2_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 27.52/27.76        | ~ (v1_relat_1 @ sk_C)
% 27.52/27.76        | ~ (v1_funct_1 @ sk_C)
% 27.52/27.76        | ~ (v2_funct_1 @ sk_C))),
% 27.52/27.76      inference('sup+', [status(thm)], ['103', '104'])).
% 27.52/27.76  thf('106', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 27.52/27.76      inference('demod', [status(thm)], ['87', '88'])).
% 27.52/27.76  thf('107', plain, ((v1_relat_1 @ sk_C)),
% 27.52/27.76      inference('sup-', [status(thm)], ['63', '64'])).
% 27.52/27.76  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('109', plain, ((v2_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('110', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 27.52/27.76      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 27.52/27.76  thf('111', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 27.52/27.76      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 27.52/27.76  thf('112', plain,
% 27.52/27.76      ((~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 27.52/27.76        | (v2_funct_1 @ (k6_partfun1 @ sk_A)))),
% 27.52/27.76      inference('demod', [status(thm)], ['92', '110', '111'])).
% 27.52/27.76  thf('113', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('114', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('115', plain,
% 27.52/27.76      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 27.52/27.76         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 27.52/27.76          | ~ (v1_funct_1 @ X23)
% 27.52/27.76          | ~ (v1_funct_1 @ X26)
% 27.52/27.76          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 27.52/27.76          | (v1_funct_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)))),
% 27.52/27.76      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 27.52/27.76  thf('116', plain,
% 27.52/27.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.52/27.76         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 27.52/27.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 27.52/27.76          | ~ (v1_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_funct_1 @ sk_C))),
% 27.52/27.76      inference('sup-', [status(thm)], ['114', '115'])).
% 27.52/27.76  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('118', plain,
% 27.52/27.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.52/27.76         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 27.52/27.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 27.52/27.76          | ~ (v1_funct_1 @ X0))),
% 27.52/27.76      inference('demod', [status(thm)], ['116', '117'])).
% 27.52/27.76  thf('119', plain,
% 27.52/27.76      ((~ (v1_funct_1 @ sk_D)
% 27.52/27.76        | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)))),
% 27.52/27.76      inference('sup-', [status(thm)], ['113', '118'])).
% 27.52/27.76  thf('120', plain, ((v1_funct_1 @ sk_D)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('121', plain,
% 27.52/27.76      ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D))),
% 27.52/27.76      inference('demod', [status(thm)], ['119', '120'])).
% 27.52/27.76  thf('122', plain,
% 27.52/27.76      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 27.52/27.76         = (k6_partfun1 @ sk_A))),
% 27.52/27.76      inference('demod', [status(thm)], ['23', '26'])).
% 27.52/27.76  thf('123', plain, ((v1_funct_1 @ (k6_partfun1 @ sk_A))),
% 27.52/27.76      inference('demod', [status(thm)], ['121', '122'])).
% 27.52/27.76  thf('124', plain, ((v2_funct_1 @ (k6_partfun1 @ sk_A))),
% 27.52/27.76      inference('demod', [status(thm)], ['112', '123'])).
% 27.52/27.76  thf('125', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('126', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('127', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('128', plain, ((v1_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('129', plain,
% 27.52/27.76      (((zip_tseitin_0 @ sk_D @ sk_C)
% 27.52/27.76        | (zip_tseitin_1 @ sk_A @ sk_B)
% 27.52/27.76        | ((sk_B) != (sk_B)))),
% 27.52/27.76      inference('demod', [status(thm)],
% 27.52/27.76                ['53', '124', '125', '126', '127', '128'])).
% 27.52/27.76  thf('130', plain,
% 27.52/27.76      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 27.52/27.76      inference('simplify', [status(thm)], ['129'])).
% 27.52/27.76  thf('131', plain,
% 27.52/27.76      (![X42 : $i, X43 : $i]:
% 27.52/27.76         (((X42) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X42 @ X43))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_2])).
% 27.52/27.76  thf('132', plain,
% 27.52/27.76      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 27.52/27.76      inference('sup-', [status(thm)], ['130', '131'])).
% 27.52/27.76  thf('133', plain, (((sk_A) != (k1_xboole_0))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('134', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 27.52/27.76      inference('simplify_reflect-', [status(thm)], ['132', '133'])).
% 27.52/27.76  thf('135', plain,
% 27.52/27.76      (![X40 : $i, X41 : $i]:
% 27.52/27.76         ((v2_funct_1 @ X41) | ~ (zip_tseitin_0 @ X41 @ X40))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_4])).
% 27.52/27.76  thf('136', plain, ((v2_funct_1 @ sk_D)),
% 27.52/27.76      inference('sup-', [status(thm)], ['134', '135'])).
% 27.52/27.76  thf('137', plain,
% 27.52/27.76      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 27.52/27.76      inference('demod', [status(thm)], ['45', '136'])).
% 27.52/27.76  thf('138', plain,
% 27.52/27.76      (![X11 : $i]:
% 27.52/27.76         (~ (v2_funct_1 @ X11)
% 27.52/27.76          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ (k2_funct_1 @ X11)))
% 27.52/27.76              = (k1_relat_1 @ X11))
% 27.52/27.76          | ~ (v1_funct_1 @ X11)
% 27.52/27.76          | ~ (v1_relat_1 @ X11))),
% 27.52/27.76      inference('cnf', [status(esa)], [t58_funct_1])).
% 27.52/27.76  thf('139', plain,
% 27.52/27.76      ((((k2_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 27.52/27.76        | ~ (v1_relat_1 @ sk_D)
% 27.52/27.76        | ~ (v1_funct_1 @ sk_D)
% 27.52/27.76        | ~ (v2_funct_1 @ sk_D))),
% 27.52/27.76      inference('sup+', [status(thm)], ['137', '138'])).
% 27.52/27.76  thf('140', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 27.52/27.76      inference('demod', [status(thm)], ['87', '88'])).
% 27.52/27.76  thf('141', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('142', plain,
% 27.52/27.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 27.52/27.76         ((v1_relat_1 @ X12)
% 27.52/27.76          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 27.52/27.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 27.52/27.76  thf('143', plain, ((v1_relat_1 @ sk_D)),
% 27.52/27.76      inference('sup-', [status(thm)], ['141', '142'])).
% 27.52/27.76  thf('144', plain, ((v1_funct_1 @ sk_D)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('145', plain, ((v2_funct_1 @ sk_D)),
% 27.52/27.76      inference('sup-', [status(thm)], ['134', '135'])).
% 27.52/27.76  thf('146', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 27.52/27.76      inference('demod', [status(thm)], ['139', '140', '143', '144', '145'])).
% 27.52/27.76  thf('147', plain,
% 27.52/27.76      (![X5 : $i]:
% 27.52/27.76         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 27.52/27.76          | ~ (v1_relat_1 @ X5))),
% 27.52/27.76      inference('demod', [status(thm)], ['67', '68'])).
% 27.52/27.76  thf('148', plain,
% 27.52/27.76      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 27.52/27.76        | ~ (v1_relat_1 @ sk_D))),
% 27.52/27.76      inference('sup+', [status(thm)], ['146', '147'])).
% 27.52/27.76  thf('149', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('150', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf(redefinition_k1_partfun1, axiom,
% 27.52/27.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 27.52/27.76     ( ( ( v1_funct_1 @ E ) & 
% 27.52/27.76         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 27.52/27.76         ( v1_funct_1 @ F ) & 
% 27.52/27.76         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 27.52/27.76       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 27.52/27.76  thf('151', plain,
% 27.52/27.76      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 27.52/27.76         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 27.52/27.76          | ~ (v1_funct_1 @ X29)
% 27.52/27.76          | ~ (v1_funct_1 @ X32)
% 27.52/27.76          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 27.52/27.76          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 27.52/27.76              = (k5_relat_1 @ X29 @ X32)))),
% 27.52/27.76      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 27.52/27.76  thf('152', plain,
% 27.52/27.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.52/27.76         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 27.52/27.76            = (k5_relat_1 @ sk_C @ X0))
% 27.52/27.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 27.52/27.76          | ~ (v1_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_funct_1 @ sk_C))),
% 27.52/27.76      inference('sup-', [status(thm)], ['150', '151'])).
% 27.52/27.76  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('154', plain,
% 27.52/27.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.52/27.76         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 27.52/27.76            = (k5_relat_1 @ sk_C @ X0))
% 27.52/27.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 27.52/27.76          | ~ (v1_funct_1 @ X0))),
% 27.52/27.76      inference('demod', [status(thm)], ['152', '153'])).
% 27.52/27.76  thf('155', plain,
% 27.52/27.76      ((~ (v1_funct_1 @ sk_D)
% 27.52/27.76        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 27.52/27.76            = (k5_relat_1 @ sk_C @ sk_D)))),
% 27.52/27.76      inference('sup-', [status(thm)], ['149', '154'])).
% 27.52/27.76  thf('156', plain, ((v1_funct_1 @ sk_D)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('157', plain,
% 27.52/27.76      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 27.52/27.76         = (k6_partfun1 @ sk_A))),
% 27.52/27.76      inference('demod', [status(thm)], ['23', '26'])).
% 27.52/27.76  thf('158', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 27.52/27.76      inference('demod', [status(thm)], ['155', '156', '157'])).
% 27.52/27.76  thf(dt_k2_funct_1, axiom,
% 27.52/27.76    (![A:$i]:
% 27.52/27.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 27.52/27.76       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 27.52/27.76         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 27.52/27.76  thf('159', plain,
% 27.52/27.76      (![X7 : $i]:
% 27.52/27.76         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 27.52/27.76          | ~ (v1_funct_1 @ X7)
% 27.52/27.76          | ~ (v1_relat_1 @ X7))),
% 27.52/27.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 27.52/27.76  thf('160', plain,
% 27.52/27.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('161', plain,
% 27.52/27.76      (![X49 : $i, X50 : $i, X51 : $i]:
% 27.52/27.76         (((X49) = (k1_xboole_0))
% 27.52/27.76          | ~ (v1_funct_1 @ X50)
% 27.52/27.76          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 27.52/27.76          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 27.52/27.76          | ((k5_relat_1 @ (k2_funct_1 @ X50) @ X50) = (k6_partfun1 @ X49))
% 27.52/27.76          | ~ (v2_funct_1 @ X50)
% 27.52/27.76          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 27.52/27.76      inference('cnf', [status(esa)], [t35_funct_2])).
% 27.52/27.76  thf('162', plain,
% 27.52/27.76      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 27.52/27.76        | ~ (v2_funct_1 @ sk_C)
% 27.52/27.76        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 27.52/27.76        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 27.52/27.76        | ~ (v1_funct_1 @ sk_C)
% 27.52/27.76        | ((sk_B) = (k1_xboole_0)))),
% 27.52/27.76      inference('sup-', [status(thm)], ['160', '161'])).
% 27.52/27.76  thf('163', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('164', plain, ((v2_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('165', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('166', plain, ((v1_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('167', plain,
% 27.52/27.76      ((((sk_B) != (sk_B))
% 27.52/27.76        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 27.52/27.76        | ((sk_B) = (k1_xboole_0)))),
% 27.52/27.76      inference('demod', [status(thm)], ['162', '163', '164', '165', '166'])).
% 27.52/27.76  thf('168', plain,
% 27.52/27.76      ((((sk_B) = (k1_xboole_0))
% 27.52/27.76        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 27.52/27.76      inference('simplify', [status(thm)], ['167'])).
% 27.52/27.76  thf('169', plain, (((sk_B) != (k1_xboole_0))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('170', plain,
% 27.52/27.76      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 27.52/27.76      inference('simplify_reflect-', [status(thm)], ['168', '169'])).
% 27.52/27.76  thf('171', plain,
% 27.52/27.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.52/27.76         (~ (v1_relat_1 @ X0)
% 27.52/27.76          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 27.52/27.76              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 27.52/27.76          | ~ (v1_relat_1 @ X2)
% 27.52/27.76          | ~ (v1_relat_1 @ X1))),
% 27.52/27.76      inference('cnf', [status(esa)], [t55_relat_1])).
% 27.52/27.76  thf('172', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 27.52/27.76            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 27.52/27.76          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 27.52/27.76          | ~ (v1_relat_1 @ X0)
% 27.52/27.76          | ~ (v1_relat_1 @ sk_C))),
% 27.52/27.76      inference('sup+', [status(thm)], ['170', '171'])).
% 27.52/27.76  thf('173', plain, ((v1_relat_1 @ sk_C)),
% 27.52/27.76      inference('sup-', [status(thm)], ['63', '64'])).
% 27.52/27.76  thf('174', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 27.52/27.76            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 27.52/27.76          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 27.52/27.76          | ~ (v1_relat_1 @ X0))),
% 27.52/27.76      inference('demod', [status(thm)], ['172', '173'])).
% 27.52/27.76  thf('175', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (~ (v1_relat_1 @ sk_C)
% 27.52/27.76          | ~ (v1_funct_1 @ sk_C)
% 27.52/27.76          | ~ (v1_relat_1 @ X0)
% 27.52/27.76          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 27.52/27.76              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 27.52/27.76      inference('sup-', [status(thm)], ['159', '174'])).
% 27.52/27.76  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 27.52/27.76      inference('sup-', [status(thm)], ['63', '64'])).
% 27.52/27.76  thf('177', plain, ((v1_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('178', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (~ (v1_relat_1 @ X0)
% 27.52/27.76          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 27.52/27.76              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 27.52/27.76      inference('demod', [status(thm)], ['175', '176', '177'])).
% 27.52/27.76  thf('179', plain,
% 27.52/27.76      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 27.52/27.76          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 27.52/27.76        | ~ (v1_relat_1 @ sk_D))),
% 27.52/27.76      inference('sup+', [status(thm)], ['158', '178'])).
% 27.52/27.76  thf('180', plain,
% 27.52/27.76      (![X7 : $i]:
% 27.52/27.76         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 27.52/27.76          | ~ (v1_funct_1 @ X7)
% 27.52/27.76          | ~ (v1_relat_1 @ X7))),
% 27.52/27.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 27.52/27.76  thf(t55_funct_1, axiom,
% 27.52/27.76    (![A:$i]:
% 27.52/27.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 27.52/27.76       ( ( v2_funct_1 @ A ) =>
% 27.52/27.76         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 27.52/27.76           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 27.52/27.76  thf('181', plain,
% 27.52/27.76      (![X10 : $i]:
% 27.52/27.76         (~ (v2_funct_1 @ X10)
% 27.52/27.76          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 27.52/27.76          | ~ (v1_funct_1 @ X10)
% 27.52/27.76          | ~ (v1_relat_1 @ X10))),
% 27.52/27.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 27.52/27.76  thf('182', plain,
% 27.52/27.76      (![X6 : $i]:
% 27.52/27.76         (((k5_relat_1 @ X6 @ (k6_partfun1 @ (k2_relat_1 @ X6))) = (X6))
% 27.52/27.76          | ~ (v1_relat_1 @ X6))),
% 27.52/27.76      inference('demod', [status(thm)], ['59', '60'])).
% 27.52/27.76  thf('183', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 27.52/27.76            = (k2_funct_1 @ X0))
% 27.52/27.76          | ~ (v1_relat_1 @ X0)
% 27.52/27.76          | ~ (v1_funct_1 @ X0)
% 27.52/27.76          | ~ (v2_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 27.52/27.76      inference('sup+', [status(thm)], ['181', '182'])).
% 27.52/27.76  thf('184', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (~ (v1_relat_1 @ X0)
% 27.52/27.76          | ~ (v1_funct_1 @ X0)
% 27.52/27.76          | ~ (v2_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_relat_1 @ X0)
% 27.52/27.76          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 27.52/27.76              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 27.52/27.76      inference('sup-', [status(thm)], ['180', '183'])).
% 27.52/27.76  thf('185', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 27.52/27.76            = (k2_funct_1 @ X0))
% 27.52/27.76          | ~ (v2_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_relat_1 @ X0))),
% 27.52/27.76      inference('simplify', [status(thm)], ['184'])).
% 27.52/27.76  thf('186', plain,
% 27.52/27.76      (![X7 : $i]:
% 27.52/27.76         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 27.52/27.76          | ~ (v1_funct_1 @ X7)
% 27.52/27.76          | ~ (v1_relat_1 @ X7))),
% 27.52/27.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 27.52/27.76  thf('187', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 27.52/27.76      inference('sup+', [status(thm)], ['56', '57'])).
% 27.52/27.76  thf('188', plain,
% 27.52/27.76      (![X7 : $i]:
% 27.52/27.76         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 27.52/27.76          | ~ (v1_funct_1 @ X7)
% 27.52/27.76          | ~ (v1_relat_1 @ X7))),
% 27.52/27.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 27.52/27.76  thf('189', plain,
% 27.52/27.76      (![X10 : $i]:
% 27.52/27.76         (~ (v2_funct_1 @ X10)
% 27.52/27.76          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 27.52/27.76          | ~ (v1_funct_1 @ X10)
% 27.52/27.76          | ~ (v1_relat_1 @ X10))),
% 27.52/27.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 27.52/27.76  thf('190', plain,
% 27.52/27.76      (![X5 : $i]:
% 27.52/27.76         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 27.52/27.76          | ~ (v1_relat_1 @ X5))),
% 27.52/27.76      inference('demod', [status(thm)], ['67', '68'])).
% 27.52/27.76  thf('191', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 27.52/27.76            = (k2_funct_1 @ X0))
% 27.52/27.76          | ~ (v1_relat_1 @ X0)
% 27.52/27.76          | ~ (v1_funct_1 @ X0)
% 27.52/27.76          | ~ (v2_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 27.52/27.76      inference('sup+', [status(thm)], ['189', '190'])).
% 27.52/27.76  thf('192', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (~ (v1_relat_1 @ X0)
% 27.52/27.76          | ~ (v1_funct_1 @ X0)
% 27.52/27.76          | ~ (v2_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_relat_1 @ X0)
% 27.52/27.76          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 27.52/27.76              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 27.52/27.76      inference('sup-', [status(thm)], ['188', '191'])).
% 27.52/27.76  thf('193', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 27.52/27.76            = (k2_funct_1 @ X0))
% 27.52/27.76          | ~ (v2_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_funct_1 @ X0)
% 27.52/27.76          | ~ (v1_relat_1 @ X0))),
% 27.52/27.76      inference('simplify', [status(thm)], ['192'])).
% 27.52/27.76  thf('194', plain,
% 27.52/27.76      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 27.52/27.76          = (k2_funct_1 @ sk_C))
% 27.52/27.76        | ~ (v1_relat_1 @ sk_C)
% 27.52/27.76        | ~ (v1_funct_1 @ sk_C)
% 27.52/27.76        | ~ (v2_funct_1 @ sk_C))),
% 27.52/27.76      inference('sup+', [status(thm)], ['187', '193'])).
% 27.52/27.76  thf('195', plain, ((v1_relat_1 @ sk_C)),
% 27.52/27.76      inference('sup-', [status(thm)], ['63', '64'])).
% 27.52/27.76  thf('196', plain, ((v1_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('197', plain, ((v2_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('198', plain,
% 27.52/27.76      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 27.52/27.76         = (k2_funct_1 @ sk_C))),
% 27.52/27.76      inference('demod', [status(thm)], ['194', '195', '196', '197'])).
% 27.52/27.76  thf('199', plain,
% 27.52/27.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.52/27.76         (~ (v1_relat_1 @ X0)
% 27.52/27.76          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 27.52/27.76              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 27.52/27.76          | ~ (v1_relat_1 @ X2)
% 27.52/27.76          | ~ (v1_relat_1 @ X1))),
% 27.52/27.76      inference('cnf', [status(esa)], [t55_relat_1])).
% 27.52/27.76  thf('200', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 27.52/27.76            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 27.52/27.76               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 27.52/27.76          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 27.52/27.76          | ~ (v1_relat_1 @ X0)
% 27.52/27.76          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 27.52/27.76      inference('sup+', [status(thm)], ['198', '199'])).
% 27.52/27.76  thf('201', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 27.52/27.76      inference('sup-', [status(thm)], ['73', '74'])).
% 27.52/27.76  thf('202', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 27.52/27.76            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 27.52/27.76               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 27.52/27.76          | ~ (v1_relat_1 @ X0)
% 27.52/27.76          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 27.52/27.76      inference('demod', [status(thm)], ['200', '201'])).
% 27.52/27.76  thf('203', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (~ (v1_relat_1 @ sk_C)
% 27.52/27.76          | ~ (v1_funct_1 @ sk_C)
% 27.52/27.76          | ~ (v1_relat_1 @ X0)
% 27.52/27.76          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 27.52/27.76              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 27.52/27.76                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 27.52/27.76      inference('sup-', [status(thm)], ['186', '202'])).
% 27.52/27.76  thf('204', plain, ((v1_relat_1 @ sk_C)),
% 27.52/27.76      inference('sup-', [status(thm)], ['63', '64'])).
% 27.52/27.76  thf('205', plain, ((v1_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('206', plain,
% 27.52/27.76      (![X0 : $i]:
% 27.52/27.76         (~ (v1_relat_1 @ X0)
% 27.52/27.76          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 27.52/27.76              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 27.52/27.76                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 27.52/27.76      inference('demod', [status(thm)], ['203', '204', '205'])).
% 27.52/27.76  thf('207', plain,
% 27.52/27.76      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 27.52/27.76          (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 27.52/27.76          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 27.52/27.76        | ~ (v1_relat_1 @ sk_C)
% 27.52/27.76        | ~ (v1_funct_1 @ sk_C)
% 27.52/27.76        | ~ (v2_funct_1 @ sk_C)
% 27.52/27.76        | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 27.52/27.76      inference('sup+', [status(thm)], ['185', '206'])).
% 27.52/27.76  thf('208', plain,
% 27.52/27.76      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 27.52/27.76         = (k2_funct_1 @ sk_C))),
% 27.52/27.76      inference('demod', [status(thm)], ['194', '195', '196', '197'])).
% 27.52/27.76  thf('209', plain, ((v1_relat_1 @ sk_C)),
% 27.52/27.76      inference('sup-', [status(thm)], ['63', '64'])).
% 27.52/27.76  thf('210', plain, ((v1_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('211', plain, ((v2_funct_1 @ sk_C)),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('212', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 27.52/27.76      inference('sup-', [status(thm)], ['73', '74'])).
% 27.52/27.76  thf('213', plain,
% 27.52/27.76      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 27.52/27.76         = (k2_funct_1 @ sk_C))),
% 27.52/27.76      inference('demod', [status(thm)],
% 27.52/27.76                ['207', '208', '209', '210', '211', '212'])).
% 27.52/27.76  thf('214', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 27.52/27.76      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 27.52/27.76  thf('215', plain,
% 27.52/27.76      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 27.52/27.76         = (k2_funct_1 @ sk_C))),
% 27.52/27.76      inference('demod', [status(thm)], ['213', '214'])).
% 27.52/27.76  thf('216', plain, ((v1_relat_1 @ sk_D)),
% 27.52/27.76      inference('sup-', [status(thm)], ['141', '142'])).
% 27.52/27.76  thf('217', plain,
% 27.52/27.76      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 27.52/27.76      inference('demod', [status(thm)], ['179', '215', '216'])).
% 27.52/27.76  thf('218', plain, ((v1_relat_1 @ sk_D)),
% 27.52/27.76      inference('sup-', [status(thm)], ['141', '142'])).
% 27.52/27.76  thf('219', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 27.52/27.76      inference('demod', [status(thm)], ['148', '217', '218'])).
% 27.52/27.76  thf('220', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 27.52/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.52/27.76  thf('221', plain, ($false),
% 27.52/27.76      inference('simplify_reflect-', [status(thm)], ['219', '220'])).
% 27.52/27.76  
% 27.52/27.76  % SZS output end Refutation
% 27.52/27.76  
% 27.52/27.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
