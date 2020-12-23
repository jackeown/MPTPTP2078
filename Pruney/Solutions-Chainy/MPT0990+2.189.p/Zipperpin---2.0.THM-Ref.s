%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3Z4iJMwcZj

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:27 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  248 (5038 expanded)
%              Number of leaves         :   45 (1479 expanded)
%              Depth                    :   27
%              Number of atoms          : 2575 (138091 expanded)
%              Number of equality atoms :  211 (9364 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
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
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('26',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A_1 ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( ( k5_relat_1 @ X11 @ X12 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('31',plain,
    ( ( ( k6_relat_1 @ sk_A_1 )
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
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('33',plain,(
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

thf('34',plain,(
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

thf('35',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_relat_1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A_1 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
      = sk_A_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['41','44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k6_relat_1 @ sk_A_1 )
     != ( k6_relat_1 @ sk_A_1 ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','48','53','54','59','60','65'])).

thf('67',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('69',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('70',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
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

thf('72',plain,(
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

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A_1 ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('78',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('79',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['77','78','79','80','81','82'])).

thf('84',plain,
    ( ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('86',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v2_funct_1 @ X40 )
      | ~ ( zip_tseitin_0 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('90',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['67','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
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

thf('93',plain,(
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

thf('94',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_relat_1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('98',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('101',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['41','44','45','46','47'])).

thf('104',plain,
    ( ( sk_A_1 != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['88','89'])).

thf('107',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('108',plain,(
    ! [X51: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('109',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X51: $i] :
      ( ( v1_funct_2 @ X51 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('112',plain,(
    ! [X51: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('113',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_relat_1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('120',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['107','121'])).

thf('123',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['41','44','45','46','47'])).

thf('125',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['88','89'])).

thf('126',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('127',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','123','124','125','126','127'])).

thf('129',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['91','130'])).

thf('132',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('134',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( ( k5_relat_1 @ X11 @ X12 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['132','136'])).

thf('138',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['128','129'])).

thf('140',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['131'])).

thf('141',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('142',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('144',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['88','89'])).

thf('145',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['41','44','45','46','47'])).

thf('146',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['131'])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('148',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['131'])).

thf('149',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['41','44','45','46','47'])).

thf('151',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['131'])).

thf('152',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('154',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('156',plain,(
    ! [X51: $i] :
      ( ( v1_funct_2 @ X51 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('157',plain,
    ( ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('164',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('165',plain,(
    ! [X51: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('166',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('171',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('173',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('175',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_relat_1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('178',plain,
    ( ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A_1 ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['178','179','180','181','182'])).

thf('184',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A_1 ) ),
    inference('simplify_reflect-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('188',plain,
    ( ( sk_B != sk_B )
    | ( ( k6_relat_1 @ sk_A_1 )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['154','160','161','162','163','173','174','175','186','187'])).

thf('189',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k6_relat_1 @ sk_A_1 )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( k6_relat_1 @ sk_A_1 )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('193',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A_1 ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('195',plain,
    ( sk_A_1
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['131'])).

thf('197',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_A_1 != sk_A_1 )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141','142','143','144','145','146','147','148','149','150','151','195','196'])).

thf('198',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['198','199','200'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3Z4iJMwcZj
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:01:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.13/2.34  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.13/2.34  % Solved by: fo/fo7.sh
% 2.13/2.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.13/2.34  % done 1906 iterations in 1.878s
% 2.13/2.34  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.13/2.34  % SZS output start Refutation
% 2.13/2.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.13/2.34  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.13/2.34  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.13/2.34  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.13/2.34  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.13/2.34  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.13/2.34  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 2.13/2.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.13/2.34  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.13/2.34  thf(sk_D_type, type, sk_D: $i).
% 2.13/2.34  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.13/2.34  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.13/2.34  thf(sk_C_type, type, sk_C: $i).
% 2.13/2.34  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.13/2.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.13/2.34  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.13/2.34  thf(sk_A_1_type, type, sk_A_1: $i).
% 2.13/2.34  thf(sk_B_type, type, sk_B: $i).
% 2.13/2.34  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.13/2.34  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.13/2.34  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.13/2.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.13/2.34  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.13/2.34  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.13/2.34  thf(t36_funct_2, conjecture,
% 2.13/2.34    (![A:$i,B:$i,C:$i]:
% 2.13/2.34     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.13/2.34         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.13/2.34       ( ![D:$i]:
% 2.13/2.34         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.13/2.34             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.13/2.34           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.13/2.34               ( r2_relset_1 @
% 2.13/2.34                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.13/2.34                 ( k6_partfun1 @ A ) ) & 
% 2.13/2.34               ( v2_funct_1 @ C ) ) =>
% 2.13/2.34             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.13/2.34               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.13/2.34  thf(zf_stmt_0, negated_conjecture,
% 2.13/2.34    (~( ![A:$i,B:$i,C:$i]:
% 2.13/2.34        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.13/2.34            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.13/2.34          ( ![D:$i]:
% 2.13/2.34            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.13/2.34                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.13/2.34              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.13/2.34                  ( r2_relset_1 @
% 2.13/2.34                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.13/2.34                    ( k6_partfun1 @ A ) ) & 
% 2.13/2.34                  ( v2_funct_1 @ C ) ) =>
% 2.13/2.34                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.13/2.34                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.13/2.34    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.13/2.34  thf('0', plain,
% 2.13/2.34      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 2.13/2.34        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 2.13/2.34        (k6_partfun1 @ sk_A_1))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf(redefinition_k6_partfun1, axiom,
% 2.13/2.34    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.13/2.34  thf('1', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 2.13/2.34      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.13/2.34  thf('2', plain,
% 2.13/2.34      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 2.13/2.34        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 2.13/2.34        (k6_relat_1 @ sk_A_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['0', '1'])).
% 2.13/2.34  thf('3', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('4', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf(redefinition_k1_partfun1, axiom,
% 2.13/2.34    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.13/2.34     ( ( ( v1_funct_1 @ E ) & 
% 2.13/2.34         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.13/2.34         ( v1_funct_1 @ F ) & 
% 2.13/2.34         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.13/2.34       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.13/2.34  thf('5', plain,
% 2.13/2.34      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.13/2.34         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.13/2.34          | ~ (v1_funct_1 @ X28)
% 2.13/2.34          | ~ (v1_funct_1 @ X31)
% 2.13/2.34          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 2.13/2.34          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 2.13/2.34              = (k5_relat_1 @ X28 @ X31)))),
% 2.13/2.34      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.13/2.34  thf('6', plain,
% 2.13/2.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.34         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.13/2.34            = (k5_relat_1 @ sk_C @ X0))
% 2.13/2.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.13/2.34          | ~ (v1_funct_1 @ X0)
% 2.13/2.34          | ~ (v1_funct_1 @ sk_C))),
% 2.13/2.34      inference('sup-', [status(thm)], ['4', '5'])).
% 2.13/2.34  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('8', plain,
% 2.13/2.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.34         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.13/2.34            = (k5_relat_1 @ sk_C @ X0))
% 2.13/2.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.13/2.34          | ~ (v1_funct_1 @ X0))),
% 2.13/2.34      inference('demod', [status(thm)], ['6', '7'])).
% 2.13/2.34  thf('9', plain,
% 2.13/2.34      ((~ (v1_funct_1 @ sk_D)
% 2.13/2.34        | ((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 2.13/2.34            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['3', '8'])).
% 2.13/2.34  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('11', plain,
% 2.13/2.34      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 2.13/2.34         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.13/2.34      inference('demod', [status(thm)], ['9', '10'])).
% 2.13/2.34  thf('12', plain,
% 2.13/2.34      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.13/2.34        (k6_relat_1 @ sk_A_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['2', '11'])).
% 2.13/2.34  thf('13', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('14', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf(dt_k1_partfun1, axiom,
% 2.13/2.34    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.13/2.34     ( ( ( v1_funct_1 @ E ) & 
% 2.13/2.34         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.13/2.34         ( v1_funct_1 @ F ) & 
% 2.13/2.34         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.13/2.34       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.13/2.34         ( m1_subset_1 @
% 2.13/2.34           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.13/2.34           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.13/2.34  thf('15', plain,
% 2.13/2.34      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.13/2.34         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 2.13/2.34          | ~ (v1_funct_1 @ X20)
% 2.13/2.34          | ~ (v1_funct_1 @ X23)
% 2.13/2.35          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 2.13/2.35          | (m1_subset_1 @ (k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23) @ 
% 2.13/2.35             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X25))))),
% 2.13/2.35      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.13/2.35  thf('16', plain,
% 2.13/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.35         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.13/2.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 2.13/2.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.13/2.35          | ~ (v1_funct_1 @ X1)
% 2.13/2.35          | ~ (v1_funct_1 @ sk_C))),
% 2.13/2.35      inference('sup-', [status(thm)], ['14', '15'])).
% 2.13/2.35  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('18', plain,
% 2.13/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.35         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.13/2.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 2.13/2.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.13/2.35          | ~ (v1_funct_1 @ X1))),
% 2.13/2.35      inference('demod', [status(thm)], ['16', '17'])).
% 2.13/2.35  thf('19', plain,
% 2.13/2.35      ((~ (v1_funct_1 @ sk_D)
% 2.13/2.35        | (m1_subset_1 @ 
% 2.13/2.35           (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 2.13/2.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 2.13/2.35      inference('sup-', [status(thm)], ['13', '18'])).
% 2.13/2.35  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('21', plain,
% 2.13/2.35      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 2.13/2.35         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.13/2.35      inference('demod', [status(thm)], ['9', '10'])).
% 2.13/2.35  thf('22', plain,
% 2.13/2.35      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.13/2.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))),
% 2.13/2.35      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.13/2.35  thf(redefinition_r2_relset_1, axiom,
% 2.13/2.35    (![A:$i,B:$i,C:$i,D:$i]:
% 2.13/2.35     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.13/2.35         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.13/2.35       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.13/2.35  thf('23', plain,
% 2.13/2.35      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 2.13/2.35         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 2.13/2.35          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 2.13/2.35          | ((X16) = (X19))
% 2.13/2.35          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 2.13/2.35      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.13/2.35  thf('24', plain,
% 2.13/2.35      (![X0 : $i]:
% 2.13/2.35         (~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 2.13/2.35          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 2.13/2.35          | ~ (m1_subset_1 @ X0 @ 
% 2.13/2.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 2.13/2.35      inference('sup-', [status(thm)], ['22', '23'])).
% 2.13/2.35  thf('25', plain,
% 2.13/2.35      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A_1) @ 
% 2.13/2.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))
% 2.13/2.35        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A_1)))),
% 2.13/2.35      inference('sup-', [status(thm)], ['12', '24'])).
% 2.13/2.35  thf(dt_k6_partfun1, axiom,
% 2.13/2.35    (![A:$i]:
% 2.13/2.35     ( ( m1_subset_1 @
% 2.13/2.35         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.13/2.35       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.13/2.35  thf('26', plain,
% 2.13/2.35      (![X27 : $i]:
% 2.13/2.35         (m1_subset_1 @ (k6_partfun1 @ X27) @ 
% 2.13/2.35          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 2.13/2.35      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.13/2.35  thf('27', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 2.13/2.35      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.13/2.35  thf('28', plain,
% 2.13/2.35      (![X27 : $i]:
% 2.13/2.35         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 2.13/2.35          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 2.13/2.35      inference('demod', [status(thm)], ['26', '27'])).
% 2.13/2.35  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A_1))),
% 2.13/2.35      inference('demod', [status(thm)], ['25', '28'])).
% 2.13/2.35  thf(t64_funct_1, axiom,
% 2.13/2.35    (![A:$i]:
% 2.13/2.35     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.13/2.35       ( ![B:$i]:
% 2.13/2.35         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.13/2.35           ( ( ( v2_funct_1 @ A ) & 
% 2.13/2.35               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 2.13/2.35               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 2.13/2.35             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.13/2.35  thf('30', plain,
% 2.13/2.35      (![X11 : $i, X12 : $i]:
% 2.13/2.35         (~ (v1_relat_1 @ X11)
% 2.13/2.35          | ~ (v1_funct_1 @ X11)
% 2.13/2.35          | ((X11) = (k2_funct_1 @ X12))
% 2.13/2.35          | ((k5_relat_1 @ X11 @ X12) != (k6_relat_1 @ (k2_relat_1 @ X12)))
% 2.13/2.35          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X12))
% 2.13/2.35          | ~ (v2_funct_1 @ X12)
% 2.13/2.35          | ~ (v1_funct_1 @ X12)
% 2.13/2.35          | ~ (v1_relat_1 @ X12))),
% 2.13/2.35      inference('cnf', [status(esa)], [t64_funct_1])).
% 2.13/2.35  thf('31', plain,
% 2.13/2.35      ((((k6_relat_1 @ sk_A_1) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 2.13/2.35        | ~ (v1_relat_1 @ sk_D)
% 2.13/2.35        | ~ (v1_funct_1 @ sk_D)
% 2.13/2.35        | ~ (v2_funct_1 @ sk_D)
% 2.13/2.35        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 2.13/2.35        | ((sk_C) = (k2_funct_1 @ sk_D))
% 2.13/2.35        | ~ (v1_funct_1 @ sk_C)
% 2.13/2.35        | ~ (v1_relat_1 @ sk_C))),
% 2.13/2.35      inference('sup-', [status(thm)], ['29', '30'])).
% 2.13/2.35  thf('32', plain,
% 2.13/2.35      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 2.13/2.35        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 2.13/2.35        (k6_relat_1 @ sk_A_1))),
% 2.13/2.35      inference('demod', [status(thm)], ['0', '1'])).
% 2.13/2.35  thf('33', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf(t24_funct_2, axiom,
% 2.13/2.35    (![A:$i,B:$i,C:$i]:
% 2.13/2.35     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.13/2.35         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.13/2.35       ( ![D:$i]:
% 2.13/2.35         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.13/2.35             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.13/2.35           ( ( r2_relset_1 @
% 2.13/2.35               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.13/2.35               ( k6_partfun1 @ B ) ) =>
% 2.13/2.35             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.13/2.35  thf('34', plain,
% 2.13/2.35      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 2.13/2.35         (~ (v1_funct_1 @ X35)
% 2.13/2.35          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 2.13/2.35          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 2.13/2.35          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 2.13/2.35               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 2.13/2.35               (k6_partfun1 @ X36))
% 2.13/2.35          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 2.13/2.35          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 2.13/2.35          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 2.13/2.35          | ~ (v1_funct_1 @ X38))),
% 2.13/2.35      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.13/2.35  thf('35', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 2.13/2.35      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.13/2.35  thf('36', plain,
% 2.13/2.35      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 2.13/2.35         (~ (v1_funct_1 @ X35)
% 2.13/2.35          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 2.13/2.35          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 2.13/2.35          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 2.13/2.35               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 2.13/2.35               (k6_relat_1 @ X36))
% 2.13/2.35          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 2.13/2.35          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 2.13/2.35          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 2.13/2.35          | ~ (v1_funct_1 @ X38))),
% 2.13/2.35      inference('demod', [status(thm)], ['34', '35'])).
% 2.13/2.35  thf('37', plain,
% 2.13/2.35      (![X0 : $i]:
% 2.13/2.35         (~ (v1_funct_1 @ X0)
% 2.13/2.35          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 2.13/2.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 2.13/2.35          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 2.13/2.35          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 2.13/2.35               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 2.13/2.35               (k6_relat_1 @ sk_A_1))
% 2.13/2.35          | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 2.13/2.35          | ~ (v1_funct_1 @ sk_C))),
% 2.13/2.35      inference('sup-', [status(thm)], ['33', '36'])).
% 2.13/2.35  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('40', plain,
% 2.13/2.35      (![X0 : $i]:
% 2.13/2.35         (~ (v1_funct_1 @ X0)
% 2.13/2.35          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 2.13/2.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 2.13/2.35          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 2.13/2.35          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 2.13/2.35               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 2.13/2.35               (k6_relat_1 @ sk_A_1)))),
% 2.13/2.35      inference('demod', [status(thm)], ['37', '38', '39'])).
% 2.13/2.35  thf('41', plain,
% 2.13/2.35      ((((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (sk_A_1))
% 2.13/2.35        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 2.13/2.35        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 2.13/2.35        | ~ (v1_funct_1 @ sk_D))),
% 2.13/2.35      inference('sup-', [status(thm)], ['32', '40'])).
% 2.13/2.35  thf('42', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf(redefinition_k2_relset_1, axiom,
% 2.13/2.35    (![A:$i,B:$i,C:$i]:
% 2.13/2.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.13/2.35       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.13/2.35  thf('43', plain,
% 2.13/2.35      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.13/2.35         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 2.13/2.35          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.13/2.35      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.13/2.35  thf('44', plain,
% 2.13/2.35      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.13/2.35      inference('sup-', [status(thm)], ['42', '43'])).
% 2.13/2.35  thf('45', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 2.13/2.35      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 2.13/2.35  thf('49', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf(cc2_relat_1, axiom,
% 2.13/2.35    (![A:$i]:
% 2.13/2.35     ( ( v1_relat_1 @ A ) =>
% 2.13/2.35       ( ![B:$i]:
% 2.13/2.35         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.13/2.35  thf('50', plain,
% 2.13/2.35      (![X3 : $i, X4 : $i]:
% 2.13/2.35         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.13/2.35          | (v1_relat_1 @ X3)
% 2.13/2.35          | ~ (v1_relat_1 @ X4))),
% 2.13/2.35      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.13/2.35  thf('51', plain,
% 2.13/2.35      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)) | (v1_relat_1 @ sk_D))),
% 2.13/2.35      inference('sup-', [status(thm)], ['49', '50'])).
% 2.13/2.35  thf(fc6_relat_1, axiom,
% 2.13/2.35    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.13/2.35  thf('52', plain,
% 2.13/2.35      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 2.13/2.35      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.13/2.35  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 2.13/2.35      inference('demod', [status(thm)], ['51', '52'])).
% 2.13/2.35  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('55', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('56', plain,
% 2.13/2.35      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.13/2.35         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 2.13/2.35          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.13/2.35      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.13/2.35  thf('57', plain,
% 2.13/2.35      (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.13/2.35      inference('sup-', [status(thm)], ['55', '56'])).
% 2.13/2.35  thf('58', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('59', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.13/2.35      inference('sup+', [status(thm)], ['57', '58'])).
% 2.13/2.35  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('61', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('62', plain,
% 2.13/2.35      (![X3 : $i, X4 : $i]:
% 2.13/2.35         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.13/2.35          | (v1_relat_1 @ X3)
% 2.13/2.35          | ~ (v1_relat_1 @ X4))),
% 2.13/2.35      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.13/2.35  thf('63', plain,
% 2.13/2.35      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.13/2.35      inference('sup-', [status(thm)], ['61', '62'])).
% 2.13/2.35  thf('64', plain,
% 2.13/2.35      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 2.13/2.35      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.13/2.35  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 2.13/2.35      inference('demod', [status(thm)], ['63', '64'])).
% 2.13/2.35  thf('66', plain,
% 2.13/2.35      ((((k6_relat_1 @ sk_A_1) != (k6_relat_1 @ sk_A_1))
% 2.13/2.35        | ~ (v2_funct_1 @ sk_D)
% 2.13/2.35        | ((sk_B) != (k1_relat_1 @ sk_D))
% 2.13/2.35        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 2.13/2.35      inference('demod', [status(thm)],
% 2.13/2.35                ['31', '48', '53', '54', '59', '60', '65'])).
% 2.13/2.35  thf('67', plain,
% 2.13/2.35      ((((sk_C) = (k2_funct_1 @ sk_D))
% 2.13/2.35        | ((sk_B) != (k1_relat_1 @ sk_D))
% 2.13/2.35        | ~ (v2_funct_1 @ sk_D))),
% 2.13/2.35      inference('simplify', [status(thm)], ['66'])).
% 2.13/2.35  thf('68', plain,
% 2.13/2.35      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 2.13/2.35         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.13/2.35      inference('demod', [status(thm)], ['9', '10'])).
% 2.13/2.35  thf('69', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A_1))),
% 2.13/2.35      inference('demod', [status(thm)], ['25', '28'])).
% 2.13/2.35  thf('70', plain,
% 2.13/2.35      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 2.13/2.35         = (k6_relat_1 @ sk_A_1))),
% 2.13/2.35      inference('demod', [status(thm)], ['68', '69'])).
% 2.13/2.35  thf('71', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf(t30_funct_2, axiom,
% 2.13/2.35    (![A:$i,B:$i,C:$i,D:$i]:
% 2.13/2.35     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.13/2.35         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 2.13/2.35       ( ![E:$i]:
% 2.13/2.35         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 2.13/2.35             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 2.13/2.35           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.13/2.35               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 2.13/2.35             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 2.13/2.35               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 2.13/2.35  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 2.13/2.35  thf(zf_stmt_2, axiom,
% 2.13/2.35    (![C:$i,B:$i]:
% 2.13/2.35     ( ( zip_tseitin_1 @ C @ B ) =>
% 2.13/2.35       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 2.13/2.35  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.13/2.35  thf(zf_stmt_4, axiom,
% 2.13/2.35    (![E:$i,D:$i]:
% 2.13/2.35     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 2.13/2.35  thf(zf_stmt_5, axiom,
% 2.13/2.35    (![A:$i,B:$i,C:$i,D:$i]:
% 2.13/2.35     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.13/2.35         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.13/2.35       ( ![E:$i]:
% 2.13/2.35         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.13/2.35             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.13/2.35           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 2.13/2.35               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 2.13/2.35             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 2.13/2.35  thf('72', plain,
% 2.13/2.35      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 2.13/2.35         (~ (v1_funct_1 @ X43)
% 2.13/2.35          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 2.13/2.35          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.13/2.35          | (zip_tseitin_0 @ X43 @ X46)
% 2.13/2.35          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43))
% 2.13/2.35          | (zip_tseitin_1 @ X45 @ X44)
% 2.13/2.35          | ((k2_relset_1 @ X47 @ X44 @ X46) != (X44))
% 2.13/2.35          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X44)))
% 2.13/2.35          | ~ (v1_funct_2 @ X46 @ X47 @ X44)
% 2.13/2.35          | ~ (v1_funct_1 @ X46))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.13/2.35  thf('73', plain,
% 2.13/2.35      (![X0 : $i, X1 : $i]:
% 2.13/2.35         (~ (v1_funct_1 @ X0)
% 2.13/2.35          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.13/2.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.13/2.35          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.13/2.35          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 2.13/2.35          | ~ (v2_funct_1 @ 
% 2.13/2.35               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 2.13/2.35          | (zip_tseitin_0 @ sk_D @ X0)
% 2.13/2.35          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 2.13/2.35          | ~ (v1_funct_1 @ sk_D))),
% 2.13/2.35      inference('sup-', [status(thm)], ['71', '72'])).
% 2.13/2.35  thf('74', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('76', plain,
% 2.13/2.35      (![X0 : $i, X1 : $i]:
% 2.13/2.35         (~ (v1_funct_1 @ X0)
% 2.13/2.35          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.13/2.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.13/2.35          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.13/2.35          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 2.13/2.35          | ~ (v2_funct_1 @ 
% 2.13/2.35               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 2.13/2.35          | (zip_tseitin_0 @ sk_D @ X0))),
% 2.13/2.35      inference('demod', [status(thm)], ['73', '74', '75'])).
% 2.13/2.35  thf('77', plain,
% 2.13/2.35      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A_1))
% 2.13/2.35        | (zip_tseitin_0 @ sk_D @ sk_C)
% 2.13/2.35        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 2.13/2.35        | ((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 2.13/2.35        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 2.13/2.35        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 2.13/2.35        | ~ (v1_funct_1 @ sk_C))),
% 2.13/2.35      inference('sup-', [status(thm)], ['70', '76'])).
% 2.13/2.35  thf(fc4_funct_1, axiom,
% 2.13/2.35    (![A:$i]:
% 2.13/2.35     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.13/2.35       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.13/2.35  thf('78', plain, (![X10 : $i]: (v2_funct_1 @ (k6_relat_1 @ X10))),
% 2.13/2.35      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.13/2.35  thf('79', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('80', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('81', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('83', plain,
% 2.13/2.35      (((zip_tseitin_0 @ sk_D @ sk_C)
% 2.13/2.35        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 2.13/2.35        | ((sk_B) != (sk_B)))),
% 2.13/2.35      inference('demod', [status(thm)], ['77', '78', '79', '80', '81', '82'])).
% 2.13/2.35  thf('84', plain,
% 2.13/2.35      (((zip_tseitin_1 @ sk_A_1 @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 2.13/2.35      inference('simplify', [status(thm)], ['83'])).
% 2.13/2.35  thf('85', plain,
% 2.13/2.35      (![X41 : $i, X42 : $i]:
% 2.13/2.35         (((X41) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X41 @ X42))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.13/2.35  thf('86', plain,
% 2.13/2.35      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A_1) = (k1_xboole_0)))),
% 2.13/2.35      inference('sup-', [status(thm)], ['84', '85'])).
% 2.13/2.35  thf('87', plain, (((sk_A_1) != (k1_xboole_0))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('88', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 2.13/2.35      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 2.13/2.35  thf('89', plain,
% 2.13/2.35      (![X39 : $i, X40 : $i]:
% 2.13/2.35         ((v2_funct_1 @ X40) | ~ (zip_tseitin_0 @ X40 @ X39))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.13/2.35  thf('90', plain, ((v2_funct_1 @ sk_D)),
% 2.13/2.35      inference('sup-', [status(thm)], ['88', '89'])).
% 2.13/2.35  thf('91', plain,
% 2.13/2.35      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 2.13/2.35      inference('demod', [status(thm)], ['67', '90'])).
% 2.13/2.35  thf('92', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf(t35_funct_2, axiom,
% 2.13/2.35    (![A:$i,B:$i,C:$i]:
% 2.13/2.35     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.13/2.35         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.13/2.35       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.13/2.35         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.13/2.35           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.13/2.35             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.13/2.35  thf('93', plain,
% 2.13/2.35      (![X48 : $i, X49 : $i, X50 : $i]:
% 2.13/2.35         (((X48) = (k1_xboole_0))
% 2.13/2.35          | ~ (v1_funct_1 @ X49)
% 2.13/2.35          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 2.13/2.35          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 2.13/2.35          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_partfun1 @ X50))
% 2.13/2.35          | ~ (v2_funct_1 @ X49)
% 2.13/2.35          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 2.13/2.35      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.13/2.35  thf('94', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 2.13/2.35      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.13/2.35  thf('95', plain,
% 2.13/2.35      (![X48 : $i, X49 : $i, X50 : $i]:
% 2.13/2.35         (((X48) = (k1_xboole_0))
% 2.13/2.35          | ~ (v1_funct_1 @ X49)
% 2.13/2.35          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 2.13/2.35          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 2.13/2.35          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_relat_1 @ X50))
% 2.13/2.35          | ~ (v2_funct_1 @ X49)
% 2.13/2.35          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 2.13/2.35      inference('demod', [status(thm)], ['93', '94'])).
% 2.13/2.35  thf('96', plain,
% 2.13/2.35      ((((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) != (sk_A_1))
% 2.13/2.35        | ~ (v2_funct_1 @ sk_D)
% 2.13/2.35        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.13/2.35        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 2.13/2.35        | ~ (v1_funct_1 @ sk_D)
% 2.13/2.35        | ((sk_A_1) = (k1_xboole_0)))),
% 2.13/2.35      inference('sup-', [status(thm)], ['92', '95'])).
% 2.13/2.35  thf('97', plain,
% 2.13/2.35      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.13/2.35      inference('sup-', [status(thm)], ['42', '43'])).
% 2.13/2.35  thf('98', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('99', plain, ((v1_funct_1 @ sk_D)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('100', plain,
% 2.13/2.35      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 2.13/2.35        | ~ (v2_funct_1 @ sk_D)
% 2.13/2.35        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.13/2.35        | ((sk_A_1) = (k1_xboole_0)))),
% 2.13/2.35      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 2.13/2.35  thf('101', plain, (((sk_A_1) != (k1_xboole_0))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('102', plain,
% 2.13/2.35      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 2.13/2.35        | ~ (v2_funct_1 @ sk_D)
% 2.13/2.35        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 2.13/2.35      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 2.13/2.35  thf('103', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 2.13/2.35      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 2.13/2.35  thf('104', plain,
% 2.13/2.35      ((((sk_A_1) != (sk_A_1))
% 2.13/2.35        | ~ (v2_funct_1 @ sk_D)
% 2.13/2.35        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 2.13/2.35      inference('demod', [status(thm)], ['102', '103'])).
% 2.13/2.35  thf('105', plain,
% 2.13/2.35      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.13/2.35        | ~ (v2_funct_1 @ sk_D))),
% 2.13/2.35      inference('simplify', [status(thm)], ['104'])).
% 2.13/2.35  thf('106', plain, ((v2_funct_1 @ sk_D)),
% 2.13/2.35      inference('sup-', [status(thm)], ['88', '89'])).
% 2.13/2.35  thf('107', plain,
% 2.13/2.35      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 2.13/2.35      inference('demod', [status(thm)], ['105', '106'])).
% 2.13/2.35  thf(t3_funct_2, axiom,
% 2.13/2.35    (![A:$i]:
% 2.13/2.35     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.13/2.35       ( ( v1_funct_1 @ A ) & 
% 2.13/2.35         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 2.13/2.35         ( m1_subset_1 @
% 2.13/2.35           A @ 
% 2.13/2.35           ( k1_zfmisc_1 @
% 2.13/2.35             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.13/2.35  thf('108', plain,
% 2.13/2.35      (![X51 : $i]:
% 2.13/2.35         ((m1_subset_1 @ X51 @ 
% 2.13/2.35           (k1_zfmisc_1 @ 
% 2.13/2.35            (k2_zfmisc_1 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51))))
% 2.13/2.35          | ~ (v1_funct_1 @ X51)
% 2.13/2.35          | ~ (v1_relat_1 @ X51))),
% 2.13/2.35      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.13/2.35  thf('109', plain,
% 2.13/2.35      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.13/2.35         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 2.13/2.35          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.13/2.35      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.13/2.35  thf('110', plain,
% 2.13/2.35      (![X0 : $i]:
% 2.13/2.35         (~ (v1_relat_1 @ X0)
% 2.13/2.35          | ~ (v1_funct_1 @ X0)
% 2.13/2.35          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.13/2.35              = (k2_relat_1 @ X0)))),
% 2.13/2.35      inference('sup-', [status(thm)], ['108', '109'])).
% 2.13/2.35  thf('111', plain,
% 2.13/2.35      (![X51 : $i]:
% 2.13/2.35         ((v1_funct_2 @ X51 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51))
% 2.13/2.35          | ~ (v1_funct_1 @ X51)
% 2.13/2.35          | ~ (v1_relat_1 @ X51))),
% 2.13/2.35      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.13/2.35  thf('112', plain,
% 2.13/2.35      (![X51 : $i]:
% 2.13/2.35         ((m1_subset_1 @ X51 @ 
% 2.13/2.35           (k1_zfmisc_1 @ 
% 2.13/2.35            (k2_zfmisc_1 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51))))
% 2.13/2.35          | ~ (v1_funct_1 @ X51)
% 2.13/2.35          | ~ (v1_relat_1 @ X51))),
% 2.13/2.35      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.13/2.35  thf('113', plain,
% 2.13/2.35      (![X48 : $i, X49 : $i, X50 : $i]:
% 2.13/2.35         (((X48) = (k1_xboole_0))
% 2.13/2.35          | ~ (v1_funct_1 @ X49)
% 2.13/2.35          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 2.13/2.35          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 2.13/2.35          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_relat_1 @ X50))
% 2.13/2.35          | ~ (v2_funct_1 @ X49)
% 2.13/2.35          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 2.13/2.35      inference('demod', [status(thm)], ['93', '94'])).
% 2.13/2.35  thf('114', plain,
% 2.13/2.35      (![X0 : $i]:
% 2.13/2.35         (~ (v1_relat_1 @ X0)
% 2.13/2.35          | ~ (v1_funct_1 @ X0)
% 2.13/2.35          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.13/2.35              != (k2_relat_1 @ X0))
% 2.13/2.35          | ~ (v2_funct_1 @ X0)
% 2.13/2.35          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 2.13/2.35              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.35          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 2.13/2.35          | ~ (v1_funct_1 @ X0)
% 2.13/2.35          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 2.13/2.35      inference('sup-', [status(thm)], ['112', '113'])).
% 2.13/2.35  thf('115', plain,
% 2.13/2.35      (![X0 : $i]:
% 2.13/2.35         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 2.13/2.35          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 2.13/2.35          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 2.13/2.35              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.35          | ~ (v2_funct_1 @ X0)
% 2.13/2.35          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.13/2.35              != (k2_relat_1 @ X0))
% 2.13/2.35          | ~ (v1_funct_1 @ X0)
% 2.13/2.35          | ~ (v1_relat_1 @ X0))),
% 2.13/2.35      inference('simplify', [status(thm)], ['114'])).
% 2.13/2.35  thf('116', plain,
% 2.13/2.35      (![X0 : $i]:
% 2.13/2.35         (~ (v1_relat_1 @ X0)
% 2.13/2.35          | ~ (v1_funct_1 @ X0)
% 2.13/2.35          | ~ (v1_relat_1 @ X0)
% 2.13/2.35          | ~ (v1_funct_1 @ X0)
% 2.13/2.35          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.13/2.35              != (k2_relat_1 @ X0))
% 2.13/2.35          | ~ (v2_funct_1 @ X0)
% 2.13/2.35          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 2.13/2.35              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.35          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 2.13/2.35      inference('sup-', [status(thm)], ['111', '115'])).
% 2.13/2.35  thf('117', plain,
% 2.13/2.35      (![X0 : $i]:
% 2.13/2.35         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 2.13/2.35          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 2.13/2.35              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.35          | ~ (v2_funct_1 @ X0)
% 2.13/2.35          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.13/2.35              != (k2_relat_1 @ X0))
% 2.13/2.35          | ~ (v1_funct_1 @ X0)
% 2.13/2.35          | ~ (v1_relat_1 @ X0))),
% 2.13/2.35      inference('simplify', [status(thm)], ['116'])).
% 2.13/2.35  thf('118', plain,
% 2.13/2.35      (![X0 : $i]:
% 2.13/2.35         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 2.13/2.35          | ~ (v1_funct_1 @ X0)
% 2.13/2.35          | ~ (v1_relat_1 @ X0)
% 2.13/2.35          | ~ (v1_relat_1 @ X0)
% 2.13/2.35          | ~ (v1_funct_1 @ X0)
% 2.13/2.35          | ~ (v2_funct_1 @ X0)
% 2.13/2.35          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 2.13/2.35              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.35          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 2.13/2.35      inference('sup-', [status(thm)], ['110', '117'])).
% 2.13/2.35  thf('119', plain,
% 2.13/2.35      (![X0 : $i]:
% 2.13/2.35         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 2.13/2.35          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 2.13/2.35              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.35          | ~ (v2_funct_1 @ X0)
% 2.13/2.35          | ~ (v1_relat_1 @ X0)
% 2.13/2.35          | ~ (v1_funct_1 @ X0))),
% 2.13/2.35      inference('simplify', [status(thm)], ['118'])).
% 2.13/2.35  thf(t71_relat_1, axiom,
% 2.13/2.35    (![A:$i]:
% 2.13/2.35     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.13/2.35       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.13/2.35  thf('120', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 2.13/2.35      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.13/2.35  thf('121', plain,
% 2.13/2.35      (![X0 : $i]:
% 2.13/2.35         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 2.13/2.35            = (k1_relat_1 @ X0))
% 2.13/2.35          | ~ (v1_funct_1 @ X0)
% 2.13/2.35          | ~ (v1_relat_1 @ X0)
% 2.13/2.35          | ~ (v2_funct_1 @ X0)
% 2.13/2.35          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 2.13/2.35      inference('sup+', [status(thm)], ['119', '120'])).
% 2.13/2.35  thf('122', plain,
% 2.13/2.35      ((((k1_relat_1 @ (k6_relat_1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 2.13/2.35        | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 2.13/2.35        | ~ (v2_funct_1 @ sk_D)
% 2.13/2.35        | ~ (v1_relat_1 @ sk_D)
% 2.13/2.35        | ~ (v1_funct_1 @ sk_D))),
% 2.13/2.35      inference('sup+', [status(thm)], ['107', '121'])).
% 2.13/2.35  thf('123', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 2.13/2.35      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.13/2.35  thf('124', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 2.13/2.35      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 2.13/2.35  thf('125', plain, ((v2_funct_1 @ sk_D)),
% 2.13/2.35      inference('sup-', [status(thm)], ['88', '89'])).
% 2.13/2.35  thf('126', plain, ((v1_relat_1 @ sk_D)),
% 2.13/2.35      inference('demod', [status(thm)], ['51', '52'])).
% 2.13/2.35  thf('127', plain, ((v1_funct_1 @ sk_D)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('128', plain,
% 2.13/2.35      ((((sk_B) = (k1_relat_1 @ sk_D)) | ((sk_A_1) = (k1_xboole_0)))),
% 2.13/2.35      inference('demod', [status(thm)],
% 2.13/2.35                ['122', '123', '124', '125', '126', '127'])).
% 2.13/2.35  thf('129', plain, (((sk_A_1) != (k1_xboole_0))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('130', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.13/2.35      inference('simplify_reflect-', [status(thm)], ['128', '129'])).
% 2.13/2.35  thf('131', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 2.13/2.35      inference('demod', [status(thm)], ['91', '130'])).
% 2.13/2.35  thf('132', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 2.13/2.35      inference('simplify', [status(thm)], ['131'])).
% 2.13/2.35  thf('133', plain,
% 2.13/2.35      (![X0 : $i]:
% 2.13/2.35         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 2.13/2.35          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 2.13/2.35              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.35          | ~ (v2_funct_1 @ X0)
% 2.13/2.35          | ~ (v1_relat_1 @ X0)
% 2.13/2.35          | ~ (v1_funct_1 @ X0))),
% 2.13/2.35      inference('simplify', [status(thm)], ['118'])).
% 2.13/2.35  thf('134', plain,
% 2.13/2.35      (![X11 : $i, X12 : $i]:
% 2.13/2.35         (~ (v1_relat_1 @ X11)
% 2.13/2.35          | ~ (v1_funct_1 @ X11)
% 2.13/2.35          | ((X11) = (k2_funct_1 @ X12))
% 2.13/2.35          | ((k5_relat_1 @ X11 @ X12) != (k6_relat_1 @ (k2_relat_1 @ X12)))
% 2.13/2.35          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X12))
% 2.13/2.35          | ~ (v2_funct_1 @ X12)
% 2.13/2.35          | ~ (v1_funct_1 @ X12)
% 2.13/2.35          | ~ (v1_relat_1 @ X12))),
% 2.13/2.35      inference('cnf', [status(esa)], [t64_funct_1])).
% 2.13/2.35  thf('135', plain,
% 2.13/2.35      (![X0 : $i]:
% 2.13/2.35         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 2.13/2.35            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 2.13/2.35          | ~ (v1_funct_1 @ X0)
% 2.13/2.35          | ~ (v1_relat_1 @ X0)
% 2.13/2.35          | ~ (v2_funct_1 @ X0)
% 2.13/2.35          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 2.13/2.35          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.13/2.35          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.13/2.35          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 2.13/2.35          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.13/2.35          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 2.13/2.35          | ~ (v1_funct_1 @ X0)
% 2.13/2.35          | ~ (v1_relat_1 @ X0))),
% 2.13/2.35      inference('sup-', [status(thm)], ['133', '134'])).
% 2.13/2.35  thf('136', plain,
% 2.13/2.35      (![X0 : $i]:
% 2.13/2.35         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 2.13/2.35          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.13/2.35          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 2.13/2.35          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.13/2.35          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.13/2.35          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 2.13/2.35          | ~ (v2_funct_1 @ X0)
% 2.13/2.35          | ~ (v1_relat_1 @ X0)
% 2.13/2.35          | ~ (v1_funct_1 @ X0)
% 2.13/2.35          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 2.13/2.35              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 2.13/2.35      inference('simplify', [status(thm)], ['135'])).
% 2.13/2.35  thf('137', plain,
% 2.13/2.35      ((~ (v2_funct_1 @ sk_C)
% 2.13/2.35        | ((k6_relat_1 @ (k1_relat_1 @ sk_D))
% 2.13/2.35            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_D))))
% 2.13/2.35        | ~ (v1_funct_1 @ sk_D)
% 2.13/2.35        | ~ (v1_relat_1 @ sk_D)
% 2.13/2.35        | ~ (v2_funct_1 @ sk_D)
% 2.13/2.35        | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 2.13/2.35        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 2.13/2.35        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 2.13/2.35        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 2.13/2.35        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 2.13/2.35      inference('sup-', [status(thm)], ['132', '136'])).
% 2.13/2.35  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('139', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.13/2.35      inference('simplify_reflect-', [status(thm)], ['128', '129'])).
% 2.13/2.35  thf('140', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 2.13/2.35      inference('simplify', [status(thm)], ['131'])).
% 2.13/2.35  thf('141', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.13/2.35      inference('sup+', [status(thm)], ['57', '58'])).
% 2.13/2.35  thf('142', plain, ((v1_funct_1 @ sk_D)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('143', plain, ((v1_relat_1 @ sk_D)),
% 2.13/2.35      inference('demod', [status(thm)], ['51', '52'])).
% 2.13/2.35  thf('144', plain, ((v2_funct_1 @ sk_D)),
% 2.13/2.35      inference('sup-', [status(thm)], ['88', '89'])).
% 2.13/2.35  thf('145', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 2.13/2.35      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 2.13/2.35  thf('146', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 2.13/2.35      inference('simplify', [status(thm)], ['131'])).
% 2.13/2.35  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 2.13/2.35      inference('demod', [status(thm)], ['63', '64'])).
% 2.13/2.35  thf('148', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 2.13/2.35      inference('simplify', [status(thm)], ['131'])).
% 2.13/2.35  thf('149', plain, ((v1_funct_1 @ sk_C)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('150', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 2.13/2.35      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 2.13/2.35  thf('151', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 2.13/2.35      inference('simplify', [status(thm)], ['131'])).
% 2.13/2.35  thf('152', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.13/2.35      inference('sup+', [status(thm)], ['57', '58'])).
% 2.13/2.35  thf('153', plain,
% 2.13/2.35      (![X0 : $i]:
% 2.13/2.35         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 2.13/2.35          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 2.13/2.35          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 2.13/2.35              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.13/2.35          | ~ (v2_funct_1 @ X0)
% 2.13/2.35          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.13/2.35              != (k2_relat_1 @ X0))
% 2.13/2.35          | ~ (v1_funct_1 @ X0)
% 2.13/2.35          | ~ (v1_relat_1 @ X0))),
% 2.13/2.35      inference('simplify', [status(thm)], ['114'])).
% 2.13/2.35  thf('154', plain,
% 2.13/2.35      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)
% 2.13/2.35        | ~ (v1_relat_1 @ sk_C)
% 2.13/2.35        | ~ (v1_funct_1 @ sk_C)
% 2.13/2.35        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.13/2.35            != (k2_relat_1 @ sk_C))
% 2.13/2.35        | ~ (v2_funct_1 @ sk_C)
% 2.13/2.35        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 2.13/2.35            = (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 2.13/2.35        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 2.13/2.35      inference('sup-', [status(thm)], ['152', '153'])).
% 2.13/2.35  thf('155', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.13/2.35      inference('sup+', [status(thm)], ['57', '58'])).
% 2.13/2.35  thf('156', plain,
% 2.13/2.35      (![X51 : $i]:
% 2.13/2.35         ((v1_funct_2 @ X51 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51))
% 2.13/2.35          | ~ (v1_funct_1 @ X51)
% 2.13/2.35          | ~ (v1_relat_1 @ X51))),
% 2.13/2.35      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.13/2.35  thf('157', plain,
% 2.13/2.35      (((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)
% 2.13/2.35        | ~ (v1_relat_1 @ sk_C)
% 2.13/2.35        | ~ (v1_funct_1 @ sk_C))),
% 2.13/2.35      inference('sup+', [status(thm)], ['155', '156'])).
% 2.13/2.35  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 2.13/2.35      inference('demod', [status(thm)], ['63', '64'])).
% 2.13/2.35  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('160', plain, ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)),
% 2.13/2.35      inference('demod', [status(thm)], ['157', '158', '159'])).
% 2.13/2.35  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 2.13/2.35      inference('demod', [status(thm)], ['63', '64'])).
% 2.13/2.35  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('163', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.13/2.35      inference('sup+', [status(thm)], ['57', '58'])).
% 2.13/2.35  thf('164', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.13/2.35      inference('sup+', [status(thm)], ['57', '58'])).
% 2.13/2.35  thf('165', plain,
% 2.13/2.35      (![X51 : $i]:
% 2.13/2.35         ((m1_subset_1 @ X51 @ 
% 2.13/2.35           (k1_zfmisc_1 @ 
% 2.13/2.35            (k2_zfmisc_1 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51))))
% 2.13/2.35          | ~ (v1_funct_1 @ X51)
% 2.13/2.35          | ~ (v1_relat_1 @ X51))),
% 2.13/2.35      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.13/2.35  thf('166', plain,
% 2.13/2.35      (((m1_subset_1 @ sk_C @ 
% 2.13/2.35         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))
% 2.13/2.35        | ~ (v1_relat_1 @ sk_C)
% 2.13/2.35        | ~ (v1_funct_1 @ sk_C))),
% 2.13/2.35      inference('sup+', [status(thm)], ['164', '165'])).
% 2.13/2.35  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 2.13/2.35      inference('demod', [status(thm)], ['63', '64'])).
% 2.13/2.35  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('169', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_C @ 
% 2.13/2.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 2.13/2.35      inference('demod', [status(thm)], ['166', '167', '168'])).
% 2.13/2.35  thf('170', plain,
% 2.13/2.35      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.13/2.35         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 2.13/2.35          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.13/2.35      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.13/2.35  thf('171', plain,
% 2.13/2.35      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.13/2.35      inference('sup-', [status(thm)], ['169', '170'])).
% 2.13/2.35  thf('172', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.13/2.35      inference('sup+', [status(thm)], ['57', '58'])).
% 2.13/2.35  thf('173', plain,
% 2.13/2.35      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C) = (sk_B))),
% 2.13/2.35      inference('demod', [status(thm)], ['171', '172'])).
% 2.13/2.35  thf('174', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.13/2.35      inference('sup+', [status(thm)], ['57', '58'])).
% 2.13/2.35  thf('175', plain, ((v2_funct_1 @ sk_C)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('176', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('177', plain,
% 2.13/2.35      (![X48 : $i, X49 : $i, X50 : $i]:
% 2.13/2.35         (((X48) = (k1_xboole_0))
% 2.13/2.35          | ~ (v1_funct_1 @ X49)
% 2.13/2.35          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 2.13/2.35          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 2.13/2.35          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_relat_1 @ X50))
% 2.13/2.35          | ~ (v2_funct_1 @ X49)
% 2.13/2.35          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 2.13/2.35      inference('demod', [status(thm)], ['93', '94'])).
% 2.13/2.35  thf('178', plain,
% 2.13/2.35      ((((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 2.13/2.35        | ~ (v2_funct_1 @ sk_C)
% 2.13/2.35        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A_1))
% 2.13/2.35        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 2.13/2.35        | ~ (v1_funct_1 @ sk_C)
% 2.13/2.35        | ((sk_B) = (k1_xboole_0)))),
% 2.13/2.35      inference('sup-', [status(thm)], ['176', '177'])).
% 2.13/2.35  thf('179', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('180', plain, ((v2_funct_1 @ sk_C)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('181', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('182', plain, ((v1_funct_1 @ sk_C)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('183', plain,
% 2.13/2.35      ((((sk_B) != (sk_B))
% 2.13/2.35        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A_1))
% 2.13/2.35        | ((sk_B) = (k1_xboole_0)))),
% 2.13/2.35      inference('demod', [status(thm)], ['178', '179', '180', '181', '182'])).
% 2.13/2.35  thf('184', plain,
% 2.13/2.35      ((((sk_B) = (k1_xboole_0))
% 2.13/2.35        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A_1)))),
% 2.13/2.35      inference('simplify', [status(thm)], ['183'])).
% 2.13/2.35  thf('185', plain, (((sk_B) != (k1_xboole_0))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('186', plain,
% 2.13/2.35      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A_1))),
% 2.13/2.35      inference('simplify_reflect-', [status(thm)], ['184', '185'])).
% 2.13/2.35  thf('187', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.13/2.35      inference('sup+', [status(thm)], ['57', '58'])).
% 2.13/2.35  thf('188', plain,
% 2.13/2.35      ((((sk_B) != (sk_B))
% 2.13/2.35        | ((k6_relat_1 @ sk_A_1) = (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 2.13/2.35        | ((sk_B) = (k1_xboole_0)))),
% 2.13/2.35      inference('demod', [status(thm)],
% 2.13/2.35                ['154', '160', '161', '162', '163', '173', '174', '175', 
% 2.13/2.35                 '186', '187'])).
% 2.13/2.35  thf('189', plain,
% 2.13/2.35      ((((sk_B) = (k1_xboole_0))
% 2.13/2.35        | ((k6_relat_1 @ sk_A_1) = (k6_relat_1 @ (k1_relat_1 @ sk_C))))),
% 2.13/2.35      inference('simplify', [status(thm)], ['188'])).
% 2.13/2.35  thf('190', plain, (((sk_B) != (k1_xboole_0))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('191', plain,
% 2.13/2.35      (((k6_relat_1 @ sk_A_1) = (k6_relat_1 @ (k1_relat_1 @ sk_C)))),
% 2.13/2.35      inference('simplify_reflect-', [status(thm)], ['189', '190'])).
% 2.13/2.35  thf('192', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 2.13/2.35      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.13/2.35  thf('193', plain,
% 2.13/2.35      (((k1_relat_1 @ (k6_relat_1 @ sk_A_1)) = (k1_relat_1 @ sk_C))),
% 2.13/2.35      inference('sup+', [status(thm)], ['191', '192'])).
% 2.13/2.35  thf('194', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 2.13/2.35      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.13/2.35  thf('195', plain, (((sk_A_1) = (k1_relat_1 @ sk_C))),
% 2.13/2.35      inference('demod', [status(thm)], ['193', '194'])).
% 2.13/2.35  thf('196', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 2.13/2.35      inference('simplify', [status(thm)], ['131'])).
% 2.13/2.35  thf('197', plain,
% 2.13/2.35      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 2.13/2.35        | ((sk_A_1) = (k1_xboole_0))
% 2.13/2.35        | ((sk_A_1) != (sk_A_1))
% 2.13/2.35        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 2.13/2.35      inference('demod', [status(thm)],
% 2.13/2.35                ['137', '138', '139', '140', '141', '142', '143', '144', 
% 2.13/2.35                 '145', '146', '147', '148', '149', '150', '151', '195', '196'])).
% 2.13/2.35  thf('198', plain,
% 2.13/2.35      ((((sk_D) = (k2_funct_1 @ sk_C)) | ((sk_A_1) = (k1_xboole_0)))),
% 2.13/2.35      inference('simplify', [status(thm)], ['197'])).
% 2.13/2.35  thf('199', plain, (((sk_A_1) != (k1_xboole_0))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('200', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('201', plain, ($false),
% 2.13/2.35      inference('simplify_reflect-', [status(thm)], ['198', '199', '200'])).
% 2.13/2.35  
% 2.13/2.35  % SZS output end Refutation
% 2.13/2.35  
% 2.13/2.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
