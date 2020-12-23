%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tKWM8YbsSX

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:28 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :  246 (5826 expanded)
%              Number of leaves         :   45 (1691 expanded)
%              Depth                    :   27
%              Number of atoms          : 2580 (162556 expanded)
%              Number of equality atoms :  209 (10976 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X21 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 ) ) ),
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
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X7 @ X8 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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

thf('32',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_relset_1 @ X32 @ X32 @ ( k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34 ) @ ( k6_partfun1 @ X32 ) )
      | ( ( k2_relset_1 @ X33 @ X32 @ X34 )
        = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('35',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_relset_1 @ X32 @ X32 @ ( k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34 ) @ ( k6_relat_1 @ X32 ) )
      | ( ( k2_relset_1 @ X33 @ X32 @ X34 )
        = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','45','46','47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('54',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','49','54','55','60','61','66'])).

thf('68',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('70',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('71',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
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

thf('73',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( zip_tseitin_0 @ X39 @ X42 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X43 @ X40 @ X40 @ X41 @ X42 @ X39 ) )
      | ( zip_tseitin_1 @ X41 @ X40 )
      | ( ( k2_relset_1 @ X43 @ X40 @ X42 )
       != X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X40 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('74',plain,(
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
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','77'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('79',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('80',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['78','79','80','81','82','83'])).

thf('85',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('87',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v2_funct_1 @ X36 )
      | ~ ( zip_tseitin_0 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('91',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['68','91'])).

thf('93',plain,(
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

thf('94',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( ( k5_relat_1 @ X45 @ ( k2_funct_1 @ X45 ) )
        = ( k6_partfun1 @ X46 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X46 @ X44 @ X45 )
       != X44 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('95',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('96',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( ( k5_relat_1 @ X45 @ ( k2_funct_1 @ X45 ) )
        = ( k6_relat_1 @ X46 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X46 @ X44 @ X45 )
       != X44 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('99',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','45','46','47','48'])).

thf('105',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['89','90'])).

thf('108',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('109',plain,(
    ! [X47: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ ( k2_relat_1 @ X47 ) ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('110',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X47: $i] :
      ( ( v1_funct_2 @ X47 @ ( k1_relat_1 @ X47 ) @ ( k2_relat_1 @ X47 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('113',plain,(
    ! [X47: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ ( k2_relat_1 @ X47 ) ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('114',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( ( k5_relat_1 @ X45 @ ( k2_funct_1 @ X45 ) )
        = ( k6_relat_1 @ X46 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X46 @ X44 @ X45 )
       != X44 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('115',plain,(
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
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
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
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
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
    inference('sup-',[status(thm)],['112','116'])).

thf('118',plain,(
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
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
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
    inference('sup-',[status(thm)],['111','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('121',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['108','122'])).

thf('124',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('125',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','45','46','47','48'])).

thf('126',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['89','90'])).

thf('127',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('128',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124','125','126','127','128'])).

thf('130',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['92','131'])).

thf('133',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('135',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X7 @ X8 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('136',plain,(
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
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
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
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
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
    inference('sup-',[status(thm)],['133','137'])).

thf('139',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['129','130'])).

thf('141',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['132'])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['58','59'])).

thf('143',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('145',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['89','90'])).

thf('146',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','45','46','47','48'])).

thf('147',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['132'])).

thf('148',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('149',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['132'])).

thf('150',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','45','46','47','48'])).

thf('152',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['132'])).

thf('153',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['58','59'])).

thf('154',plain,(
    ! [X47: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ ( k2_relat_1 @ X47 ) ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('155',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( ( k5_relat_1 @ X45 @ ( k2_funct_1 @ X45 ) )
        = ( k6_relat_1 @ X46 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X46 @ X44 @ X45 )
       != X44 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('160',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('162',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('163',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['58','59'])).

thf('165',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['58','59'])).

thf('168',plain,(
    ! [X47: $i] :
      ( ( v1_funct_2 @ X47 @ ( k1_relat_1 @ X47 ) @ ( k2_relat_1 @ X47 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('169',plain,
    ( ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['160','165','166','172','173'])).

thf('175',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['175','176'])).

thf('178',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( ( k5_relat_1 @ X45 @ ( k2_funct_1 @ X45 ) )
        = ( k6_relat_1 @ X46 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X46 @ X44 @ X45 )
       != X44 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('180',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['180','181','182','183','184'])).

thf('186',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['186','187'])).

thf('189',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['177','188'])).

thf('190',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('191',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('193',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['132'])).

thf('195',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','142','143','144','145','146','147','148','149','150','151','152','193','194'])).

thf('196',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['196','197','198'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tKWM8YbsSX
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:45:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.04/1.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.04/1.29  % Solved by: fo/fo7.sh
% 1.04/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.29  % done 1241 iterations in 0.825s
% 1.04/1.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.04/1.29  % SZS output start Refutation
% 1.04/1.29  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.04/1.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.04/1.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.04/1.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.04/1.29  thf(sk_B_type, type, sk_B: $i).
% 1.04/1.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.04/1.29  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.04/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.29  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.04/1.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.04/1.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.04/1.29  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.04/1.29  thf(sk_C_type, type, sk_C: $i).
% 1.04/1.29  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.04/1.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.04/1.29  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.04/1.29  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.04/1.29  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.04/1.29  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.04/1.29  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.04/1.29  thf(sk_D_type, type, sk_D: $i).
% 1.04/1.29  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.04/1.29  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.04/1.29  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.04/1.29  thf(t36_funct_2, conjecture,
% 1.04/1.29    (![A:$i,B:$i,C:$i]:
% 1.04/1.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.04/1.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.04/1.29       ( ![D:$i]:
% 1.04/1.29         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.04/1.29             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.04/1.29           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.04/1.29               ( r2_relset_1 @
% 1.04/1.29                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.04/1.29                 ( k6_partfun1 @ A ) ) & 
% 1.04/1.29               ( v2_funct_1 @ C ) ) =>
% 1.04/1.29             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.04/1.29               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.04/1.29  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.29    (~( ![A:$i,B:$i,C:$i]:
% 1.04/1.29        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.04/1.29            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.04/1.29          ( ![D:$i]:
% 1.04/1.29            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.04/1.29                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.04/1.29              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.04/1.29                  ( r2_relset_1 @
% 1.04/1.29                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.04/1.29                    ( k6_partfun1 @ A ) ) & 
% 1.04/1.29                  ( v2_funct_1 @ C ) ) =>
% 1.04/1.29                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.04/1.29                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.04/1.29    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.04/1.29  thf('0', plain,
% 1.04/1.29      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.04/1.29        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.04/1.29        (k6_partfun1 @ sk_A))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf(redefinition_k6_partfun1, axiom,
% 1.04/1.29    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.04/1.29  thf('1', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.04/1.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.04/1.29  thf('2', plain,
% 1.04/1.29      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.04/1.29        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.04/1.29        (k6_relat_1 @ sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['0', '1'])).
% 1.04/1.29  thf('3', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('4', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf(redefinition_k1_partfun1, axiom,
% 1.04/1.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.04/1.29     ( ( ( v1_funct_1 @ E ) & 
% 1.04/1.29         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.04/1.29         ( v1_funct_1 @ F ) & 
% 1.04/1.29         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.04/1.29       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.04/1.29  thf('5', plain,
% 1.04/1.29      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.04/1.29         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.04/1.29          | ~ (v1_funct_1 @ X24)
% 1.04/1.29          | ~ (v1_funct_1 @ X27)
% 1.04/1.29          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.04/1.29          | ((k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 1.04/1.29              = (k5_relat_1 @ X24 @ X27)))),
% 1.04/1.29      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.04/1.29  thf('6', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.29         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.04/1.29            = (k5_relat_1 @ sk_C @ X0))
% 1.04/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.04/1.29          | ~ (v1_funct_1 @ X0)
% 1.04/1.29          | ~ (v1_funct_1 @ sk_C))),
% 1.04/1.29      inference('sup-', [status(thm)], ['4', '5'])).
% 1.04/1.29  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('8', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.29         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.04/1.29            = (k5_relat_1 @ sk_C @ X0))
% 1.04/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.04/1.29          | ~ (v1_funct_1 @ X0))),
% 1.04/1.29      inference('demod', [status(thm)], ['6', '7'])).
% 1.04/1.29  thf('9', plain,
% 1.04/1.29      ((~ (v1_funct_1 @ sk_D)
% 1.04/1.29        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.04/1.29            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['3', '8'])).
% 1.04/1.29  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('11', plain,
% 1.04/1.29      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.04/1.29         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.04/1.29      inference('demod', [status(thm)], ['9', '10'])).
% 1.04/1.29  thf('12', plain,
% 1.04/1.29      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.04/1.29        (k6_relat_1 @ sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['2', '11'])).
% 1.04/1.29  thf('13', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('14', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf(dt_k1_partfun1, axiom,
% 1.04/1.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.04/1.29     ( ( ( v1_funct_1 @ E ) & 
% 1.04/1.29         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.04/1.29         ( v1_funct_1 @ F ) & 
% 1.04/1.29         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.04/1.29       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.04/1.29         ( m1_subset_1 @
% 1.04/1.29           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.04/1.29           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.04/1.29  thf('15', plain,
% 1.04/1.29      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.04/1.29         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.04/1.29          | ~ (v1_funct_1 @ X16)
% 1.04/1.29          | ~ (v1_funct_1 @ X19)
% 1.04/1.29          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.04/1.29          | (m1_subset_1 @ (k1_partfun1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19) @ 
% 1.04/1.29             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X21))))),
% 1.04/1.29      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.04/1.29  thf('16', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.29         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.04/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.04/1.29          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.04/1.29          | ~ (v1_funct_1 @ X1)
% 1.04/1.29          | ~ (v1_funct_1 @ sk_C))),
% 1.04/1.29      inference('sup-', [status(thm)], ['14', '15'])).
% 1.04/1.29  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('18', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.29         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.04/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.04/1.29          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.04/1.29          | ~ (v1_funct_1 @ X1))),
% 1.04/1.29      inference('demod', [status(thm)], ['16', '17'])).
% 1.04/1.29  thf('19', plain,
% 1.04/1.29      ((~ (v1_funct_1 @ sk_D)
% 1.04/1.29        | (m1_subset_1 @ 
% 1.04/1.29           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.04/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.04/1.29      inference('sup-', [status(thm)], ['13', '18'])).
% 1.04/1.29  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('21', plain,
% 1.04/1.29      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.04/1.29         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.04/1.29      inference('demod', [status(thm)], ['9', '10'])).
% 1.04/1.29  thf('22', plain,
% 1.04/1.29      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.04/1.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.04/1.29      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.04/1.29  thf(redefinition_r2_relset_1, axiom,
% 1.04/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.04/1.29     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.04/1.29         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.04/1.29       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.04/1.29  thf('23', plain,
% 1.04/1.29      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.04/1.29         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.04/1.29          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.04/1.29          | ((X12) = (X15))
% 1.04/1.29          | ~ (r2_relset_1 @ X13 @ X14 @ X12 @ X15))),
% 1.04/1.29      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.04/1.29  thf('24', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.04/1.29          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.04/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.04/1.29      inference('sup-', [status(thm)], ['22', '23'])).
% 1.04/1.29  thf('25', plain,
% 1.04/1.29      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.04/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.04/1.29        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['12', '24'])).
% 1.04/1.29  thf(dt_k6_partfun1, axiom,
% 1.04/1.29    (![A:$i]:
% 1.04/1.29     ( ( m1_subset_1 @
% 1.04/1.29         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.04/1.29       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.04/1.29  thf('26', plain,
% 1.04/1.29      (![X23 : $i]:
% 1.04/1.29         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 1.04/1.29          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 1.04/1.29      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.04/1.29  thf('27', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.04/1.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.04/1.29  thf('28', plain,
% 1.04/1.29      (![X23 : $i]:
% 1.04/1.29         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 1.04/1.29          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 1.04/1.29      inference('demod', [status(thm)], ['26', '27'])).
% 1.04/1.29  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['25', '28'])).
% 1.04/1.29  thf(t64_funct_1, axiom,
% 1.04/1.29    (![A:$i]:
% 1.04/1.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.04/1.29       ( ![B:$i]:
% 1.04/1.29         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.04/1.29           ( ( ( v2_funct_1 @ A ) & 
% 1.04/1.29               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.04/1.29               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.04/1.29             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.04/1.29  thf('30', plain,
% 1.04/1.29      (![X7 : $i, X8 : $i]:
% 1.04/1.29         (~ (v1_relat_1 @ X7)
% 1.04/1.29          | ~ (v1_funct_1 @ X7)
% 1.04/1.29          | ((X7) = (k2_funct_1 @ X8))
% 1.04/1.29          | ((k5_relat_1 @ X7 @ X8) != (k6_relat_1 @ (k2_relat_1 @ X8)))
% 1.04/1.29          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 1.04/1.29          | ~ (v2_funct_1 @ X8)
% 1.04/1.29          | ~ (v1_funct_1 @ X8)
% 1.04/1.29          | ~ (v1_relat_1 @ X8))),
% 1.04/1.29      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.04/1.29  thf('31', plain,
% 1.04/1.29      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 1.04/1.29        | ~ (v1_relat_1 @ sk_D)
% 1.04/1.29        | ~ (v1_funct_1 @ sk_D)
% 1.04/1.29        | ~ (v2_funct_1 @ sk_D)
% 1.04/1.29        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.04/1.29        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.04/1.29        | ~ (v1_funct_1 @ sk_C)
% 1.04/1.29        | ~ (v1_relat_1 @ sk_C))),
% 1.04/1.29      inference('sup-', [status(thm)], ['29', '30'])).
% 1.04/1.29  thf('32', plain,
% 1.04/1.29      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.04/1.29         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.04/1.29      inference('demod', [status(thm)], ['9', '10'])).
% 1.04/1.29  thf('33', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf(t24_funct_2, axiom,
% 1.04/1.29    (![A:$i,B:$i,C:$i]:
% 1.04/1.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.04/1.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.04/1.29       ( ![D:$i]:
% 1.04/1.29         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.04/1.29             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.04/1.29           ( ( r2_relset_1 @
% 1.04/1.29               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.04/1.29               ( k6_partfun1 @ B ) ) =>
% 1.04/1.29             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.04/1.29  thf('34', plain,
% 1.04/1.29      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.04/1.29         (~ (v1_funct_1 @ X31)
% 1.04/1.29          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 1.04/1.29          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.04/1.29          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 1.04/1.29               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 1.04/1.29               (k6_partfun1 @ X32))
% 1.04/1.29          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 1.04/1.29          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 1.04/1.29          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 1.04/1.29          | ~ (v1_funct_1 @ X34))),
% 1.04/1.29      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.04/1.29  thf('35', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.04/1.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.04/1.29  thf('36', plain,
% 1.04/1.29      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.04/1.29         (~ (v1_funct_1 @ X31)
% 1.04/1.29          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 1.04/1.29          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.04/1.29          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 1.04/1.29               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 1.04/1.29               (k6_relat_1 @ X32))
% 1.04/1.29          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 1.04/1.29          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 1.04/1.29          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 1.04/1.29          | ~ (v1_funct_1 @ X34))),
% 1.04/1.29      inference('demod', [status(thm)], ['34', '35'])).
% 1.04/1.29  thf('37', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (~ (v1_funct_1 @ X0)
% 1.04/1.29          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.04/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.04/1.29          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.04/1.29          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.04/1.29               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.04/1.29               (k6_relat_1 @ sk_A))
% 1.04/1.29          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.04/1.29          | ~ (v1_funct_1 @ sk_C))),
% 1.04/1.29      inference('sup-', [status(thm)], ['33', '36'])).
% 1.04/1.29  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('40', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (~ (v1_funct_1 @ X0)
% 1.04/1.29          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.04/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.04/1.29          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.04/1.29          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.04/1.29               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.04/1.29               (k6_relat_1 @ sk_A)))),
% 1.04/1.29      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.04/1.29  thf('41', plain,
% 1.04/1.29      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.04/1.29           (k6_relat_1 @ sk_A))
% 1.04/1.29        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.04/1.29        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.04/1.29        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.04/1.29        | ~ (v1_funct_1 @ sk_D))),
% 1.04/1.29      inference('sup-', [status(thm)], ['32', '40'])).
% 1.04/1.29  thf('42', plain,
% 1.04/1.29      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.04/1.29        (k6_relat_1 @ sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['2', '11'])).
% 1.04/1.29  thf('43', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf(redefinition_k2_relset_1, axiom,
% 1.04/1.29    (![A:$i,B:$i,C:$i]:
% 1.04/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.04/1.29       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.04/1.29  thf('44', plain,
% 1.04/1.29      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.04/1.29         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 1.04/1.29          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.04/1.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.04/1.29  thf('45', plain,
% 1.04/1.29      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.04/1.29      inference('sup-', [status(thm)], ['43', '44'])).
% 1.04/1.29  thf('46', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('49', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['41', '42', '45', '46', '47', '48'])).
% 1.04/1.29  thf('50', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf(cc2_relat_1, axiom,
% 1.04/1.29    (![A:$i]:
% 1.04/1.29     ( ( v1_relat_1 @ A ) =>
% 1.04/1.29       ( ![B:$i]:
% 1.04/1.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.04/1.29  thf('51', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i]:
% 1.04/1.29         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.04/1.29          | (v1_relat_1 @ X0)
% 1.04/1.29          | ~ (v1_relat_1 @ X1))),
% 1.04/1.29      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.04/1.29  thf('52', plain,
% 1.04/1.29      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.04/1.29      inference('sup-', [status(thm)], ['50', '51'])).
% 1.04/1.29  thf(fc6_relat_1, axiom,
% 1.04/1.29    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.04/1.29  thf('53', plain,
% 1.04/1.29      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.04/1.29      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.04/1.29  thf('54', plain, ((v1_relat_1 @ sk_D)),
% 1.04/1.29      inference('demod', [status(thm)], ['52', '53'])).
% 1.04/1.29  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('56', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('57', plain,
% 1.04/1.29      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.04/1.29         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 1.04/1.29          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.04/1.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.04/1.29  thf('58', plain,
% 1.04/1.29      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.04/1.29      inference('sup-', [status(thm)], ['56', '57'])).
% 1.04/1.29  thf('59', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('60', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.04/1.29      inference('sup+', [status(thm)], ['58', '59'])).
% 1.04/1.29  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('62', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('63', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i]:
% 1.04/1.29         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.04/1.29          | (v1_relat_1 @ X0)
% 1.04/1.29          | ~ (v1_relat_1 @ X1))),
% 1.04/1.29      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.04/1.29  thf('64', plain,
% 1.04/1.29      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.04/1.29      inference('sup-', [status(thm)], ['62', '63'])).
% 1.04/1.29  thf('65', plain,
% 1.04/1.29      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.04/1.29      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.04/1.29  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 1.04/1.29      inference('demod', [status(thm)], ['64', '65'])).
% 1.04/1.29  thf('67', plain,
% 1.04/1.29      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 1.04/1.29        | ~ (v2_funct_1 @ sk_D)
% 1.04/1.29        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.04/1.29        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.04/1.29      inference('demod', [status(thm)],
% 1.04/1.29                ['31', '49', '54', '55', '60', '61', '66'])).
% 1.04/1.29  thf('68', plain,
% 1.04/1.29      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.04/1.29        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.04/1.29        | ~ (v2_funct_1 @ sk_D))),
% 1.04/1.29      inference('simplify', [status(thm)], ['67'])).
% 1.04/1.29  thf('69', plain,
% 1.04/1.29      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.04/1.29         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.04/1.29      inference('demod', [status(thm)], ['9', '10'])).
% 1.04/1.29  thf('70', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['25', '28'])).
% 1.04/1.29  thf('71', plain,
% 1.04/1.29      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.04/1.29         = (k6_relat_1 @ sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['69', '70'])).
% 1.04/1.29  thf('72', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf(t30_funct_2, axiom,
% 1.04/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.04/1.29     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.04/1.29         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.04/1.29       ( ![E:$i]:
% 1.04/1.29         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.04/1.29             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.04/1.29           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.04/1.29               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.04/1.29             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.04/1.29               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.04/1.29  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.04/1.29  thf(zf_stmt_2, axiom,
% 1.04/1.29    (![C:$i,B:$i]:
% 1.04/1.29     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.04/1.29       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.04/1.29  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.04/1.29  thf(zf_stmt_4, axiom,
% 1.04/1.29    (![E:$i,D:$i]:
% 1.04/1.29     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.04/1.29  thf(zf_stmt_5, axiom,
% 1.04/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.04/1.29     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.04/1.29         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.04/1.29       ( ![E:$i]:
% 1.04/1.29         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.04/1.29             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.04/1.29           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.04/1.29               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.04/1.29             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.04/1.29  thf('73', plain,
% 1.04/1.29      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.04/1.29         (~ (v1_funct_1 @ X39)
% 1.04/1.29          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 1.04/1.29          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.04/1.29          | (zip_tseitin_0 @ X39 @ X42)
% 1.04/1.29          | ~ (v2_funct_1 @ (k1_partfun1 @ X43 @ X40 @ X40 @ X41 @ X42 @ X39))
% 1.04/1.29          | (zip_tseitin_1 @ X41 @ X40)
% 1.04/1.29          | ((k2_relset_1 @ X43 @ X40 @ X42) != (X40))
% 1.04/1.29          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X40)))
% 1.04/1.29          | ~ (v1_funct_2 @ X42 @ X43 @ X40)
% 1.04/1.29          | ~ (v1_funct_1 @ X42))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.04/1.29  thf('74', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i]:
% 1.04/1.29         (~ (v1_funct_1 @ X0)
% 1.04/1.29          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.04/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.04/1.29          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.04/1.29          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.04/1.29          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.04/1.29          | (zip_tseitin_0 @ sk_D @ X0)
% 1.04/1.29          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.04/1.29          | ~ (v1_funct_1 @ sk_D))),
% 1.04/1.29      inference('sup-', [status(thm)], ['72', '73'])).
% 1.04/1.29  thf('75', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('77', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i]:
% 1.04/1.29         (~ (v1_funct_1 @ X0)
% 1.04/1.29          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.04/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.04/1.29          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.04/1.29          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.04/1.29          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.04/1.29          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.04/1.29      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.04/1.29  thf('78', plain,
% 1.04/1.29      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.04/1.29        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.04/1.29        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.04/1.29        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.04/1.29        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.04/1.29        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.04/1.29        | ~ (v1_funct_1 @ sk_C))),
% 1.04/1.29      inference('sup-', [status(thm)], ['71', '77'])).
% 1.04/1.29  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.04/1.29  thf('79', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 1.04/1.29      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.04/1.29  thf('80', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('81', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('82', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('84', plain,
% 1.04/1.29      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.04/1.29        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.04/1.29        | ((sk_B) != (sk_B)))),
% 1.04/1.29      inference('demod', [status(thm)], ['78', '79', '80', '81', '82', '83'])).
% 1.04/1.29  thf('85', plain,
% 1.04/1.29      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.04/1.29      inference('simplify', [status(thm)], ['84'])).
% 1.04/1.29  thf('86', plain,
% 1.04/1.29      (![X37 : $i, X38 : $i]:
% 1.04/1.29         (((X37) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X37 @ X38))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.04/1.29  thf('87', plain,
% 1.04/1.29      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['85', '86'])).
% 1.04/1.29  thf('88', plain, (((sk_A) != (k1_xboole_0))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('89', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.04/1.29      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 1.04/1.29  thf('90', plain,
% 1.04/1.29      (![X35 : $i, X36 : $i]:
% 1.04/1.29         ((v2_funct_1 @ X36) | ~ (zip_tseitin_0 @ X36 @ X35))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.04/1.29  thf('91', plain, ((v2_funct_1 @ sk_D)),
% 1.04/1.29      inference('sup-', [status(thm)], ['89', '90'])).
% 1.04/1.29  thf('92', plain,
% 1.04/1.29      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 1.04/1.29      inference('demod', [status(thm)], ['68', '91'])).
% 1.04/1.29  thf('93', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf(t35_funct_2, axiom,
% 1.04/1.29    (![A:$i,B:$i,C:$i]:
% 1.04/1.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.04/1.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.04/1.29       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.04/1.29         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.04/1.29           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.04/1.29             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.04/1.29  thf('94', plain,
% 1.04/1.29      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.04/1.29         (((X44) = (k1_xboole_0))
% 1.04/1.29          | ~ (v1_funct_1 @ X45)
% 1.04/1.29          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 1.04/1.29          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 1.04/1.29          | ((k5_relat_1 @ X45 @ (k2_funct_1 @ X45)) = (k6_partfun1 @ X46))
% 1.04/1.29          | ~ (v2_funct_1 @ X45)
% 1.04/1.29          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 1.04/1.29      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.04/1.29  thf('95', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.04/1.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.04/1.29  thf('96', plain,
% 1.04/1.29      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.04/1.29         (((X44) = (k1_xboole_0))
% 1.04/1.29          | ~ (v1_funct_1 @ X45)
% 1.04/1.29          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 1.04/1.29          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 1.04/1.29          | ((k5_relat_1 @ X45 @ (k2_funct_1 @ X45)) = (k6_relat_1 @ X46))
% 1.04/1.29          | ~ (v2_funct_1 @ X45)
% 1.04/1.29          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 1.04/1.29      inference('demod', [status(thm)], ['94', '95'])).
% 1.04/1.29  thf('97', plain,
% 1.04/1.29      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.04/1.29        | ~ (v2_funct_1 @ sk_D)
% 1.04/1.29        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.04/1.29        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.04/1.29        | ~ (v1_funct_1 @ sk_D)
% 1.04/1.29        | ((sk_A) = (k1_xboole_0)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['93', '96'])).
% 1.04/1.29  thf('98', plain,
% 1.04/1.29      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.04/1.29      inference('sup-', [status(thm)], ['43', '44'])).
% 1.04/1.29  thf('99', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('100', plain, ((v1_funct_1 @ sk_D)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('101', plain,
% 1.04/1.29      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.04/1.29        | ~ (v2_funct_1 @ sk_D)
% 1.04/1.29        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.04/1.29        | ((sk_A) = (k1_xboole_0)))),
% 1.04/1.29      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 1.04/1.29  thf('102', plain, (((sk_A) != (k1_xboole_0))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('103', plain,
% 1.04/1.29      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.04/1.29        | ~ (v2_funct_1 @ sk_D)
% 1.04/1.29        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 1.04/1.29      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 1.04/1.29  thf('104', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['41', '42', '45', '46', '47', '48'])).
% 1.04/1.29  thf('105', plain,
% 1.04/1.29      ((((sk_A) != (sk_A))
% 1.04/1.29        | ~ (v2_funct_1 @ sk_D)
% 1.04/1.29        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 1.04/1.29      inference('demod', [status(thm)], ['103', '104'])).
% 1.04/1.29  thf('106', plain,
% 1.04/1.29      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.04/1.29        | ~ (v2_funct_1 @ sk_D))),
% 1.04/1.29      inference('simplify', [status(thm)], ['105'])).
% 1.04/1.29  thf('107', plain, ((v2_funct_1 @ sk_D)),
% 1.04/1.29      inference('sup-', [status(thm)], ['89', '90'])).
% 1.04/1.29  thf('108', plain,
% 1.04/1.29      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.04/1.29      inference('demod', [status(thm)], ['106', '107'])).
% 1.04/1.29  thf(t3_funct_2, axiom,
% 1.04/1.29    (![A:$i]:
% 1.04/1.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.04/1.29       ( ( v1_funct_1 @ A ) & 
% 1.04/1.29         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.04/1.29         ( m1_subset_1 @
% 1.04/1.29           A @ 
% 1.04/1.29           ( k1_zfmisc_1 @
% 1.04/1.29             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.04/1.29  thf('109', plain,
% 1.04/1.29      (![X47 : $i]:
% 1.04/1.29         ((m1_subset_1 @ X47 @ 
% 1.04/1.29           (k1_zfmisc_1 @ 
% 1.04/1.29            (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ (k2_relat_1 @ X47))))
% 1.04/1.29          | ~ (v1_funct_1 @ X47)
% 1.04/1.29          | ~ (v1_relat_1 @ X47))),
% 1.04/1.29      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.04/1.29  thf('110', plain,
% 1.04/1.29      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.04/1.29         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 1.04/1.29          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.04/1.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.04/1.29  thf('111', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (~ (v1_relat_1 @ X0)
% 1.04/1.29          | ~ (v1_funct_1 @ X0)
% 1.04/1.29          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.04/1.29              = (k2_relat_1 @ X0)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['109', '110'])).
% 1.04/1.29  thf('112', plain,
% 1.04/1.29      (![X47 : $i]:
% 1.04/1.29         ((v1_funct_2 @ X47 @ (k1_relat_1 @ X47) @ (k2_relat_1 @ X47))
% 1.04/1.29          | ~ (v1_funct_1 @ X47)
% 1.04/1.29          | ~ (v1_relat_1 @ X47))),
% 1.04/1.29      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.04/1.29  thf('113', plain,
% 1.04/1.29      (![X47 : $i]:
% 1.04/1.29         ((m1_subset_1 @ X47 @ 
% 1.04/1.29           (k1_zfmisc_1 @ 
% 1.04/1.29            (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ (k2_relat_1 @ X47))))
% 1.04/1.29          | ~ (v1_funct_1 @ X47)
% 1.04/1.29          | ~ (v1_relat_1 @ X47))),
% 1.04/1.29      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.04/1.29  thf('114', plain,
% 1.04/1.29      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.04/1.29         (((X44) = (k1_xboole_0))
% 1.04/1.29          | ~ (v1_funct_1 @ X45)
% 1.04/1.29          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 1.04/1.29          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 1.04/1.29          | ((k5_relat_1 @ X45 @ (k2_funct_1 @ X45)) = (k6_relat_1 @ X46))
% 1.04/1.29          | ~ (v2_funct_1 @ X45)
% 1.04/1.29          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 1.04/1.29      inference('demod', [status(thm)], ['94', '95'])).
% 1.04/1.29  thf('115', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (~ (v1_relat_1 @ X0)
% 1.04/1.29          | ~ (v1_funct_1 @ X0)
% 1.04/1.29          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.04/1.29              != (k2_relat_1 @ X0))
% 1.04/1.29          | ~ (v2_funct_1 @ X0)
% 1.04/1.29          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.04/1.29              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.04/1.29          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.04/1.29          | ~ (v1_funct_1 @ X0)
% 1.04/1.29          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['113', '114'])).
% 1.04/1.29  thf('116', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.04/1.29          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.04/1.29          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.04/1.29              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.04/1.29          | ~ (v2_funct_1 @ X0)
% 1.04/1.29          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.04/1.29              != (k2_relat_1 @ X0))
% 1.04/1.29          | ~ (v1_funct_1 @ X0)
% 1.04/1.29          | ~ (v1_relat_1 @ X0))),
% 1.04/1.29      inference('simplify', [status(thm)], ['115'])).
% 1.04/1.29  thf('117', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (~ (v1_relat_1 @ X0)
% 1.04/1.29          | ~ (v1_funct_1 @ X0)
% 1.04/1.29          | ~ (v1_relat_1 @ X0)
% 1.04/1.29          | ~ (v1_funct_1 @ X0)
% 1.04/1.29          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.04/1.29              != (k2_relat_1 @ X0))
% 1.04/1.29          | ~ (v2_funct_1 @ X0)
% 1.04/1.29          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.04/1.29              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.04/1.29          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['112', '116'])).
% 1.04/1.29  thf('118', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.04/1.29          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.04/1.29              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.04/1.29          | ~ (v2_funct_1 @ X0)
% 1.04/1.29          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.04/1.29              != (k2_relat_1 @ X0))
% 1.04/1.29          | ~ (v1_funct_1 @ X0)
% 1.04/1.29          | ~ (v1_relat_1 @ X0))),
% 1.04/1.29      inference('simplify', [status(thm)], ['117'])).
% 1.04/1.29  thf('119', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 1.04/1.29          | ~ (v1_funct_1 @ X0)
% 1.04/1.29          | ~ (v1_relat_1 @ X0)
% 1.04/1.29          | ~ (v1_relat_1 @ X0)
% 1.04/1.29          | ~ (v1_funct_1 @ X0)
% 1.04/1.29          | ~ (v2_funct_1 @ X0)
% 1.04/1.29          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.04/1.29              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.04/1.29          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['111', '118'])).
% 1.04/1.29  thf('120', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.04/1.29          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.04/1.29              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.04/1.29          | ~ (v2_funct_1 @ X0)
% 1.04/1.29          | ~ (v1_relat_1 @ X0)
% 1.04/1.29          | ~ (v1_funct_1 @ X0))),
% 1.04/1.29      inference('simplify', [status(thm)], ['119'])).
% 1.04/1.29  thf(t71_relat_1, axiom,
% 1.04/1.29    (![A:$i]:
% 1.04/1.29     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.04/1.29       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.04/1.29  thf('121', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.04/1.29      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.04/1.29  thf('122', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 1.04/1.29            = (k1_relat_1 @ X0))
% 1.04/1.29          | ~ (v1_funct_1 @ X0)
% 1.04/1.29          | ~ (v1_relat_1 @ X0)
% 1.04/1.29          | ~ (v2_funct_1 @ X0)
% 1.04/1.29          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.04/1.29      inference('sup+', [status(thm)], ['120', '121'])).
% 1.04/1.29  thf('123', plain,
% 1.04/1.29      ((((k1_relat_1 @ (k6_relat_1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 1.04/1.29        | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 1.04/1.29        | ~ (v2_funct_1 @ sk_D)
% 1.04/1.29        | ~ (v1_relat_1 @ sk_D)
% 1.04/1.29        | ~ (v1_funct_1 @ sk_D))),
% 1.04/1.29      inference('sup+', [status(thm)], ['108', '122'])).
% 1.04/1.29  thf('124', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.04/1.29      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.04/1.29  thf('125', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['41', '42', '45', '46', '47', '48'])).
% 1.04/1.29  thf('126', plain, ((v2_funct_1 @ sk_D)),
% 1.04/1.29      inference('sup-', [status(thm)], ['89', '90'])).
% 1.04/1.29  thf('127', plain, ((v1_relat_1 @ sk_D)),
% 1.04/1.29      inference('demod', [status(thm)], ['52', '53'])).
% 1.04/1.29  thf('128', plain, ((v1_funct_1 @ sk_D)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('129', plain,
% 1.04/1.29      ((((sk_B) = (k1_relat_1 @ sk_D)) | ((sk_A) = (k1_xboole_0)))),
% 1.04/1.29      inference('demod', [status(thm)],
% 1.04/1.29                ['123', '124', '125', '126', '127', '128'])).
% 1.04/1.29  thf('130', plain, (((sk_A) != (k1_xboole_0))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('131', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.04/1.29      inference('simplify_reflect-', [status(thm)], ['129', '130'])).
% 1.04/1.29  thf('132', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 1.04/1.29      inference('demod', [status(thm)], ['92', '131'])).
% 1.04/1.29  thf('133', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.04/1.29      inference('simplify', [status(thm)], ['132'])).
% 1.04/1.29  thf('134', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.04/1.29          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.04/1.29              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.04/1.29          | ~ (v2_funct_1 @ X0)
% 1.04/1.29          | ~ (v1_relat_1 @ X0)
% 1.04/1.29          | ~ (v1_funct_1 @ X0))),
% 1.04/1.29      inference('simplify', [status(thm)], ['119'])).
% 1.04/1.29  thf('135', plain,
% 1.04/1.29      (![X7 : $i, X8 : $i]:
% 1.04/1.29         (~ (v1_relat_1 @ X7)
% 1.04/1.29          | ~ (v1_funct_1 @ X7)
% 1.04/1.29          | ((X7) = (k2_funct_1 @ X8))
% 1.04/1.29          | ((k5_relat_1 @ X7 @ X8) != (k6_relat_1 @ (k2_relat_1 @ X8)))
% 1.04/1.29          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 1.04/1.29          | ~ (v2_funct_1 @ X8)
% 1.04/1.29          | ~ (v1_funct_1 @ X8)
% 1.04/1.29          | ~ (v1_relat_1 @ X8))),
% 1.04/1.29      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.04/1.29  thf('136', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 1.04/1.29            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.04/1.29          | ~ (v1_funct_1 @ X0)
% 1.04/1.29          | ~ (v1_relat_1 @ X0)
% 1.04/1.29          | ~ (v2_funct_1 @ X0)
% 1.04/1.29          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.04/1.29          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.04/1.29          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.04/1.29          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.04/1.29          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.04/1.29          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.04/1.29          | ~ (v1_funct_1 @ X0)
% 1.04/1.29          | ~ (v1_relat_1 @ X0))),
% 1.04/1.29      inference('sup-', [status(thm)], ['134', '135'])).
% 1.04/1.29  thf('137', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.04/1.29          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.04/1.29          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.04/1.29          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.04/1.29          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.04/1.29          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.04/1.29          | ~ (v2_funct_1 @ X0)
% 1.04/1.29          | ~ (v1_relat_1 @ X0)
% 1.04/1.29          | ~ (v1_funct_1 @ X0)
% 1.04/1.29          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 1.04/1.29              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.04/1.29      inference('simplify', [status(thm)], ['136'])).
% 1.04/1.29  thf('138', plain,
% 1.04/1.29      ((~ (v2_funct_1 @ sk_C)
% 1.04/1.29        | ((k6_relat_1 @ (k1_relat_1 @ sk_D))
% 1.04/1.29            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_D))))
% 1.04/1.29        | ~ (v1_funct_1 @ sk_D)
% 1.04/1.29        | ~ (v1_relat_1 @ sk_D)
% 1.04/1.29        | ~ (v2_funct_1 @ sk_D)
% 1.04/1.29        | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 1.04/1.29        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 1.04/1.29        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 1.04/1.29        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 1.04/1.29        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 1.04/1.29      inference('sup-', [status(thm)], ['133', '137'])).
% 1.04/1.29  thf('139', plain, ((v2_funct_1 @ sk_C)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('140', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.04/1.29      inference('simplify_reflect-', [status(thm)], ['129', '130'])).
% 1.04/1.29  thf('141', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.04/1.29      inference('simplify', [status(thm)], ['132'])).
% 1.04/1.29  thf('142', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.04/1.29      inference('sup+', [status(thm)], ['58', '59'])).
% 1.04/1.29  thf('143', plain, ((v1_funct_1 @ sk_D)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('144', plain, ((v1_relat_1 @ sk_D)),
% 1.04/1.29      inference('demod', [status(thm)], ['52', '53'])).
% 1.04/1.29  thf('145', plain, ((v2_funct_1 @ sk_D)),
% 1.04/1.29      inference('sup-', [status(thm)], ['89', '90'])).
% 1.04/1.29  thf('146', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['41', '42', '45', '46', '47', '48'])).
% 1.04/1.29  thf('147', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.04/1.29      inference('simplify', [status(thm)], ['132'])).
% 1.04/1.29  thf('148', plain, ((v1_relat_1 @ sk_C)),
% 1.04/1.29      inference('demod', [status(thm)], ['64', '65'])).
% 1.04/1.29  thf('149', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.04/1.29      inference('simplify', [status(thm)], ['132'])).
% 1.04/1.29  thf('150', plain, ((v1_funct_1 @ sk_C)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('151', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['41', '42', '45', '46', '47', '48'])).
% 1.04/1.29  thf('152', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.04/1.29      inference('simplify', [status(thm)], ['132'])).
% 1.04/1.29  thf('153', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.04/1.29      inference('sup+', [status(thm)], ['58', '59'])).
% 1.04/1.29  thf('154', plain,
% 1.04/1.29      (![X47 : $i]:
% 1.04/1.29         ((m1_subset_1 @ X47 @ 
% 1.04/1.29           (k1_zfmisc_1 @ 
% 1.04/1.29            (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ (k2_relat_1 @ X47))))
% 1.04/1.29          | ~ (v1_funct_1 @ X47)
% 1.04/1.29          | ~ (v1_relat_1 @ X47))),
% 1.04/1.29      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.04/1.29  thf('155', plain,
% 1.04/1.29      (((m1_subset_1 @ sk_C @ 
% 1.04/1.29         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))
% 1.04/1.29        | ~ (v1_relat_1 @ sk_C)
% 1.04/1.29        | ~ (v1_funct_1 @ sk_C))),
% 1.04/1.29      inference('sup+', [status(thm)], ['153', '154'])).
% 1.04/1.29  thf('156', plain, ((v1_relat_1 @ sk_C)),
% 1.04/1.29      inference('demod', [status(thm)], ['64', '65'])).
% 1.04/1.29  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('158', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_C @ 
% 1.04/1.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 1.04/1.29      inference('demod', [status(thm)], ['155', '156', '157'])).
% 1.04/1.29  thf('159', plain,
% 1.04/1.29      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.04/1.29         (((X44) = (k1_xboole_0))
% 1.04/1.29          | ~ (v1_funct_1 @ X45)
% 1.04/1.29          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 1.04/1.29          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 1.04/1.29          | ((k5_relat_1 @ X45 @ (k2_funct_1 @ X45)) = (k6_relat_1 @ X46))
% 1.04/1.29          | ~ (v2_funct_1 @ X45)
% 1.04/1.29          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 1.04/1.29      inference('demod', [status(thm)], ['94', '95'])).
% 1.04/1.29  thf('160', plain,
% 1.04/1.29      ((((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C) != (sk_B))
% 1.04/1.29        | ~ (v2_funct_1 @ sk_C)
% 1.04/1.29        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.04/1.29            = (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 1.04/1.29        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)
% 1.04/1.29        | ~ (v1_funct_1 @ sk_C)
% 1.04/1.29        | ((sk_B) = (k1_xboole_0)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['158', '159'])).
% 1.04/1.29  thf('161', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_C @ 
% 1.04/1.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 1.04/1.29      inference('demod', [status(thm)], ['155', '156', '157'])).
% 1.04/1.29  thf('162', plain,
% 1.04/1.29      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.04/1.29         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 1.04/1.29          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.04/1.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.04/1.29  thf('163', plain,
% 1.04/1.29      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.04/1.29      inference('sup-', [status(thm)], ['161', '162'])).
% 1.04/1.29  thf('164', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.04/1.29      inference('sup+', [status(thm)], ['58', '59'])).
% 1.04/1.29  thf('165', plain,
% 1.04/1.29      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C) = (sk_B))),
% 1.04/1.29      inference('demod', [status(thm)], ['163', '164'])).
% 1.04/1.29  thf('166', plain, ((v2_funct_1 @ sk_C)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('167', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.04/1.29      inference('sup+', [status(thm)], ['58', '59'])).
% 1.04/1.29  thf('168', plain,
% 1.04/1.29      (![X47 : $i]:
% 1.04/1.29         ((v1_funct_2 @ X47 @ (k1_relat_1 @ X47) @ (k2_relat_1 @ X47))
% 1.04/1.29          | ~ (v1_funct_1 @ X47)
% 1.04/1.29          | ~ (v1_relat_1 @ X47))),
% 1.04/1.29      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.04/1.29  thf('169', plain,
% 1.04/1.29      (((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)
% 1.04/1.29        | ~ (v1_relat_1 @ sk_C)
% 1.04/1.29        | ~ (v1_funct_1 @ sk_C))),
% 1.04/1.29      inference('sup+', [status(thm)], ['167', '168'])).
% 1.04/1.29  thf('170', plain, ((v1_relat_1 @ sk_C)),
% 1.04/1.29      inference('demod', [status(thm)], ['64', '65'])).
% 1.04/1.29  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('172', plain, ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)),
% 1.04/1.29      inference('demod', [status(thm)], ['169', '170', '171'])).
% 1.04/1.29  thf('173', plain, ((v1_funct_1 @ sk_C)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('174', plain,
% 1.04/1.29      ((((sk_B) != (sk_B))
% 1.04/1.29        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.04/1.29            = (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 1.04/1.29        | ((sk_B) = (k1_xboole_0)))),
% 1.04/1.29      inference('demod', [status(thm)], ['160', '165', '166', '172', '173'])).
% 1.04/1.29  thf('175', plain,
% 1.04/1.29      ((((sk_B) = (k1_xboole_0))
% 1.04/1.29        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.04/1.29            = (k6_relat_1 @ (k1_relat_1 @ sk_C))))),
% 1.04/1.29      inference('simplify', [status(thm)], ['174'])).
% 1.04/1.29  thf('176', plain, (((sk_B) != (k1_xboole_0))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('177', plain,
% 1.04/1.29      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.04/1.29         = (k6_relat_1 @ (k1_relat_1 @ sk_C)))),
% 1.04/1.29      inference('simplify_reflect-', [status(thm)], ['175', '176'])).
% 1.04/1.29  thf('178', plain,
% 1.04/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('179', plain,
% 1.04/1.29      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.04/1.29         (((X44) = (k1_xboole_0))
% 1.04/1.29          | ~ (v1_funct_1 @ X45)
% 1.04/1.29          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 1.04/1.29          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 1.04/1.29          | ((k5_relat_1 @ X45 @ (k2_funct_1 @ X45)) = (k6_relat_1 @ X46))
% 1.04/1.29          | ~ (v2_funct_1 @ X45)
% 1.04/1.29          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 1.04/1.29      inference('demod', [status(thm)], ['94', '95'])).
% 1.04/1.29  thf('180', plain,
% 1.04/1.29      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.04/1.29        | ~ (v2_funct_1 @ sk_C)
% 1.04/1.29        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.04/1.29        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.04/1.29        | ~ (v1_funct_1 @ sk_C)
% 1.04/1.29        | ((sk_B) = (k1_xboole_0)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['178', '179'])).
% 1.04/1.29  thf('181', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('182', plain, ((v2_funct_1 @ sk_C)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('183', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('185', plain,
% 1.04/1.29      ((((sk_B) != (sk_B))
% 1.04/1.29        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.04/1.29        | ((sk_B) = (k1_xboole_0)))),
% 1.04/1.29      inference('demod', [status(thm)], ['180', '181', '182', '183', '184'])).
% 1.04/1.29  thf('186', plain,
% 1.04/1.29      ((((sk_B) = (k1_xboole_0))
% 1.04/1.29        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 1.04/1.29      inference('simplify', [status(thm)], ['185'])).
% 1.04/1.29  thf('187', plain, (((sk_B) != (k1_xboole_0))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('188', plain,
% 1.04/1.29      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 1.04/1.29      inference('simplify_reflect-', [status(thm)], ['186', '187'])).
% 1.04/1.29  thf('189', plain,
% 1.04/1.29      (((k6_relat_1 @ (k1_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 1.04/1.29      inference('sup+', [status(thm)], ['177', '188'])).
% 1.04/1.29  thf('190', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.04/1.29      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.04/1.29  thf('191', plain,
% 1.04/1.29      (((k1_relat_1 @ (k6_relat_1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 1.04/1.29      inference('sup+', [status(thm)], ['189', '190'])).
% 1.04/1.29  thf('192', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.04/1.29      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.04/1.29  thf('193', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.04/1.29      inference('demod', [status(thm)], ['191', '192'])).
% 1.04/1.29  thf('194', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.04/1.29      inference('simplify', [status(thm)], ['132'])).
% 1.04/1.29  thf('195', plain,
% 1.04/1.29      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 1.04/1.29        | ((sk_A) = (k1_xboole_0))
% 1.04/1.29        | ((sk_A) != (sk_A))
% 1.04/1.29        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.04/1.29      inference('demod', [status(thm)],
% 1.04/1.29                ['138', '139', '140', '141', '142', '143', '144', '145', 
% 1.04/1.29                 '146', '147', '148', '149', '150', '151', '152', '193', '194'])).
% 1.04/1.29  thf('196', plain,
% 1.04/1.29      ((((sk_D) = (k2_funct_1 @ sk_C)) | ((sk_A) = (k1_xboole_0)))),
% 1.04/1.29      inference('simplify', [status(thm)], ['195'])).
% 1.04/1.29  thf('197', plain, (((sk_A) != (k1_xboole_0))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('198', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('199', plain, ($false),
% 1.04/1.29      inference('simplify_reflect-', [status(thm)], ['196', '197', '198'])).
% 1.04/1.29  
% 1.04/1.29  % SZS output end Refutation
% 1.04/1.29  
% 1.04/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
