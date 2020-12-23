%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LGPn0TL9yI

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:10 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  206 (4892 expanded)
%              Number of leaves         :   44 (1418 expanded)
%              Depth                    :   28
%              Number of atoms          : 2076 (137406 expanded)
%              Number of equality atoms :  159 (9253 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k2_funct_1 @ X5 ) )
      | ( ( k5_relat_1 @ X4 @ X5 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('51',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','49','52','53','58','59','62'])).

thf('64',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('66',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('67',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
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

thf('69',plain,(
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

thf('70',plain,(
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
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('75',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('76',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['74','75','76','77','78','79'])).

thf('81',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('83',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v2_funct_1 @ X36 )
      | ~ ( zip_tseitin_0 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('87',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','87'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('89',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('90',plain,(
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

thf('91',plain,(
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

thf('92',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('93',plain,(
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
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','45','46','47','48'])).

thf('97',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','97','98','99'])).

thf('101',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('105',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['89','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['50','51'])).

thf('108',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('110',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('112',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('114',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['88','114'])).

thf('116',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('118',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k2_funct_1 @ X5 ) )
      | ( ( k5_relat_1 @ X4 @ X5 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('119',plain,(
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
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
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
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
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
    inference('sup-',[status(thm)],['116','120'])).

thf('122',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['56','57'])).

thf('124',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['50','51'])).

thf('125',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('127',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['115'])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('129',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['115'])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['115'])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','45','46','47','48'])).

thf('134',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['115'])).

thf('135',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
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
    inference(demod,[status(thm)],['91','92'])).

thf('138',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['138','139','140','141','142'])).

thf('144',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['135','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('149',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['147','148','149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('153',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('155',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['115'])).

thf('157',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125','126','127','128','129','130','131','132','133','134','155','156'])).

thf('158',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['158','159'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LGPn0TL9yI
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:45:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 1.07/1.23  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.07/1.23  % Solved by: fo/fo7.sh
% 1.07/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.23  % done 1304 iterations in 0.771s
% 1.07/1.23  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.07/1.23  % SZS output start Refutation
% 1.07/1.23  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.07/1.23  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.07/1.23  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.23  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.07/1.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.23  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.07/1.23  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.23  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.23  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.07/1.23  thf(sk_D_type, type, sk_D: $i).
% 1.07/1.23  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.07/1.23  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.07/1.23  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.07/1.23  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.07/1.23  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.07/1.23  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.07/1.23  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.07/1.23  thf(sk_C_type, type, sk_C: $i).
% 1.07/1.23  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.07/1.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.23  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.07/1.23  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.07/1.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.23  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.07/1.23  thf(t36_funct_2, conjecture,
% 1.07/1.23    (![A:$i,B:$i,C:$i]:
% 1.07/1.23     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.23         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.23       ( ![D:$i]:
% 1.07/1.23         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.07/1.23             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.07/1.23           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.07/1.23               ( r2_relset_1 @
% 1.07/1.23                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.07/1.23                 ( k6_partfun1 @ A ) ) & 
% 1.07/1.23               ( v2_funct_1 @ C ) ) =>
% 1.07/1.23             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.07/1.23               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.07/1.23  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.23    (~( ![A:$i,B:$i,C:$i]:
% 1.07/1.23        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.23            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.23          ( ![D:$i]:
% 1.07/1.23            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.07/1.23                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.07/1.23              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.07/1.23                  ( r2_relset_1 @
% 1.07/1.23                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.07/1.23                    ( k6_partfun1 @ A ) ) & 
% 1.07/1.23                  ( v2_funct_1 @ C ) ) =>
% 1.07/1.23                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.07/1.23                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.07/1.23    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.07/1.23  thf('0', plain,
% 1.07/1.23      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.23        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.07/1.23        (k6_partfun1 @ sk_A))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf(redefinition_k6_partfun1, axiom,
% 1.07/1.23    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.07/1.23  thf('1', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.07/1.23      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.23  thf('2', plain,
% 1.07/1.23      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.23        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.07/1.23        (k6_relat_1 @ sk_A))),
% 1.07/1.23      inference('demod', [status(thm)], ['0', '1'])).
% 1.07/1.23  thf('3', plain,
% 1.07/1.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('4', plain,
% 1.07/1.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf(redefinition_k1_partfun1, axiom,
% 1.07/1.23    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.07/1.23     ( ( ( v1_funct_1 @ E ) & 
% 1.07/1.23         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.23         ( v1_funct_1 @ F ) & 
% 1.07/1.23         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.07/1.23       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.07/1.23  thf('5', plain,
% 1.07/1.23      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.07/1.23         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.07/1.23          | ~ (v1_funct_1 @ X24)
% 1.07/1.23          | ~ (v1_funct_1 @ X27)
% 1.07/1.23          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.07/1.23          | ((k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 1.07/1.23              = (k5_relat_1 @ X24 @ X27)))),
% 1.07/1.23      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.07/1.23  thf('6', plain,
% 1.07/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.23         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.07/1.23            = (k5_relat_1 @ sk_C @ X0))
% 1.07/1.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.07/1.23          | ~ (v1_funct_1 @ X0)
% 1.07/1.23          | ~ (v1_funct_1 @ sk_C))),
% 1.07/1.23      inference('sup-', [status(thm)], ['4', '5'])).
% 1.07/1.23  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('8', plain,
% 1.07/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.23         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.07/1.23            = (k5_relat_1 @ sk_C @ X0))
% 1.07/1.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.07/1.23          | ~ (v1_funct_1 @ X0))),
% 1.07/1.23      inference('demod', [status(thm)], ['6', '7'])).
% 1.07/1.23  thf('9', plain,
% 1.07/1.23      ((~ (v1_funct_1 @ sk_D)
% 1.07/1.23        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.07/1.23            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.07/1.23      inference('sup-', [status(thm)], ['3', '8'])).
% 1.07/1.23  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('11', plain,
% 1.07/1.23      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.07/1.23         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.07/1.23      inference('demod', [status(thm)], ['9', '10'])).
% 1.07/1.23  thf('12', plain,
% 1.07/1.23      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.07/1.23        (k6_relat_1 @ sk_A))),
% 1.07/1.23      inference('demod', [status(thm)], ['2', '11'])).
% 1.07/1.23  thf('13', plain,
% 1.07/1.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('14', plain,
% 1.07/1.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf(dt_k1_partfun1, axiom,
% 1.07/1.23    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.07/1.23     ( ( ( v1_funct_1 @ E ) & 
% 1.07/1.23         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.23         ( v1_funct_1 @ F ) & 
% 1.07/1.23         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.07/1.23       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.07/1.23         ( m1_subset_1 @
% 1.07/1.23           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.07/1.23           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.07/1.23  thf('15', plain,
% 1.07/1.23      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.07/1.23         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.07/1.23          | ~ (v1_funct_1 @ X16)
% 1.07/1.23          | ~ (v1_funct_1 @ X19)
% 1.07/1.23          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.07/1.23          | (m1_subset_1 @ (k1_partfun1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19) @ 
% 1.07/1.23             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X21))))),
% 1.07/1.23      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.07/1.23  thf('16', plain,
% 1.07/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.23         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.07/1.23           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.07/1.23          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.07/1.23          | ~ (v1_funct_1 @ X1)
% 1.07/1.23          | ~ (v1_funct_1 @ sk_C))),
% 1.07/1.23      inference('sup-', [status(thm)], ['14', '15'])).
% 1.07/1.23  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('18', plain,
% 1.07/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.23         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.07/1.23           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.07/1.23          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.07/1.23          | ~ (v1_funct_1 @ X1))),
% 1.07/1.23      inference('demod', [status(thm)], ['16', '17'])).
% 1.07/1.23  thf('19', plain,
% 1.07/1.23      ((~ (v1_funct_1 @ sk_D)
% 1.07/1.23        | (m1_subset_1 @ 
% 1.07/1.23           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.07/1.23           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.07/1.23      inference('sup-', [status(thm)], ['13', '18'])).
% 1.07/1.23  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('21', plain,
% 1.07/1.23      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.07/1.23         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.07/1.23      inference('demod', [status(thm)], ['9', '10'])).
% 1.07/1.23  thf('22', plain,
% 1.07/1.23      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.07/1.23        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.23      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.07/1.23  thf(redefinition_r2_relset_1, axiom,
% 1.07/1.23    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.23     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.23         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.23       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.07/1.23  thf('23', plain,
% 1.07/1.23      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.07/1.23         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.07/1.23          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.07/1.23          | ((X12) = (X15))
% 1.07/1.23          | ~ (r2_relset_1 @ X13 @ X14 @ X12 @ X15))),
% 1.07/1.23      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.07/1.23  thf('24', plain,
% 1.07/1.23      (![X0 : $i]:
% 1.07/1.23         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.07/1.23          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.07/1.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.07/1.23      inference('sup-', [status(thm)], ['22', '23'])).
% 1.07/1.23  thf('25', plain,
% 1.07/1.23      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.07/1.23           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.07/1.23        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 1.07/1.23      inference('sup-', [status(thm)], ['12', '24'])).
% 1.07/1.23  thf(dt_k6_partfun1, axiom,
% 1.07/1.23    (![A:$i]:
% 1.07/1.23     ( ( m1_subset_1 @
% 1.07/1.23         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.07/1.23       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.07/1.23  thf('26', plain,
% 1.07/1.23      (![X23 : $i]:
% 1.07/1.23         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 1.07/1.23          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 1.07/1.23      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.07/1.23  thf('27', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.07/1.23      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.23  thf('28', plain,
% 1.07/1.23      (![X23 : $i]:
% 1.07/1.23         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 1.07/1.23          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 1.07/1.23      inference('demod', [status(thm)], ['26', '27'])).
% 1.07/1.23  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.07/1.23      inference('demod', [status(thm)], ['25', '28'])).
% 1.07/1.23  thf(t64_funct_1, axiom,
% 1.07/1.23    (![A:$i]:
% 1.07/1.23     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.07/1.23       ( ![B:$i]:
% 1.07/1.23         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.07/1.23           ( ( ( v2_funct_1 @ A ) & 
% 1.07/1.23               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.07/1.23               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.07/1.23             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.07/1.23  thf('30', plain,
% 1.07/1.23      (![X4 : $i, X5 : $i]:
% 1.07/1.23         (~ (v1_relat_1 @ X4)
% 1.07/1.23          | ~ (v1_funct_1 @ X4)
% 1.07/1.23          | ((X4) = (k2_funct_1 @ X5))
% 1.07/1.23          | ((k5_relat_1 @ X4 @ X5) != (k6_relat_1 @ (k2_relat_1 @ X5)))
% 1.07/1.23          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X5))
% 1.07/1.23          | ~ (v2_funct_1 @ X5)
% 1.07/1.23          | ~ (v1_funct_1 @ X5)
% 1.07/1.23          | ~ (v1_relat_1 @ X5))),
% 1.07/1.23      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.07/1.23  thf('31', plain,
% 1.07/1.23      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 1.07/1.23        | ~ (v1_relat_1 @ sk_D)
% 1.07/1.23        | ~ (v1_funct_1 @ sk_D)
% 1.07/1.23        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.23        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.07/1.23        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.07/1.23        | ~ (v1_funct_1 @ sk_C)
% 1.07/1.23        | ~ (v1_relat_1 @ sk_C))),
% 1.07/1.23      inference('sup-', [status(thm)], ['29', '30'])).
% 1.07/1.23  thf('32', plain,
% 1.07/1.23      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.07/1.23         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.07/1.23      inference('demod', [status(thm)], ['9', '10'])).
% 1.07/1.23  thf('33', plain,
% 1.07/1.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf(t24_funct_2, axiom,
% 1.07/1.23    (![A:$i,B:$i,C:$i]:
% 1.07/1.23     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.23         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.23       ( ![D:$i]:
% 1.07/1.23         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.07/1.23             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.07/1.23           ( ( r2_relset_1 @
% 1.07/1.23               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.07/1.23               ( k6_partfun1 @ B ) ) =>
% 1.07/1.23             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.07/1.23  thf('34', plain,
% 1.07/1.23      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.07/1.23         (~ (v1_funct_1 @ X31)
% 1.07/1.23          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 1.07/1.23          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.07/1.23          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 1.07/1.23               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 1.07/1.23               (k6_partfun1 @ X32))
% 1.07/1.23          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 1.07/1.23          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 1.07/1.23          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 1.07/1.23          | ~ (v1_funct_1 @ X34))),
% 1.07/1.23      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.07/1.23  thf('35', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.07/1.23      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.23  thf('36', plain,
% 1.07/1.23      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.07/1.23         (~ (v1_funct_1 @ X31)
% 1.07/1.23          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 1.07/1.23          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.07/1.23          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 1.07/1.23               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 1.07/1.23               (k6_relat_1 @ X32))
% 1.07/1.23          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 1.07/1.23          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 1.07/1.23          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 1.07/1.23          | ~ (v1_funct_1 @ X34))),
% 1.07/1.23      inference('demod', [status(thm)], ['34', '35'])).
% 1.07/1.23  thf('37', plain,
% 1.07/1.23      (![X0 : $i]:
% 1.07/1.23         (~ (v1_funct_1 @ X0)
% 1.07/1.23          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.07/1.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.07/1.23          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.07/1.23          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.23               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.07/1.23               (k6_relat_1 @ sk_A))
% 1.07/1.23          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.07/1.23          | ~ (v1_funct_1 @ sk_C))),
% 1.07/1.23      inference('sup-', [status(thm)], ['33', '36'])).
% 1.07/1.23  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('40', plain,
% 1.07/1.23      (![X0 : $i]:
% 1.07/1.23         (~ (v1_funct_1 @ X0)
% 1.07/1.23          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.07/1.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.07/1.23          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.07/1.23          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.23               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.07/1.23               (k6_relat_1 @ sk_A)))),
% 1.07/1.23      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.07/1.23  thf('41', plain,
% 1.07/1.23      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.07/1.23           (k6_relat_1 @ sk_A))
% 1.07/1.23        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.07/1.23        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.07/1.23        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.07/1.23        | ~ (v1_funct_1 @ sk_D))),
% 1.07/1.23      inference('sup-', [status(thm)], ['32', '40'])).
% 1.07/1.23  thf('42', plain,
% 1.07/1.23      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.07/1.23        (k6_relat_1 @ sk_A))),
% 1.07/1.23      inference('demod', [status(thm)], ['2', '11'])).
% 1.07/1.23  thf('43', plain,
% 1.07/1.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf(redefinition_k2_relset_1, axiom,
% 1.07/1.23    (![A:$i,B:$i,C:$i]:
% 1.07/1.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.23       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.07/1.23  thf('44', plain,
% 1.07/1.23      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.23         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 1.07/1.23          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.07/1.23      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.07/1.23  thf('45', plain,
% 1.07/1.23      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.07/1.23      inference('sup-', [status(thm)], ['43', '44'])).
% 1.07/1.23  thf('46', plain,
% 1.07/1.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('49', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.07/1.23      inference('demod', [status(thm)], ['41', '42', '45', '46', '47', '48'])).
% 1.07/1.23  thf('50', plain,
% 1.07/1.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf(cc1_relset_1, axiom,
% 1.07/1.23    (![A:$i,B:$i,C:$i]:
% 1.07/1.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.23       ( v1_relat_1 @ C ) ))).
% 1.07/1.23  thf('51', plain,
% 1.07/1.23      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.07/1.23         ((v1_relat_1 @ X6)
% 1.07/1.23          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.07/1.23      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.07/1.23  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.23      inference('sup-', [status(thm)], ['50', '51'])).
% 1.07/1.23  thf('53', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('54', plain,
% 1.07/1.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('55', plain,
% 1.07/1.23      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.23         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 1.07/1.23          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.07/1.23      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.07/1.23  thf('56', plain,
% 1.07/1.23      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.07/1.23      inference('sup-', [status(thm)], ['54', '55'])).
% 1.07/1.23  thf('57', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('58', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.07/1.23      inference('sup+', [status(thm)], ['56', '57'])).
% 1.07/1.23  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('60', plain,
% 1.07/1.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('61', plain,
% 1.07/1.23      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.07/1.23         ((v1_relat_1 @ X6)
% 1.07/1.23          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.07/1.23      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.07/1.23  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.23      inference('sup-', [status(thm)], ['60', '61'])).
% 1.07/1.23  thf('63', plain,
% 1.07/1.23      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 1.07/1.23        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.23        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.07/1.23        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.07/1.23      inference('demod', [status(thm)],
% 1.07/1.23                ['31', '49', '52', '53', '58', '59', '62'])).
% 1.07/1.23  thf('64', plain,
% 1.07/1.23      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.07/1.23        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.07/1.23        | ~ (v2_funct_1 @ sk_D))),
% 1.07/1.23      inference('simplify', [status(thm)], ['63'])).
% 1.07/1.23  thf('65', plain,
% 1.07/1.23      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.07/1.23         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.07/1.23      inference('demod', [status(thm)], ['9', '10'])).
% 1.07/1.23  thf('66', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.07/1.23      inference('demod', [status(thm)], ['25', '28'])).
% 1.07/1.23  thf('67', plain,
% 1.07/1.23      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.07/1.23         = (k6_relat_1 @ sk_A))),
% 1.07/1.23      inference('demod', [status(thm)], ['65', '66'])).
% 1.07/1.23  thf('68', plain,
% 1.07/1.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf(t30_funct_2, axiom,
% 1.07/1.23    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.23     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.23         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.07/1.23       ( ![E:$i]:
% 1.07/1.23         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.07/1.23             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.07/1.23           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.07/1.23               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.07/1.23             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.07/1.23               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.07/1.23  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.07/1.23  thf(zf_stmt_2, axiom,
% 1.07/1.23    (![C:$i,B:$i]:
% 1.07/1.23     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.07/1.23       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.07/1.23  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.07/1.23  thf(zf_stmt_4, axiom,
% 1.07/1.23    (![E:$i,D:$i]:
% 1.07/1.23     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.07/1.23  thf(zf_stmt_5, axiom,
% 1.07/1.23    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.23     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.07/1.23         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.23       ( ![E:$i]:
% 1.07/1.23         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.07/1.23             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.07/1.23           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.07/1.23               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.07/1.23             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.07/1.23  thf('69', plain,
% 1.07/1.23      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.07/1.23         (~ (v1_funct_1 @ X39)
% 1.07/1.23          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 1.07/1.23          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.07/1.23          | (zip_tseitin_0 @ X39 @ X42)
% 1.07/1.23          | ~ (v2_funct_1 @ (k1_partfun1 @ X43 @ X40 @ X40 @ X41 @ X42 @ X39))
% 1.07/1.23          | (zip_tseitin_1 @ X41 @ X40)
% 1.07/1.23          | ((k2_relset_1 @ X43 @ X40 @ X42) != (X40))
% 1.07/1.23          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X40)))
% 1.07/1.23          | ~ (v1_funct_2 @ X42 @ X43 @ X40)
% 1.07/1.23          | ~ (v1_funct_1 @ X42))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.07/1.23  thf('70', plain,
% 1.07/1.23      (![X0 : $i, X1 : $i]:
% 1.07/1.23         (~ (v1_funct_1 @ X0)
% 1.07/1.23          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.07/1.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.07/1.23          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.07/1.23          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.07/1.23          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.07/1.23          | (zip_tseitin_0 @ sk_D @ X0)
% 1.07/1.23          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.07/1.23          | ~ (v1_funct_1 @ sk_D))),
% 1.07/1.23      inference('sup-', [status(thm)], ['68', '69'])).
% 1.07/1.23  thf('71', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('73', plain,
% 1.07/1.23      (![X0 : $i, X1 : $i]:
% 1.07/1.23         (~ (v1_funct_1 @ X0)
% 1.07/1.23          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.07/1.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.07/1.23          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.07/1.23          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.07/1.23          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.07/1.23          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.07/1.23      inference('demod', [status(thm)], ['70', '71', '72'])).
% 1.07/1.23  thf('74', plain,
% 1.07/1.23      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.07/1.23        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.07/1.23        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.07/1.23        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.07/1.23        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.07/1.23        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.07/1.23        | ~ (v1_funct_1 @ sk_C))),
% 1.07/1.23      inference('sup-', [status(thm)], ['67', '73'])).
% 1.07/1.23  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.07/1.23  thf('75', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 1.07/1.23      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.07/1.23  thf('76', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('77', plain,
% 1.07/1.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('78', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('80', plain,
% 1.07/1.23      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.07/1.23        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.07/1.23        | ((sk_B) != (sk_B)))),
% 1.07/1.23      inference('demod', [status(thm)], ['74', '75', '76', '77', '78', '79'])).
% 1.07/1.23  thf('81', plain,
% 1.07/1.23      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.07/1.23      inference('simplify', [status(thm)], ['80'])).
% 1.07/1.23  thf('82', plain,
% 1.07/1.23      (![X37 : $i, X38 : $i]:
% 1.07/1.23         (((X37) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X37 @ X38))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.07/1.23  thf('83', plain,
% 1.07/1.23      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.07/1.23      inference('sup-', [status(thm)], ['81', '82'])).
% 1.07/1.23  thf('84', plain, (((sk_A) != (k1_xboole_0))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('85', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.07/1.23      inference('simplify_reflect-', [status(thm)], ['83', '84'])).
% 1.07/1.23  thf('86', plain,
% 1.07/1.23      (![X35 : $i, X36 : $i]:
% 1.07/1.23         ((v2_funct_1 @ X36) | ~ (zip_tseitin_0 @ X36 @ X35))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.07/1.23  thf('87', plain, ((v2_funct_1 @ sk_D)),
% 1.07/1.23      inference('sup-', [status(thm)], ['85', '86'])).
% 1.07/1.23  thf('88', plain,
% 1.07/1.23      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 1.07/1.23      inference('demod', [status(thm)], ['64', '87'])).
% 1.07/1.23  thf(t61_funct_1, axiom,
% 1.07/1.23    (![A:$i]:
% 1.07/1.23     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.07/1.23       ( ( v2_funct_1 @ A ) =>
% 1.07/1.23         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.07/1.23             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.07/1.23           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.07/1.23             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.07/1.23  thf('89', plain,
% 1.07/1.23      (![X3 : $i]:
% 1.07/1.23         (~ (v2_funct_1 @ X3)
% 1.07/1.23          | ((k5_relat_1 @ X3 @ (k2_funct_1 @ X3))
% 1.07/1.23              = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 1.07/1.23          | ~ (v1_funct_1 @ X3)
% 1.07/1.23          | ~ (v1_relat_1 @ X3))),
% 1.07/1.23      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.07/1.23  thf('90', plain,
% 1.07/1.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf(t35_funct_2, axiom,
% 1.07/1.23    (![A:$i,B:$i,C:$i]:
% 1.07/1.23     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.23         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.23       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.07/1.23         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.07/1.23           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.07/1.23             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.07/1.23  thf('91', plain,
% 1.07/1.23      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.07/1.23         (((X44) = (k1_xboole_0))
% 1.07/1.23          | ~ (v1_funct_1 @ X45)
% 1.07/1.23          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 1.07/1.23          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 1.07/1.23          | ((k5_relat_1 @ X45 @ (k2_funct_1 @ X45)) = (k6_partfun1 @ X46))
% 1.07/1.23          | ~ (v2_funct_1 @ X45)
% 1.07/1.23          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 1.07/1.23      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.07/1.23  thf('92', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.07/1.23      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.23  thf('93', plain,
% 1.07/1.23      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.07/1.23         (((X44) = (k1_xboole_0))
% 1.07/1.23          | ~ (v1_funct_1 @ X45)
% 1.07/1.23          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 1.07/1.23          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 1.07/1.23          | ((k5_relat_1 @ X45 @ (k2_funct_1 @ X45)) = (k6_relat_1 @ X46))
% 1.07/1.23          | ~ (v2_funct_1 @ X45)
% 1.07/1.23          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 1.07/1.23      inference('demod', [status(thm)], ['91', '92'])).
% 1.07/1.23  thf('94', plain,
% 1.07/1.23      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.07/1.23        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.23        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.07/1.23        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.07/1.23        | ~ (v1_funct_1 @ sk_D)
% 1.07/1.23        | ((sk_A) = (k1_xboole_0)))),
% 1.07/1.23      inference('sup-', [status(thm)], ['90', '93'])).
% 1.07/1.23  thf('95', plain,
% 1.07/1.23      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.07/1.23      inference('sup-', [status(thm)], ['43', '44'])).
% 1.07/1.23  thf('96', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.07/1.23      inference('demod', [status(thm)], ['41', '42', '45', '46', '47', '48'])).
% 1.07/1.23  thf('97', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 1.07/1.23      inference('demod', [status(thm)], ['95', '96'])).
% 1.07/1.23  thf('98', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('99', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('100', plain,
% 1.07/1.23      ((((sk_A) != (sk_A))
% 1.07/1.23        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.23        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.07/1.23        | ((sk_A) = (k1_xboole_0)))),
% 1.07/1.23      inference('demod', [status(thm)], ['94', '97', '98', '99'])).
% 1.07/1.23  thf('101', plain,
% 1.07/1.23      ((((sk_A) = (k1_xboole_0))
% 1.07/1.23        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.07/1.23        | ~ (v2_funct_1 @ sk_D))),
% 1.07/1.23      inference('simplify', [status(thm)], ['100'])).
% 1.07/1.23  thf('102', plain, (((sk_A) != (k1_xboole_0))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('103', plain,
% 1.07/1.23      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.07/1.23        | ~ (v2_funct_1 @ sk_D))),
% 1.07/1.23      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 1.07/1.23  thf('104', plain, ((v2_funct_1 @ sk_D)),
% 1.07/1.23      inference('sup-', [status(thm)], ['85', '86'])).
% 1.07/1.23  thf('105', plain,
% 1.07/1.23      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.07/1.23      inference('demod', [status(thm)], ['103', '104'])).
% 1.07/1.23  thf('106', plain,
% 1.07/1.23      ((((k6_relat_1 @ (k1_relat_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.07/1.23        | ~ (v1_relat_1 @ sk_D)
% 1.07/1.23        | ~ (v1_funct_1 @ sk_D)
% 1.07/1.23        | ~ (v2_funct_1 @ sk_D))),
% 1.07/1.23      inference('sup+', [status(thm)], ['89', '105'])).
% 1.07/1.23  thf('107', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.23      inference('sup-', [status(thm)], ['50', '51'])).
% 1.07/1.23  thf('108', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('109', plain, ((v2_funct_1 @ sk_D)),
% 1.07/1.23      inference('sup-', [status(thm)], ['85', '86'])).
% 1.07/1.23  thf('110', plain,
% 1.07/1.23      (((k6_relat_1 @ (k1_relat_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.07/1.23      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 1.07/1.23  thf(t71_relat_1, axiom,
% 1.07/1.23    (![A:$i]:
% 1.07/1.23     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.07/1.23       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.07/1.23  thf('111', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 1.07/1.23      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.07/1.23  thf('112', plain,
% 1.07/1.23      (((k1_relat_1 @ (k6_relat_1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 1.07/1.23      inference('sup+', [status(thm)], ['110', '111'])).
% 1.07/1.23  thf('113', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 1.07/1.23      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.07/1.23  thf('114', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.07/1.23      inference('demod', [status(thm)], ['112', '113'])).
% 1.07/1.23  thf('115', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 1.07/1.23      inference('demod', [status(thm)], ['88', '114'])).
% 1.07/1.23  thf('116', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.07/1.23      inference('simplify', [status(thm)], ['115'])).
% 1.07/1.23  thf('117', plain,
% 1.07/1.23      (![X3 : $i]:
% 1.07/1.23         (~ (v2_funct_1 @ X3)
% 1.07/1.23          | ((k5_relat_1 @ X3 @ (k2_funct_1 @ X3))
% 1.07/1.23              = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 1.07/1.23          | ~ (v1_funct_1 @ X3)
% 1.07/1.23          | ~ (v1_relat_1 @ X3))),
% 1.07/1.23      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.07/1.23  thf('118', plain,
% 1.07/1.23      (![X4 : $i, X5 : $i]:
% 1.07/1.23         (~ (v1_relat_1 @ X4)
% 1.07/1.23          | ~ (v1_funct_1 @ X4)
% 1.07/1.23          | ((X4) = (k2_funct_1 @ X5))
% 1.07/1.23          | ((k5_relat_1 @ X4 @ X5) != (k6_relat_1 @ (k2_relat_1 @ X5)))
% 1.07/1.23          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X5))
% 1.07/1.23          | ~ (v2_funct_1 @ X5)
% 1.07/1.23          | ~ (v1_funct_1 @ X5)
% 1.07/1.23          | ~ (v1_relat_1 @ X5))),
% 1.07/1.23      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.07/1.23  thf('119', plain,
% 1.07/1.23      (![X0 : $i]:
% 1.07/1.23         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 1.07/1.23            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.07/1.23          | ~ (v1_relat_1 @ X0)
% 1.07/1.23          | ~ (v1_funct_1 @ X0)
% 1.07/1.23          | ~ (v2_funct_1 @ X0)
% 1.07/1.23          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.07/1.23          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.23          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.23          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.07/1.23          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.07/1.23          | ~ (v1_funct_1 @ X0)
% 1.07/1.23          | ~ (v1_relat_1 @ X0))),
% 1.07/1.23      inference('sup-', [status(thm)], ['117', '118'])).
% 1.07/1.23  thf('120', plain,
% 1.07/1.23      (![X0 : $i]:
% 1.07/1.23         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.07/1.23          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.07/1.23          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.23          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.23          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.07/1.23          | ~ (v2_funct_1 @ X0)
% 1.07/1.23          | ~ (v1_funct_1 @ X0)
% 1.07/1.23          | ~ (v1_relat_1 @ X0)
% 1.07/1.23          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 1.07/1.23              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.07/1.23      inference('simplify', [status(thm)], ['119'])).
% 1.07/1.23  thf('121', plain,
% 1.07/1.23      ((((k6_relat_1 @ (k1_relat_1 @ sk_D))
% 1.07/1.23          != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 1.07/1.23        | ~ (v1_relat_1 @ sk_D)
% 1.07/1.23        | ~ (v1_funct_1 @ sk_D)
% 1.07/1.23        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.23        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 1.07/1.23        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 1.07/1.23        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 1.07/1.23        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 1.07/1.23        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 1.07/1.23      inference('sup-', [status(thm)], ['116', '120'])).
% 1.07/1.23  thf('122', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.07/1.23      inference('demod', [status(thm)], ['112', '113'])).
% 1.07/1.23  thf('123', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.07/1.23      inference('sup+', [status(thm)], ['56', '57'])).
% 1.07/1.23  thf('124', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.23      inference('sup-', [status(thm)], ['50', '51'])).
% 1.07/1.23  thf('125', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('126', plain, ((v2_funct_1 @ sk_D)),
% 1.07/1.23      inference('sup-', [status(thm)], ['85', '86'])).
% 1.07/1.23  thf('127', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.07/1.23      inference('simplify', [status(thm)], ['115'])).
% 1.07/1.23  thf('128', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.23      inference('sup-', [status(thm)], ['60', '61'])).
% 1.07/1.23  thf('129', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.07/1.23      inference('simplify', [status(thm)], ['115'])).
% 1.07/1.23  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('131', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.07/1.23      inference('simplify', [status(thm)], ['115'])).
% 1.07/1.23  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('133', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.07/1.23      inference('demod', [status(thm)], ['41', '42', '45', '46', '47', '48'])).
% 1.07/1.23  thf('134', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.07/1.23      inference('simplify', [status(thm)], ['115'])).
% 1.07/1.23  thf('135', plain,
% 1.07/1.23      (![X3 : $i]:
% 1.07/1.23         (~ (v2_funct_1 @ X3)
% 1.07/1.23          | ((k5_relat_1 @ X3 @ (k2_funct_1 @ X3))
% 1.07/1.23              = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 1.07/1.23          | ~ (v1_funct_1 @ X3)
% 1.07/1.23          | ~ (v1_relat_1 @ X3))),
% 1.07/1.23      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.07/1.23  thf('136', plain,
% 1.07/1.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('137', plain,
% 1.07/1.23      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.07/1.23         (((X44) = (k1_xboole_0))
% 1.07/1.23          | ~ (v1_funct_1 @ X45)
% 1.07/1.23          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 1.07/1.23          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 1.07/1.23          | ((k5_relat_1 @ X45 @ (k2_funct_1 @ X45)) = (k6_relat_1 @ X46))
% 1.07/1.23          | ~ (v2_funct_1 @ X45)
% 1.07/1.23          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 1.07/1.23      inference('demod', [status(thm)], ['91', '92'])).
% 1.07/1.23  thf('138', plain,
% 1.07/1.23      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.07/1.23        | ~ (v2_funct_1 @ sk_C)
% 1.07/1.23        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.07/1.23        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.07/1.23        | ~ (v1_funct_1 @ sk_C)
% 1.07/1.23        | ((sk_B) = (k1_xboole_0)))),
% 1.07/1.23      inference('sup-', [status(thm)], ['136', '137'])).
% 1.07/1.23  thf('139', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('140', plain, ((v2_funct_1 @ sk_C)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('141', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('142', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('143', plain,
% 1.07/1.23      ((((sk_B) != (sk_B))
% 1.07/1.23        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.07/1.23        | ((sk_B) = (k1_xboole_0)))),
% 1.07/1.23      inference('demod', [status(thm)], ['138', '139', '140', '141', '142'])).
% 1.07/1.23  thf('144', plain,
% 1.07/1.23      ((((sk_B) = (k1_xboole_0))
% 1.07/1.23        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 1.07/1.23      inference('simplify', [status(thm)], ['143'])).
% 1.07/1.23  thf('145', plain, (((sk_B) != (k1_xboole_0))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('146', plain,
% 1.07/1.23      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 1.07/1.23      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 1.07/1.23  thf('147', plain,
% 1.07/1.23      ((((k6_relat_1 @ (k1_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.07/1.23        | ~ (v1_relat_1 @ sk_C)
% 1.07/1.23        | ~ (v1_funct_1 @ sk_C)
% 1.07/1.23        | ~ (v2_funct_1 @ sk_C))),
% 1.07/1.23      inference('sup+', [status(thm)], ['135', '146'])).
% 1.07/1.23  thf('148', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.23      inference('sup-', [status(thm)], ['60', '61'])).
% 1.07/1.23  thf('149', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('150', plain, ((v2_funct_1 @ sk_C)),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('151', plain,
% 1.07/1.23      (((k6_relat_1 @ (k1_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 1.07/1.23      inference('demod', [status(thm)], ['147', '148', '149', '150'])).
% 1.07/1.23  thf('152', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 1.07/1.23      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.07/1.23  thf('153', plain,
% 1.07/1.23      (((k1_relat_1 @ (k6_relat_1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 1.07/1.23      inference('sup+', [status(thm)], ['151', '152'])).
% 1.07/1.23  thf('154', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 1.07/1.23      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.07/1.23  thf('155', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.07/1.23      inference('demod', [status(thm)], ['153', '154'])).
% 1.07/1.23  thf('156', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.07/1.23      inference('simplify', [status(thm)], ['115'])).
% 1.07/1.23  thf('157', plain,
% 1.07/1.23      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 1.07/1.23        | ((sk_A) != (sk_A))
% 1.07/1.23        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.07/1.23      inference('demod', [status(thm)],
% 1.07/1.23                ['121', '122', '123', '124', '125', '126', '127', '128', 
% 1.07/1.23                 '129', '130', '131', '132', '133', '134', '155', '156'])).
% 1.07/1.23  thf('158', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.07/1.23      inference('simplify', [status(thm)], ['157'])).
% 1.07/1.23  thf('159', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.07/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.23  thf('160', plain, ($false),
% 1.07/1.23      inference('simplify_reflect-', [status(thm)], ['158', '159'])).
% 1.07/1.23  
% 1.07/1.23  % SZS output end Refutation
% 1.07/1.23  
% 1.07/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
