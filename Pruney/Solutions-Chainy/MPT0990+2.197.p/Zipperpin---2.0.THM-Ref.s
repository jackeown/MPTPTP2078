%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pGTkCvDgv6

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:28 EST 2020

% Result     : Theorem 1.11s
% Output     : Refutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :  211 (4958 expanded)
%              Number of leaves         :   45 (1440 expanded)
%              Depth                    :   28
%              Number of atoms          : 2100 (137714 expanded)
%              Number of equality atoms :  159 (9253 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
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
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X8 @ X9 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf('35',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( ( X38 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X38 @ X39 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( v2_funct_1 @ X37 )
      | ~ ( zip_tseitin_0 @ X37 @ X36 ) ) ),
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

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('93',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('94',plain,(
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

thf('95',plain,(
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

thf('96',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('97',plain,(
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
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','45','46','47','48'])).

thf('101',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','101','102','103'])).

thf('105',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['89','90'])).

thf('109',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['93','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('112',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['89','90'])).

thf('114',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('115',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('116',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('118',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['92','118'])).

thf('120',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('122',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X8 @ X9 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('123',plain,(
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
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
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
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
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
    inference('sup-',[status(thm)],['120','124'])).

thf('126',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('127',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['58','59'])).

thf('128',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('129',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['89','90'])).

thf('131',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['119'])).

thf('132',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('133',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['119'])).

thf('134',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['119'])).

thf('136',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','45','46','47','48'])).

thf('138',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['119'])).

thf('139',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
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
    inference(demod,[status(thm)],['95','96'])).

thf('142',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['142','143','144','145','146'])).

thf('148',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['139','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['151','152','153','154'])).

thf('156',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('157',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('159',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['119'])).

thf('161',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['125','126','127','128','129','130','131','132','133','134','135','136','137','138','159','160'])).

thf('162',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['162','163'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pGTkCvDgv6
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.11/1.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.11/1.32  % Solved by: fo/fo7.sh
% 1.11/1.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.11/1.32  % done 1171 iterations in 0.854s
% 1.11/1.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.11/1.32  % SZS output start Refutation
% 1.11/1.32  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.11/1.32  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.11/1.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.11/1.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.11/1.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.11/1.32  thf(sk_B_type, type, sk_B: $i).
% 1.11/1.32  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.11/1.32  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.11/1.32  thf(sk_A_type, type, sk_A: $i).
% 1.11/1.32  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.11/1.32  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.11/1.32  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.11/1.32  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.11/1.32  thf(sk_C_type, type, sk_C: $i).
% 1.11/1.32  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.11/1.32  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.11/1.32  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.11/1.32  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.11/1.32  thf(sk_D_type, type, sk_D: $i).
% 1.11/1.32  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.11/1.32  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.11/1.32  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.11/1.32  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.11/1.32  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.11/1.32  thf(t36_funct_2, conjecture,
% 1.11/1.32    (![A:$i,B:$i,C:$i]:
% 1.11/1.32     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.11/1.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.11/1.32       ( ![D:$i]:
% 1.11/1.32         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.11/1.32             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.11/1.32           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.11/1.32               ( r2_relset_1 @
% 1.11/1.32                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.11/1.32                 ( k6_partfun1 @ A ) ) & 
% 1.11/1.32               ( v2_funct_1 @ C ) ) =>
% 1.11/1.32             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.11/1.32               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.11/1.32  thf(zf_stmt_0, negated_conjecture,
% 1.11/1.32    (~( ![A:$i,B:$i,C:$i]:
% 1.11/1.32        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.11/1.32            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.11/1.32          ( ![D:$i]:
% 1.11/1.32            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.11/1.32                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.11/1.32              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.11/1.32                  ( r2_relset_1 @
% 1.11/1.32                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.11/1.32                    ( k6_partfun1 @ A ) ) & 
% 1.11/1.32                  ( v2_funct_1 @ C ) ) =>
% 1.11/1.32                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.11/1.32                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.11/1.32    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.11/1.32  thf('0', plain,
% 1.11/1.32      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.11/1.32        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.11/1.32        (k6_partfun1 @ sk_A))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf(redefinition_k6_partfun1, axiom,
% 1.11/1.32    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.11/1.32  thf('1', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 1.11/1.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.11/1.32  thf('2', plain,
% 1.11/1.32      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.11/1.32        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.11/1.32        (k6_relat_1 @ sk_A))),
% 1.11/1.32      inference('demod', [status(thm)], ['0', '1'])).
% 1.11/1.32  thf('3', plain,
% 1.11/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('4', plain,
% 1.11/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf(redefinition_k1_partfun1, axiom,
% 1.11/1.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.11/1.32     ( ( ( v1_funct_1 @ E ) & 
% 1.11/1.32         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.11/1.32         ( v1_funct_1 @ F ) & 
% 1.11/1.32         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.11/1.32       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.11/1.32  thf('5', plain,
% 1.11/1.32      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.11/1.32         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.11/1.32          | ~ (v1_funct_1 @ X25)
% 1.11/1.32          | ~ (v1_funct_1 @ X28)
% 1.11/1.32          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.11/1.32          | ((k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 1.11/1.32              = (k5_relat_1 @ X25 @ X28)))),
% 1.11/1.32      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.11/1.32  thf('6', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.11/1.32         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.11/1.32            = (k5_relat_1 @ sk_C @ X0))
% 1.11/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.11/1.32          | ~ (v1_funct_1 @ X0)
% 1.11/1.32          | ~ (v1_funct_1 @ sk_C))),
% 1.11/1.32      inference('sup-', [status(thm)], ['4', '5'])).
% 1.11/1.32  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('8', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.11/1.32         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.11/1.32            = (k5_relat_1 @ sk_C @ X0))
% 1.11/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.11/1.32          | ~ (v1_funct_1 @ X0))),
% 1.11/1.32      inference('demod', [status(thm)], ['6', '7'])).
% 1.11/1.32  thf('9', plain,
% 1.11/1.32      ((~ (v1_funct_1 @ sk_D)
% 1.11/1.32        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.11/1.32            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.11/1.32      inference('sup-', [status(thm)], ['3', '8'])).
% 1.11/1.32  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('11', plain,
% 1.11/1.32      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.11/1.32         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.11/1.32      inference('demod', [status(thm)], ['9', '10'])).
% 1.11/1.32  thf('12', plain,
% 1.11/1.32      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.11/1.32        (k6_relat_1 @ sk_A))),
% 1.11/1.32      inference('demod', [status(thm)], ['2', '11'])).
% 1.11/1.32  thf('13', plain,
% 1.11/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('14', plain,
% 1.11/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf(dt_k1_partfun1, axiom,
% 1.11/1.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.11/1.32     ( ( ( v1_funct_1 @ E ) & 
% 1.11/1.32         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.11/1.32         ( v1_funct_1 @ F ) & 
% 1.11/1.32         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.11/1.32       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.11/1.32         ( m1_subset_1 @
% 1.11/1.32           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.11/1.32           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.11/1.32  thf('15', plain,
% 1.11/1.32      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.11/1.32         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.11/1.32          | ~ (v1_funct_1 @ X17)
% 1.11/1.32          | ~ (v1_funct_1 @ X20)
% 1.11/1.32          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.11/1.32          | (m1_subset_1 @ (k1_partfun1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20) @ 
% 1.11/1.32             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X22))))),
% 1.11/1.32      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.11/1.32  thf('16', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.11/1.32         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.11/1.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.11/1.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.11/1.32          | ~ (v1_funct_1 @ X1)
% 1.11/1.32          | ~ (v1_funct_1 @ sk_C))),
% 1.11/1.32      inference('sup-', [status(thm)], ['14', '15'])).
% 1.11/1.32  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('18', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.11/1.32         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.11/1.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.11/1.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.11/1.32          | ~ (v1_funct_1 @ X1))),
% 1.11/1.32      inference('demod', [status(thm)], ['16', '17'])).
% 1.11/1.32  thf('19', plain,
% 1.11/1.32      ((~ (v1_funct_1 @ sk_D)
% 1.11/1.32        | (m1_subset_1 @ 
% 1.11/1.32           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.11/1.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.11/1.32      inference('sup-', [status(thm)], ['13', '18'])).
% 1.11/1.32  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('21', plain,
% 1.11/1.32      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.11/1.32         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.11/1.32      inference('demod', [status(thm)], ['9', '10'])).
% 1.11/1.32  thf('22', plain,
% 1.11/1.32      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.11/1.32        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.32      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.11/1.32  thf(redefinition_r2_relset_1, axiom,
% 1.11/1.32    (![A:$i,B:$i,C:$i,D:$i]:
% 1.11/1.32     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.11/1.32         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.11/1.32       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.11/1.32  thf('23', plain,
% 1.11/1.32      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.11/1.32         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.11/1.32          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.11/1.32          | ((X13) = (X16))
% 1.11/1.32          | ~ (r2_relset_1 @ X14 @ X15 @ X13 @ X16))),
% 1.11/1.32      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.11/1.32  thf('24', plain,
% 1.11/1.32      (![X0 : $i]:
% 1.11/1.32         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.11/1.32          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.11/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.11/1.32      inference('sup-', [status(thm)], ['22', '23'])).
% 1.11/1.32  thf('25', plain,
% 1.11/1.32      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.11/1.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.11/1.32        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 1.11/1.32      inference('sup-', [status(thm)], ['12', '24'])).
% 1.11/1.32  thf(dt_k6_partfun1, axiom,
% 1.11/1.32    (![A:$i]:
% 1.11/1.32     ( ( m1_subset_1 @
% 1.11/1.32         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.11/1.32       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.11/1.32  thf('26', plain,
% 1.11/1.32      (![X24 : $i]:
% 1.11/1.32         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 1.11/1.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 1.11/1.32      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.11/1.32  thf('27', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 1.11/1.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.11/1.32  thf('28', plain,
% 1.11/1.32      (![X24 : $i]:
% 1.11/1.32         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 1.11/1.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 1.11/1.32      inference('demod', [status(thm)], ['26', '27'])).
% 1.11/1.32  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.11/1.32      inference('demod', [status(thm)], ['25', '28'])).
% 1.11/1.32  thf(t64_funct_1, axiom,
% 1.11/1.32    (![A:$i]:
% 1.11/1.32     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.11/1.32       ( ![B:$i]:
% 1.11/1.32         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.11/1.32           ( ( ( v2_funct_1 @ A ) & 
% 1.11/1.32               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.11/1.32               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.11/1.32             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.11/1.32  thf('30', plain,
% 1.11/1.32      (![X8 : $i, X9 : $i]:
% 1.11/1.32         (~ (v1_relat_1 @ X8)
% 1.11/1.32          | ~ (v1_funct_1 @ X8)
% 1.11/1.32          | ((X8) = (k2_funct_1 @ X9))
% 1.11/1.32          | ((k5_relat_1 @ X8 @ X9) != (k6_relat_1 @ (k2_relat_1 @ X9)))
% 1.11/1.32          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 1.11/1.32          | ~ (v2_funct_1 @ X9)
% 1.11/1.32          | ~ (v1_funct_1 @ X9)
% 1.11/1.32          | ~ (v1_relat_1 @ X9))),
% 1.11/1.32      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.11/1.32  thf('31', plain,
% 1.11/1.32      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 1.11/1.32        | ~ (v1_relat_1 @ sk_D)
% 1.11/1.32        | ~ (v1_funct_1 @ sk_D)
% 1.11/1.32        | ~ (v2_funct_1 @ sk_D)
% 1.11/1.32        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.11/1.32        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.11/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.11/1.32        | ~ (v1_relat_1 @ sk_C))),
% 1.11/1.32      inference('sup-', [status(thm)], ['29', '30'])).
% 1.11/1.32  thf('32', plain,
% 1.11/1.32      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.11/1.32         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.11/1.32      inference('demod', [status(thm)], ['9', '10'])).
% 1.11/1.32  thf('33', plain,
% 1.11/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf(t24_funct_2, axiom,
% 1.11/1.32    (![A:$i,B:$i,C:$i]:
% 1.11/1.32     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.11/1.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.11/1.32       ( ![D:$i]:
% 1.11/1.32         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.11/1.32             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.11/1.32           ( ( r2_relset_1 @
% 1.11/1.32               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.11/1.32               ( k6_partfun1 @ B ) ) =>
% 1.11/1.32             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.11/1.32  thf('34', plain,
% 1.11/1.32      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.11/1.32         (~ (v1_funct_1 @ X32)
% 1.11/1.32          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 1.11/1.32          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.11/1.32          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 1.11/1.32               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 1.11/1.32               (k6_partfun1 @ X33))
% 1.11/1.32          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 1.11/1.32          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 1.11/1.32          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 1.11/1.32          | ~ (v1_funct_1 @ X35))),
% 1.11/1.32      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.11/1.32  thf('35', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 1.11/1.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.11/1.32  thf('36', plain,
% 1.11/1.32      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.11/1.32         (~ (v1_funct_1 @ X32)
% 1.11/1.32          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 1.11/1.32          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.11/1.32          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 1.11/1.32               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 1.11/1.32               (k6_relat_1 @ X33))
% 1.11/1.32          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 1.11/1.32          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 1.11/1.32          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 1.11/1.32          | ~ (v1_funct_1 @ X35))),
% 1.11/1.32      inference('demod', [status(thm)], ['34', '35'])).
% 1.11/1.32  thf('37', plain,
% 1.11/1.32      (![X0 : $i]:
% 1.11/1.32         (~ (v1_funct_1 @ X0)
% 1.11/1.32          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.11/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.11/1.32          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.11/1.32          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.11/1.32               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.11/1.32               (k6_relat_1 @ sk_A))
% 1.11/1.32          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.11/1.32          | ~ (v1_funct_1 @ sk_C))),
% 1.11/1.32      inference('sup-', [status(thm)], ['33', '36'])).
% 1.11/1.32  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('40', plain,
% 1.11/1.32      (![X0 : $i]:
% 1.11/1.32         (~ (v1_funct_1 @ X0)
% 1.11/1.32          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.11/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.11/1.32          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.11/1.32          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.11/1.32               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.11/1.32               (k6_relat_1 @ sk_A)))),
% 1.11/1.32      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.11/1.32  thf('41', plain,
% 1.11/1.32      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.11/1.32           (k6_relat_1 @ sk_A))
% 1.11/1.32        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.11/1.32        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.11/1.32        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.11/1.32        | ~ (v1_funct_1 @ sk_D))),
% 1.11/1.32      inference('sup-', [status(thm)], ['32', '40'])).
% 1.11/1.32  thf('42', plain,
% 1.11/1.32      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.11/1.32        (k6_relat_1 @ sk_A))),
% 1.11/1.32      inference('demod', [status(thm)], ['2', '11'])).
% 1.11/1.32  thf('43', plain,
% 1.11/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf(redefinition_k2_relset_1, axiom,
% 1.11/1.32    (![A:$i,B:$i,C:$i]:
% 1.11/1.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.11/1.32       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.11/1.32  thf('44', plain,
% 1.11/1.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.11/1.32         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 1.11/1.32          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.11/1.32      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.11/1.32  thf('45', plain,
% 1.11/1.32      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.11/1.32      inference('sup-', [status(thm)], ['43', '44'])).
% 1.11/1.32  thf('46', plain,
% 1.11/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('49', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.11/1.32      inference('demod', [status(thm)], ['41', '42', '45', '46', '47', '48'])).
% 1.11/1.32  thf('50', plain,
% 1.11/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf(cc2_relat_1, axiom,
% 1.11/1.32    (![A:$i]:
% 1.11/1.32     ( ( v1_relat_1 @ A ) =>
% 1.11/1.32       ( ![B:$i]:
% 1.11/1.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.11/1.32  thf('51', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.11/1.32          | (v1_relat_1 @ X0)
% 1.11/1.32          | ~ (v1_relat_1 @ X1))),
% 1.11/1.32      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.11/1.32  thf('52', plain,
% 1.11/1.32      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.11/1.32      inference('sup-', [status(thm)], ['50', '51'])).
% 1.11/1.32  thf(fc6_relat_1, axiom,
% 1.11/1.32    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.11/1.32  thf('53', plain,
% 1.11/1.32      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.11/1.32      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.11/1.32  thf('54', plain, ((v1_relat_1 @ sk_D)),
% 1.11/1.32      inference('demod', [status(thm)], ['52', '53'])).
% 1.11/1.32  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('56', plain,
% 1.11/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('57', plain,
% 1.11/1.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.11/1.32         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 1.11/1.32          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.11/1.32      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.11/1.32  thf('58', plain,
% 1.11/1.32      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.11/1.32      inference('sup-', [status(thm)], ['56', '57'])).
% 1.11/1.32  thf('59', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('60', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.11/1.32      inference('sup+', [status(thm)], ['58', '59'])).
% 1.11/1.32  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('62', plain,
% 1.11/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('63', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.11/1.32          | (v1_relat_1 @ X0)
% 1.11/1.32          | ~ (v1_relat_1 @ X1))),
% 1.11/1.32      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.11/1.32  thf('64', plain,
% 1.11/1.32      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.11/1.32      inference('sup-', [status(thm)], ['62', '63'])).
% 1.11/1.32  thf('65', plain,
% 1.11/1.32      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.11/1.32      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.11/1.32  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 1.11/1.32      inference('demod', [status(thm)], ['64', '65'])).
% 1.11/1.32  thf('67', plain,
% 1.11/1.32      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 1.11/1.32        | ~ (v2_funct_1 @ sk_D)
% 1.11/1.32        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.11/1.32        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.11/1.32      inference('demod', [status(thm)],
% 1.11/1.32                ['31', '49', '54', '55', '60', '61', '66'])).
% 1.11/1.32  thf('68', plain,
% 1.11/1.32      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.11/1.32        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.11/1.32        | ~ (v2_funct_1 @ sk_D))),
% 1.11/1.32      inference('simplify', [status(thm)], ['67'])).
% 1.11/1.32  thf('69', plain,
% 1.11/1.32      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.11/1.32         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.11/1.32      inference('demod', [status(thm)], ['9', '10'])).
% 1.11/1.32  thf('70', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.11/1.32      inference('demod', [status(thm)], ['25', '28'])).
% 1.11/1.32  thf('71', plain,
% 1.11/1.32      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.11/1.32         = (k6_relat_1 @ sk_A))),
% 1.11/1.32      inference('demod', [status(thm)], ['69', '70'])).
% 1.11/1.32  thf('72', plain,
% 1.11/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf(t30_funct_2, axiom,
% 1.11/1.32    (![A:$i,B:$i,C:$i,D:$i]:
% 1.11/1.32     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.11/1.32         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.11/1.32       ( ![E:$i]:
% 1.11/1.32         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.11/1.32             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.11/1.32           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.11/1.32               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.11/1.32             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.11/1.32               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.11/1.32  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.11/1.32  thf(zf_stmt_2, axiom,
% 1.11/1.32    (![C:$i,B:$i]:
% 1.11/1.32     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.11/1.32       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.11/1.32  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.11/1.32  thf(zf_stmt_4, axiom,
% 1.11/1.32    (![E:$i,D:$i]:
% 1.11/1.32     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.11/1.32  thf(zf_stmt_5, axiom,
% 1.11/1.32    (![A:$i,B:$i,C:$i,D:$i]:
% 1.11/1.32     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.11/1.32         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.11/1.32       ( ![E:$i]:
% 1.11/1.32         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.11/1.32             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.11/1.32           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.11/1.32               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.11/1.32             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.11/1.32  thf('73', plain,
% 1.11/1.32      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.11/1.32         (~ (v1_funct_1 @ X40)
% 1.11/1.32          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 1.11/1.32          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.11/1.32          | (zip_tseitin_0 @ X40 @ X43)
% 1.11/1.32          | ~ (v2_funct_1 @ (k1_partfun1 @ X44 @ X41 @ X41 @ X42 @ X43 @ X40))
% 1.11/1.32          | (zip_tseitin_1 @ X42 @ X41)
% 1.11/1.32          | ((k2_relset_1 @ X44 @ X41 @ X43) != (X41))
% 1.11/1.32          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X41)))
% 1.11/1.32          | ~ (v1_funct_2 @ X43 @ X44 @ X41)
% 1.11/1.32          | ~ (v1_funct_1 @ X43))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.11/1.32  thf('74', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         (~ (v1_funct_1 @ X0)
% 1.11/1.32          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.11/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.11/1.32          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.11/1.32          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.11/1.32          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.11/1.32          | (zip_tseitin_0 @ sk_D @ X0)
% 1.11/1.32          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.11/1.32          | ~ (v1_funct_1 @ sk_D))),
% 1.11/1.32      inference('sup-', [status(thm)], ['72', '73'])).
% 1.11/1.32  thf('75', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('77', plain,
% 1.11/1.32      (![X0 : $i, X1 : $i]:
% 1.11/1.32         (~ (v1_funct_1 @ X0)
% 1.11/1.32          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.11/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.11/1.32          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.11/1.32          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.11/1.32          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.11/1.32          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.11/1.32      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.11/1.32  thf('78', plain,
% 1.11/1.32      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.11/1.32        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.11/1.32        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.11/1.32        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.11/1.32        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.11/1.32        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.11/1.32        | ~ (v1_funct_1 @ sk_C))),
% 1.11/1.32      inference('sup-', [status(thm)], ['71', '77'])).
% 1.11/1.32  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.11/1.32  thf('79', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 1.11/1.32      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.11/1.32  thf('80', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('81', plain,
% 1.11/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('82', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('84', plain,
% 1.11/1.32      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.11/1.32        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.11/1.32        | ((sk_B) != (sk_B)))),
% 1.11/1.32      inference('demod', [status(thm)], ['78', '79', '80', '81', '82', '83'])).
% 1.11/1.32  thf('85', plain,
% 1.11/1.32      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.11/1.32      inference('simplify', [status(thm)], ['84'])).
% 1.11/1.32  thf('86', plain,
% 1.11/1.32      (![X38 : $i, X39 : $i]:
% 1.11/1.32         (((X38) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X38 @ X39))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.11/1.32  thf('87', plain,
% 1.11/1.32      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.11/1.32      inference('sup-', [status(thm)], ['85', '86'])).
% 1.11/1.32  thf('88', plain, (((sk_A) != (k1_xboole_0))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('89', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.11/1.32      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 1.11/1.32  thf('90', plain,
% 1.11/1.32      (![X36 : $i, X37 : $i]:
% 1.11/1.32         ((v2_funct_1 @ X37) | ~ (zip_tseitin_0 @ X37 @ X36))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.11/1.32  thf('91', plain, ((v2_funct_1 @ sk_D)),
% 1.11/1.32      inference('sup-', [status(thm)], ['89', '90'])).
% 1.11/1.32  thf('92', plain,
% 1.11/1.32      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 1.11/1.32      inference('demod', [status(thm)], ['68', '91'])).
% 1.11/1.32  thf(t61_funct_1, axiom,
% 1.11/1.32    (![A:$i]:
% 1.11/1.32     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.11/1.32       ( ( v2_funct_1 @ A ) =>
% 1.11/1.32         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.11/1.32             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.11/1.32           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.11/1.32             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.11/1.32  thf('93', plain,
% 1.11/1.32      (![X7 : $i]:
% 1.11/1.32         (~ (v2_funct_1 @ X7)
% 1.11/1.32          | ((k5_relat_1 @ X7 @ (k2_funct_1 @ X7))
% 1.11/1.32              = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 1.11/1.32          | ~ (v1_funct_1 @ X7)
% 1.11/1.32          | ~ (v1_relat_1 @ X7))),
% 1.11/1.32      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.11/1.32  thf('94', plain,
% 1.11/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf(t35_funct_2, axiom,
% 1.11/1.32    (![A:$i,B:$i,C:$i]:
% 1.11/1.32     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.11/1.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.11/1.32       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.11/1.32         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.11/1.32           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.11/1.32             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.11/1.32  thf('95', plain,
% 1.11/1.32      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.11/1.32         (((X45) = (k1_xboole_0))
% 1.11/1.32          | ~ (v1_funct_1 @ X46)
% 1.11/1.32          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 1.11/1.32          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 1.11/1.32          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_partfun1 @ X47))
% 1.11/1.32          | ~ (v2_funct_1 @ X46)
% 1.11/1.32          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 1.11/1.32      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.11/1.32  thf('96', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 1.11/1.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.11/1.32  thf('97', plain,
% 1.11/1.32      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.11/1.32         (((X45) = (k1_xboole_0))
% 1.11/1.32          | ~ (v1_funct_1 @ X46)
% 1.11/1.32          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 1.11/1.32          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 1.11/1.32          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_relat_1 @ X47))
% 1.11/1.32          | ~ (v2_funct_1 @ X46)
% 1.11/1.32          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 1.11/1.32      inference('demod', [status(thm)], ['95', '96'])).
% 1.11/1.32  thf('98', plain,
% 1.11/1.32      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.11/1.32        | ~ (v2_funct_1 @ sk_D)
% 1.11/1.32        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.11/1.32        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.11/1.32        | ~ (v1_funct_1 @ sk_D)
% 1.11/1.32        | ((sk_A) = (k1_xboole_0)))),
% 1.11/1.32      inference('sup-', [status(thm)], ['94', '97'])).
% 1.11/1.32  thf('99', plain,
% 1.11/1.32      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.11/1.32      inference('sup-', [status(thm)], ['43', '44'])).
% 1.11/1.32  thf('100', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.11/1.32      inference('demod', [status(thm)], ['41', '42', '45', '46', '47', '48'])).
% 1.11/1.32  thf('101', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 1.11/1.32      inference('demod', [status(thm)], ['99', '100'])).
% 1.11/1.32  thf('102', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('103', plain, ((v1_funct_1 @ sk_D)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('104', plain,
% 1.11/1.32      ((((sk_A) != (sk_A))
% 1.11/1.32        | ~ (v2_funct_1 @ sk_D)
% 1.11/1.32        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.11/1.32        | ((sk_A) = (k1_xboole_0)))),
% 1.11/1.32      inference('demod', [status(thm)], ['98', '101', '102', '103'])).
% 1.11/1.32  thf('105', plain,
% 1.11/1.32      ((((sk_A) = (k1_xboole_0))
% 1.11/1.32        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.11/1.32        | ~ (v2_funct_1 @ sk_D))),
% 1.11/1.32      inference('simplify', [status(thm)], ['104'])).
% 1.11/1.32  thf('106', plain, (((sk_A) != (k1_xboole_0))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('107', plain,
% 1.11/1.32      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.11/1.32        | ~ (v2_funct_1 @ sk_D))),
% 1.11/1.32      inference('simplify_reflect-', [status(thm)], ['105', '106'])).
% 1.11/1.32  thf('108', plain, ((v2_funct_1 @ sk_D)),
% 1.11/1.32      inference('sup-', [status(thm)], ['89', '90'])).
% 1.11/1.32  thf('109', plain,
% 1.11/1.32      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.11/1.32      inference('demod', [status(thm)], ['107', '108'])).
% 1.11/1.32  thf('110', plain,
% 1.11/1.32      ((((k6_relat_1 @ (k1_relat_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.11/1.32        | ~ (v1_relat_1 @ sk_D)
% 1.11/1.32        | ~ (v1_funct_1 @ sk_D)
% 1.11/1.32        | ~ (v2_funct_1 @ sk_D))),
% 1.11/1.32      inference('sup+', [status(thm)], ['93', '109'])).
% 1.11/1.32  thf('111', plain, ((v1_relat_1 @ sk_D)),
% 1.11/1.32      inference('demod', [status(thm)], ['52', '53'])).
% 1.11/1.32  thf('112', plain, ((v1_funct_1 @ sk_D)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('113', plain, ((v2_funct_1 @ sk_D)),
% 1.11/1.32      inference('sup-', [status(thm)], ['89', '90'])).
% 1.11/1.32  thf('114', plain,
% 1.11/1.32      (((k6_relat_1 @ (k1_relat_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.11/1.32      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 1.11/1.32  thf(t71_relat_1, axiom,
% 1.11/1.32    (![A:$i]:
% 1.11/1.32     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.11/1.32       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.11/1.32  thf('115', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.11/1.32      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.11/1.32  thf('116', plain,
% 1.11/1.32      (((k1_relat_1 @ (k6_relat_1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 1.11/1.32      inference('sup+', [status(thm)], ['114', '115'])).
% 1.11/1.32  thf('117', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.11/1.32      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.11/1.32  thf('118', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.11/1.32      inference('demod', [status(thm)], ['116', '117'])).
% 1.11/1.32  thf('119', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 1.11/1.32      inference('demod', [status(thm)], ['92', '118'])).
% 1.11/1.32  thf('120', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.11/1.32      inference('simplify', [status(thm)], ['119'])).
% 1.11/1.32  thf('121', plain,
% 1.11/1.32      (![X7 : $i]:
% 1.11/1.32         (~ (v2_funct_1 @ X7)
% 1.11/1.32          | ((k5_relat_1 @ X7 @ (k2_funct_1 @ X7))
% 1.11/1.32              = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 1.11/1.32          | ~ (v1_funct_1 @ X7)
% 1.11/1.32          | ~ (v1_relat_1 @ X7))),
% 1.11/1.32      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.11/1.32  thf('122', plain,
% 1.11/1.32      (![X8 : $i, X9 : $i]:
% 1.11/1.32         (~ (v1_relat_1 @ X8)
% 1.11/1.32          | ~ (v1_funct_1 @ X8)
% 1.11/1.32          | ((X8) = (k2_funct_1 @ X9))
% 1.11/1.32          | ((k5_relat_1 @ X8 @ X9) != (k6_relat_1 @ (k2_relat_1 @ X9)))
% 1.11/1.32          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 1.11/1.32          | ~ (v2_funct_1 @ X9)
% 1.11/1.32          | ~ (v1_funct_1 @ X9)
% 1.11/1.32          | ~ (v1_relat_1 @ X9))),
% 1.11/1.32      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.11/1.32  thf('123', plain,
% 1.11/1.32      (![X0 : $i]:
% 1.11/1.32         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 1.11/1.32            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.11/1.32          | ~ (v1_relat_1 @ X0)
% 1.11/1.32          | ~ (v1_funct_1 @ X0)
% 1.11/1.32          | ~ (v2_funct_1 @ X0)
% 1.11/1.32          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.11/1.32          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.11/1.32          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.11/1.32          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.11/1.32          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.11/1.32          | ~ (v1_funct_1 @ X0)
% 1.11/1.32          | ~ (v1_relat_1 @ X0))),
% 1.11/1.32      inference('sup-', [status(thm)], ['121', '122'])).
% 1.11/1.32  thf('124', plain,
% 1.11/1.32      (![X0 : $i]:
% 1.11/1.32         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.11/1.32          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.11/1.32          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.11/1.32          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.11/1.32          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.11/1.32          | ~ (v2_funct_1 @ X0)
% 1.11/1.32          | ~ (v1_funct_1 @ X0)
% 1.11/1.32          | ~ (v1_relat_1 @ X0)
% 1.11/1.32          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 1.11/1.32              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.11/1.32      inference('simplify', [status(thm)], ['123'])).
% 1.11/1.32  thf('125', plain,
% 1.11/1.32      ((((k6_relat_1 @ (k1_relat_1 @ sk_D))
% 1.11/1.32          != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 1.11/1.32        | ~ (v1_relat_1 @ sk_D)
% 1.11/1.32        | ~ (v1_funct_1 @ sk_D)
% 1.11/1.32        | ~ (v2_funct_1 @ sk_D)
% 1.11/1.32        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 1.11/1.32        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 1.11/1.32        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 1.11/1.32        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 1.11/1.32        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 1.11/1.32      inference('sup-', [status(thm)], ['120', '124'])).
% 1.11/1.32  thf('126', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.11/1.32      inference('demod', [status(thm)], ['116', '117'])).
% 1.11/1.32  thf('127', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.11/1.32      inference('sup+', [status(thm)], ['58', '59'])).
% 1.11/1.32  thf('128', plain, ((v1_relat_1 @ sk_D)),
% 1.11/1.32      inference('demod', [status(thm)], ['52', '53'])).
% 1.11/1.32  thf('129', plain, ((v1_funct_1 @ sk_D)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('130', plain, ((v2_funct_1 @ sk_D)),
% 1.11/1.32      inference('sup-', [status(thm)], ['89', '90'])).
% 1.11/1.32  thf('131', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.11/1.32      inference('simplify', [status(thm)], ['119'])).
% 1.11/1.32  thf('132', plain, ((v1_relat_1 @ sk_C)),
% 1.11/1.32      inference('demod', [status(thm)], ['64', '65'])).
% 1.11/1.32  thf('133', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.11/1.32      inference('simplify', [status(thm)], ['119'])).
% 1.11/1.32  thf('134', plain, ((v1_funct_1 @ sk_C)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('135', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.11/1.32      inference('simplify', [status(thm)], ['119'])).
% 1.11/1.32  thf('136', plain, ((v2_funct_1 @ sk_C)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('137', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.11/1.32      inference('demod', [status(thm)], ['41', '42', '45', '46', '47', '48'])).
% 1.11/1.32  thf('138', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.11/1.32      inference('simplify', [status(thm)], ['119'])).
% 1.11/1.32  thf('139', plain,
% 1.11/1.32      (![X7 : $i]:
% 1.11/1.32         (~ (v2_funct_1 @ X7)
% 1.11/1.32          | ((k5_relat_1 @ X7 @ (k2_funct_1 @ X7))
% 1.11/1.32              = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 1.11/1.32          | ~ (v1_funct_1 @ X7)
% 1.11/1.32          | ~ (v1_relat_1 @ X7))),
% 1.11/1.32      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.11/1.32  thf('140', plain,
% 1.11/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('141', plain,
% 1.11/1.32      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.11/1.32         (((X45) = (k1_xboole_0))
% 1.11/1.32          | ~ (v1_funct_1 @ X46)
% 1.11/1.32          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 1.11/1.32          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 1.11/1.32          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_relat_1 @ X47))
% 1.11/1.32          | ~ (v2_funct_1 @ X46)
% 1.11/1.32          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 1.11/1.32      inference('demod', [status(thm)], ['95', '96'])).
% 1.11/1.32  thf('142', plain,
% 1.11/1.32      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.11/1.32        | ~ (v2_funct_1 @ sk_C)
% 1.11/1.32        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.11/1.32        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.11/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.11/1.32        | ((sk_B) = (k1_xboole_0)))),
% 1.11/1.32      inference('sup-', [status(thm)], ['140', '141'])).
% 1.11/1.32  thf('143', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('145', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('147', plain,
% 1.11/1.32      ((((sk_B) != (sk_B))
% 1.11/1.32        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.11/1.32        | ((sk_B) = (k1_xboole_0)))),
% 1.11/1.32      inference('demod', [status(thm)], ['142', '143', '144', '145', '146'])).
% 1.11/1.32  thf('148', plain,
% 1.11/1.32      ((((sk_B) = (k1_xboole_0))
% 1.11/1.32        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 1.11/1.32      inference('simplify', [status(thm)], ['147'])).
% 1.11/1.32  thf('149', plain, (((sk_B) != (k1_xboole_0))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('150', plain,
% 1.11/1.32      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 1.11/1.32      inference('simplify_reflect-', [status(thm)], ['148', '149'])).
% 1.11/1.32  thf('151', plain,
% 1.11/1.32      ((((k6_relat_1 @ (k1_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.11/1.32        | ~ (v1_relat_1 @ sk_C)
% 1.11/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.11/1.32        | ~ (v2_funct_1 @ sk_C))),
% 1.11/1.32      inference('sup+', [status(thm)], ['139', '150'])).
% 1.11/1.32  thf('152', plain, ((v1_relat_1 @ sk_C)),
% 1.11/1.32      inference('demod', [status(thm)], ['64', '65'])).
% 1.11/1.32  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('154', plain, ((v2_funct_1 @ sk_C)),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('155', plain,
% 1.11/1.32      (((k6_relat_1 @ (k1_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 1.11/1.32      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 1.11/1.32  thf('156', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.11/1.32      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.11/1.32  thf('157', plain,
% 1.11/1.32      (((k1_relat_1 @ (k6_relat_1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 1.11/1.32      inference('sup+', [status(thm)], ['155', '156'])).
% 1.11/1.32  thf('158', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.11/1.32      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.11/1.32  thf('159', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.11/1.32      inference('demod', [status(thm)], ['157', '158'])).
% 1.11/1.32  thf('160', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.11/1.32      inference('simplify', [status(thm)], ['119'])).
% 1.11/1.32  thf('161', plain,
% 1.11/1.32      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 1.11/1.32        | ((sk_A) != (sk_A))
% 1.11/1.32        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.11/1.32      inference('demod', [status(thm)],
% 1.11/1.32                ['125', '126', '127', '128', '129', '130', '131', '132', 
% 1.11/1.32                 '133', '134', '135', '136', '137', '138', '159', '160'])).
% 1.11/1.32  thf('162', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.11/1.32      inference('simplify', [status(thm)], ['161'])).
% 1.11/1.32  thf('163', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.11/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.32  thf('164', plain, ($false),
% 1.11/1.32      inference('simplify_reflect-', [status(thm)], ['162', '163'])).
% 1.11/1.32  
% 1.11/1.32  % SZS output end Refutation
% 1.11/1.32  
% 1.11/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
