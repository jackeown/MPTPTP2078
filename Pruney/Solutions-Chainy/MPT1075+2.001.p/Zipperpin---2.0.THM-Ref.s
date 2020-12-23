%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eyeMgk3xKU

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:26 EST 2020

% Result     : Theorem 7.46s
% Output     : Refutation 7.46s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 232 expanded)
%              Number of leaves         :   43 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          : 1464 (5426 expanded)
%              Number of equality atoms :   51 ( 132 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t192_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ B @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
             => ! [E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) )
                 => ! [F: $i] :
                      ( ( m1_subset_1 @ F @ B )
                     => ( ( v1_partfun1 @ E @ A )
                       => ( ( k3_funct_2 @ B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F )
                          = ( k1_funct_1 @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i,D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ B @ A )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
               => ! [E: $i] :
                    ( ( ( v1_funct_1 @ E )
                      & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) )
                   => ! [F: $i] :
                        ( ( m1_subset_1 @ F @ B )
                       => ( ( v1_partfun1 @ E @ A )
                         => ( ( k3_funct_2 @ B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F )
                            = ( k1_funct_1 @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t192_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_partfun1 @ X16 @ X17 )
      | ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('4',plain,
    ( ( v1_funct_2 @ sk_E @ sk_A @ sk_C )
    | ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_funct_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['4','5','6'])).

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

thf('8',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ~ ( v1_partfun1 @ C @ A ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( v1_partfun1 @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_partfun1])).

thf('18',plain,
    ( ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['12','23'])).

thf('25',plain,
    ( sk_A
    = ( k1_relset_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['9','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t185_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X45 @ X43 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X43 @ X44 @ X47 @ X42 @ X46 ) @ X45 )
        = ( k1_funct_1 @ X46 @ ( k1_funct_1 @ X42 @ X45 ) ) )
      | ( X43 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X43 @ X44 @ X42 ) @ ( k1_relset_1 @ X44 @ X47 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D ) @ ( k1_relset_1 @ sk_A @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_A @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('38',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','44','45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['1','47'])).

thf('49',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('52',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( ( k3_funct_2 @ X39 @ X40 @ X38 @ X41 )
        = ( k1_funct_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F )
    = ( k1_funct_1 @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['49','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ( ( v1_funct_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ A @ C )
        & ( m1_subset_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf('64',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X37 ) ) )
      | ( m1_subset_1 @ ( k8_funct_2 @ X34 @ X35 @ X37 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( ( k3_funct_2 @ X39 @ X40 @ X38 @ X41 )
        = ( k1_funct_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X37 ) ) )
      | ( v1_funct_1 @ ( k8_funct_2 @ X34 @ X35 @ X37 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X37 ) ) )
      | ( v1_funct_2 @ ( k8_funct_2 @ X34 @ X35 @ X37 @ X33 @ X36 ) @ X34 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['84','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','83','93'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['61','96'])).

thf('98',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['60','97'])).

thf('99',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['48','98'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['0','101','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eyeMgk3xKU
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.46/7.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.46/7.67  % Solved by: fo/fo7.sh
% 7.46/7.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.46/7.67  % done 4162 iterations in 7.220s
% 7.46/7.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.46/7.67  % SZS output start Refutation
% 7.46/7.67  thf(sk_F_type, type, sk_F: $i).
% 7.46/7.67  thf(sk_B_type, type, sk_B: $i).
% 7.46/7.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 7.46/7.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 7.46/7.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 7.46/7.67  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 7.46/7.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.46/7.67  thf(sk_D_type, type, sk_D: $i).
% 7.46/7.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 7.46/7.67  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 7.46/7.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.46/7.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.46/7.67  thf(sk_E_type, type, sk_E: $i).
% 7.46/7.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.46/7.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.46/7.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 7.46/7.67  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 7.46/7.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.46/7.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.46/7.67  thf(sk_A_type, type, sk_A: $i).
% 7.46/7.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 7.46/7.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 7.46/7.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 7.46/7.67  thf(sk_C_type, type, sk_C: $i).
% 7.46/7.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.46/7.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.46/7.67  thf(t192_funct_2, conjecture,
% 7.46/7.67    (![A:$i]:
% 7.46/7.67     ( ( ~( v1_xboole_0 @ A ) ) =>
% 7.46/7.67       ( ![B:$i]:
% 7.46/7.67         ( ( ~( v1_xboole_0 @ B ) ) =>
% 7.46/7.67           ( ![C:$i,D:$i]:
% 7.46/7.67             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 7.46/7.67                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 7.46/7.67               ( ![E:$i]:
% 7.46/7.67                 ( ( ( v1_funct_1 @ E ) & 
% 7.46/7.67                     ( m1_subset_1 @
% 7.46/7.67                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 7.46/7.67                   ( ![F:$i]:
% 7.46/7.67                     ( ( m1_subset_1 @ F @ B ) =>
% 7.46/7.67                       ( ( v1_partfun1 @ E @ A ) =>
% 7.46/7.67                         ( ( k3_funct_2 @
% 7.46/7.67                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 7.46/7.67                           ( k1_funct_1 @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.46/7.67  thf(zf_stmt_0, negated_conjecture,
% 7.46/7.67    (~( ![A:$i]:
% 7.46/7.67        ( ( ~( v1_xboole_0 @ A ) ) =>
% 7.46/7.67          ( ![B:$i]:
% 7.46/7.67            ( ( ~( v1_xboole_0 @ B ) ) =>
% 7.46/7.67              ( ![C:$i,D:$i]:
% 7.46/7.67                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 7.46/7.67                    ( m1_subset_1 @
% 7.46/7.67                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 7.46/7.67                  ( ![E:$i]:
% 7.46/7.67                    ( ( ( v1_funct_1 @ E ) & 
% 7.46/7.67                        ( m1_subset_1 @
% 7.46/7.67                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 7.46/7.67                      ( ![F:$i]:
% 7.46/7.67                        ( ( m1_subset_1 @ F @ B ) =>
% 7.46/7.67                          ( ( v1_partfun1 @ E @ A ) =>
% 7.46/7.67                            ( ( k3_funct_2 @
% 7.46/7.67                                B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 7.46/7.67                              ( k1_funct_1 @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 7.46/7.67    inference('cnf.neg', [status(esa)], [t192_funct_2])).
% 7.46/7.67  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('2', plain,
% 7.46/7.67      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf(cc1_funct_2, axiom,
% 7.46/7.67    (![A:$i,B:$i,C:$i]:
% 7.46/7.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.46/7.67       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 7.46/7.67         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 7.46/7.67  thf('3', plain,
% 7.46/7.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 7.46/7.67         (~ (v1_funct_1 @ X16)
% 7.46/7.67          | ~ (v1_partfun1 @ X16 @ X17)
% 7.46/7.67          | (v1_funct_2 @ X16 @ X17 @ X18)
% 7.46/7.67          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 7.46/7.67      inference('cnf', [status(esa)], [cc1_funct_2])).
% 7.46/7.67  thf('4', plain,
% 7.46/7.67      (((v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 7.46/7.67        | ~ (v1_partfun1 @ sk_E @ sk_A)
% 7.46/7.67        | ~ (v1_funct_1 @ sk_E))),
% 7.46/7.67      inference('sup-', [status(thm)], ['2', '3'])).
% 7.46/7.67  thf('5', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 7.46/7.67      inference('demod', [status(thm)], ['4', '5', '6'])).
% 7.46/7.67  thf(d1_funct_2, axiom,
% 7.46/7.67    (![A:$i,B:$i,C:$i]:
% 7.46/7.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.46/7.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.46/7.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 7.46/7.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 7.46/7.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.46/7.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 7.46/7.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 7.46/7.67  thf(zf_stmt_1, axiom,
% 7.46/7.67    (![C:$i,B:$i,A:$i]:
% 7.46/7.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 7.46/7.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 7.46/7.67  thf('8', plain,
% 7.46/7.67      (![X27 : $i, X28 : $i, X29 : $i]:
% 7.46/7.67         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 7.46/7.67          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 7.46/7.67          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 7.46/7.67  thf('9', plain,
% 7.46/7.67      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_A)
% 7.46/7.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_C @ sk_E)))),
% 7.46/7.67      inference('sup-', [status(thm)], ['7', '8'])).
% 7.46/7.67  thf('10', plain,
% 7.46/7.67      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 7.46/7.67  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 7.46/7.67  thf(zf_stmt_4, axiom,
% 7.46/7.67    (![B:$i,A:$i]:
% 7.46/7.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.46/7.67       ( zip_tseitin_0 @ B @ A ) ))).
% 7.46/7.67  thf(zf_stmt_5, axiom,
% 7.46/7.67    (![A:$i,B:$i,C:$i]:
% 7.46/7.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.46/7.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 7.46/7.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.46/7.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 7.46/7.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 7.46/7.67  thf('11', plain,
% 7.46/7.67      (![X30 : $i, X31 : $i, X32 : $i]:
% 7.46/7.67         (~ (zip_tseitin_0 @ X30 @ X31)
% 7.46/7.67          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 7.46/7.67          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 7.46/7.67  thf('12', plain,
% 7.46/7.67      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 7.46/7.67      inference('sup-', [status(thm)], ['10', '11'])).
% 7.46/7.67  thf('13', plain,
% 7.46/7.67      (![X25 : $i, X26 : $i]:
% 7.46/7.67         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_4])).
% 7.46/7.67  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 7.46/7.67  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 7.46/7.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 7.46/7.67  thf('15', plain,
% 7.46/7.67      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 7.46/7.67      inference('sup+', [status(thm)], ['13', '14'])).
% 7.46/7.67  thf('16', plain,
% 7.46/7.67      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf(cc2_partfun1, axiom,
% 7.46/7.67    (![A:$i,B:$i]:
% 7.46/7.67     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 7.46/7.67       ( ![C:$i]:
% 7.46/7.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.46/7.67           ( ~( v1_partfun1 @ C @ A ) ) ) ) ))).
% 7.46/7.67  thf('17', plain,
% 7.46/7.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 7.46/7.67         ((v1_xboole_0 @ X19)
% 7.46/7.67          | ~ (v1_xboole_0 @ X20)
% 7.46/7.67          | ~ (v1_partfun1 @ X21 @ X19)
% 7.46/7.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 7.46/7.67      inference('cnf', [status(esa)], [cc2_partfun1])).
% 7.46/7.67  thf('18', plain,
% 7.46/7.67      ((~ (v1_partfun1 @ sk_E @ sk_A)
% 7.46/7.67        | ~ (v1_xboole_0 @ sk_C)
% 7.46/7.67        | (v1_xboole_0 @ sk_A))),
% 7.46/7.67      inference('sup-', [status(thm)], ['16', '17'])).
% 7.46/7.67  thf('19', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('20', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_A))),
% 7.46/7.67      inference('demod', [status(thm)], ['18', '19'])).
% 7.46/7.67  thf('21', plain, (~ (v1_xboole_0 @ sk_A)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('22', plain, (~ (v1_xboole_0 @ sk_C)),
% 7.46/7.67      inference('clc', [status(thm)], ['20', '21'])).
% 7.46/7.67  thf('23', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 7.46/7.67      inference('sup-', [status(thm)], ['15', '22'])).
% 7.46/7.67  thf('24', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_A)),
% 7.46/7.67      inference('demod', [status(thm)], ['12', '23'])).
% 7.46/7.67  thf('25', plain, (((sk_A) = (k1_relset_1 @ sk_A @ sk_C @ sk_E))),
% 7.46/7.67      inference('demod', [status(thm)], ['9', '24'])).
% 7.46/7.67  thf('26', plain,
% 7.46/7.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf(t185_funct_2, axiom,
% 7.46/7.67    (![A:$i,B:$i,C:$i]:
% 7.46/7.67     ( ( ~( v1_xboole_0 @ C ) ) =>
% 7.46/7.67       ( ![D:$i]:
% 7.46/7.67         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 7.46/7.67             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 7.46/7.67           ( ![E:$i]:
% 7.46/7.67             ( ( ( v1_funct_1 @ E ) & 
% 7.46/7.67                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 7.46/7.67               ( ![F:$i]:
% 7.46/7.67                 ( ( m1_subset_1 @ F @ B ) =>
% 7.46/7.67                   ( ( r1_tarski @
% 7.46/7.67                       ( k2_relset_1 @ B @ C @ D ) @ 
% 7.46/7.67                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 7.46/7.67                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 7.46/7.67                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 7.46/7.67                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.46/7.67  thf('27', plain,
% 7.46/7.67      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 7.46/7.67         (~ (v1_funct_1 @ X42)
% 7.46/7.67          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 7.46/7.67          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 7.46/7.67          | ~ (m1_subset_1 @ X45 @ X43)
% 7.46/7.67          | ((k1_funct_1 @ (k8_funct_2 @ X43 @ X44 @ X47 @ X42 @ X46) @ X45)
% 7.46/7.67              = (k1_funct_1 @ X46 @ (k1_funct_1 @ X42 @ X45)))
% 7.46/7.67          | ((X43) = (k1_xboole_0))
% 7.46/7.67          | ~ (r1_tarski @ (k2_relset_1 @ X43 @ X44 @ X42) @ 
% 7.46/7.67               (k1_relset_1 @ X44 @ X47 @ X46))
% 7.46/7.67          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X47)))
% 7.46/7.67          | ~ (v1_funct_1 @ X46)
% 7.46/7.67          | (v1_xboole_0 @ X44))),
% 7.46/7.67      inference('cnf', [status(esa)], [t185_funct_2])).
% 7.46/7.67  thf('28', plain,
% 7.46/7.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.46/7.67         ((v1_xboole_0 @ sk_A)
% 7.46/7.67          | ~ (v1_funct_1 @ X0)
% 7.46/7.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 7.46/7.67          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_A @ sk_D) @ 
% 7.46/7.67               (k1_relset_1 @ sk_A @ X1 @ X0))
% 7.46/7.67          | ((sk_B) = (k1_xboole_0))
% 7.46/7.67          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 7.46/7.67              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 7.46/7.67          | ~ (m1_subset_1 @ X2 @ sk_B)
% 7.46/7.67          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 7.46/7.67          | ~ (v1_funct_1 @ sk_D))),
% 7.46/7.67      inference('sup-', [status(thm)], ['26', '27'])).
% 7.46/7.67  thf('29', plain,
% 7.46/7.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf(redefinition_k2_relset_1, axiom,
% 7.46/7.67    (![A:$i,B:$i,C:$i]:
% 7.46/7.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.46/7.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 7.46/7.67  thf('30', plain,
% 7.46/7.67      (![X13 : $i, X14 : $i, X15 : $i]:
% 7.46/7.67         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 7.46/7.67          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 7.46/7.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 7.46/7.67  thf('31', plain,
% 7.46/7.67      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 7.46/7.67      inference('sup-', [status(thm)], ['29', '30'])).
% 7.46/7.67  thf('32', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('34', plain,
% 7.46/7.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.46/7.67         ((v1_xboole_0 @ sk_A)
% 7.46/7.67          | ~ (v1_funct_1 @ X0)
% 7.46/7.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 7.46/7.67          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_A @ X1 @ X0))
% 7.46/7.67          | ((sk_B) = (k1_xboole_0))
% 7.46/7.67          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 7.46/7.67              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 7.46/7.67          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 7.46/7.67      inference('demod', [status(thm)], ['28', '31', '32', '33'])).
% 7.46/7.67  thf('35', plain,
% 7.46/7.67      (![X0 : $i]:
% 7.46/7.67         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)
% 7.46/7.67          | ~ (m1_subset_1 @ X0 @ sk_B)
% 7.46/7.67          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 7.46/7.67              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 7.46/7.67          | ((sk_B) = (k1_xboole_0))
% 7.46/7.67          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 7.46/7.67          | ~ (v1_funct_1 @ sk_E)
% 7.46/7.67          | (v1_xboole_0 @ sk_A))),
% 7.46/7.67      inference('sup-', [status(thm)], ['25', '34'])).
% 7.46/7.67  thf('36', plain,
% 7.46/7.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf(cc2_relset_1, axiom,
% 7.46/7.67    (![A:$i,B:$i,C:$i]:
% 7.46/7.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.46/7.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 7.46/7.67  thf('37', plain,
% 7.46/7.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 7.46/7.67         ((v5_relat_1 @ X10 @ X12)
% 7.46/7.67          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 7.46/7.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 7.46/7.67  thf('38', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 7.46/7.67      inference('sup-', [status(thm)], ['36', '37'])).
% 7.46/7.67  thf(d19_relat_1, axiom,
% 7.46/7.67    (![A:$i,B:$i]:
% 7.46/7.67     ( ( v1_relat_1 @ B ) =>
% 7.46/7.67       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 7.46/7.67  thf('39', plain,
% 7.46/7.67      (![X5 : $i, X6 : $i]:
% 7.46/7.67         (~ (v5_relat_1 @ X5 @ X6)
% 7.46/7.67          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 7.46/7.67          | ~ (v1_relat_1 @ X5))),
% 7.46/7.67      inference('cnf', [status(esa)], [d19_relat_1])).
% 7.46/7.67  thf('40', plain,
% 7.46/7.67      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 7.46/7.67      inference('sup-', [status(thm)], ['38', '39'])).
% 7.46/7.67  thf('41', plain,
% 7.46/7.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf(cc1_relset_1, axiom,
% 7.46/7.67    (![A:$i,B:$i,C:$i]:
% 7.46/7.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.46/7.67       ( v1_relat_1 @ C ) ))).
% 7.46/7.67  thf('42', plain,
% 7.46/7.67      (![X7 : $i, X8 : $i, X9 : $i]:
% 7.46/7.67         ((v1_relat_1 @ X7)
% 7.46/7.67          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 7.46/7.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.46/7.67  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 7.46/7.67      inference('sup-', [status(thm)], ['41', '42'])).
% 7.46/7.67  thf('44', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 7.46/7.67      inference('demod', [status(thm)], ['40', '43'])).
% 7.46/7.67  thf('45', plain,
% 7.46/7.67      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('46', plain, ((v1_funct_1 @ sk_E)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('47', plain,
% 7.46/7.67      (![X0 : $i]:
% 7.46/7.67         (~ (m1_subset_1 @ X0 @ sk_B)
% 7.46/7.67          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 7.46/7.67              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 7.46/7.67          | ((sk_B) = (k1_xboole_0))
% 7.46/7.67          | (v1_xboole_0 @ sk_A))),
% 7.46/7.67      inference('demod', [status(thm)], ['35', '44', '45', '46'])).
% 7.46/7.67  thf('48', plain,
% 7.46/7.67      (((v1_xboole_0 @ sk_A)
% 7.46/7.67        | ((sk_B) = (k1_xboole_0))
% 7.46/7.67        | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 7.46/7.67            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 7.46/7.67      inference('sup-', [status(thm)], ['1', '47'])).
% 7.46/7.67  thf('49', plain,
% 7.46/7.67      (((k3_funct_2 @ sk_B @ sk_C @ 
% 7.46/7.67         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 7.46/7.67         != (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('50', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('51', plain,
% 7.46/7.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf(redefinition_k3_funct_2, axiom,
% 7.46/7.67    (![A:$i,B:$i,C:$i,D:$i]:
% 7.46/7.67     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 7.46/7.67         ( v1_funct_2 @ C @ A @ B ) & 
% 7.46/7.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 7.46/7.67         ( m1_subset_1 @ D @ A ) ) =>
% 7.46/7.67       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 7.46/7.67  thf('52', plain,
% 7.46/7.67      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 7.46/7.67         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 7.46/7.67          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 7.46/7.67          | ~ (v1_funct_1 @ X38)
% 7.46/7.67          | (v1_xboole_0 @ X39)
% 7.46/7.67          | ~ (m1_subset_1 @ X41 @ X39)
% 7.46/7.67          | ((k3_funct_2 @ X39 @ X40 @ X38 @ X41) = (k1_funct_1 @ X38 @ X41)))),
% 7.46/7.67      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 7.46/7.67  thf('53', plain,
% 7.46/7.67      (![X0 : $i]:
% 7.46/7.67         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 7.46/7.67          | ~ (m1_subset_1 @ X0 @ sk_B)
% 7.46/7.67          | (v1_xboole_0 @ sk_B)
% 7.46/7.67          | ~ (v1_funct_1 @ sk_D)
% 7.46/7.67          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 7.46/7.67      inference('sup-', [status(thm)], ['51', '52'])).
% 7.46/7.67  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('55', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('56', plain,
% 7.46/7.67      (![X0 : $i]:
% 7.46/7.67         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 7.46/7.67          | ~ (m1_subset_1 @ X0 @ sk_B)
% 7.46/7.67          | (v1_xboole_0 @ sk_B))),
% 7.46/7.67      inference('demod', [status(thm)], ['53', '54', '55'])).
% 7.46/7.67  thf('57', plain, (~ (v1_xboole_0 @ sk_B)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('58', plain,
% 7.46/7.67      (![X0 : $i]:
% 7.46/7.67         (~ (m1_subset_1 @ X0 @ sk_B)
% 7.46/7.67          | ((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 7.46/7.67      inference('clc', [status(thm)], ['56', '57'])).
% 7.46/7.67  thf('59', plain,
% 7.46/7.67      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 7.46/7.67      inference('sup-', [status(thm)], ['50', '58'])).
% 7.46/7.67  thf('60', plain,
% 7.46/7.67      (((k3_funct_2 @ sk_B @ sk_C @ 
% 7.46/7.67         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 7.46/7.67         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 7.46/7.67      inference('demod', [status(thm)], ['49', '59'])).
% 7.46/7.67  thf('61', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('62', plain,
% 7.46/7.67      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('63', plain,
% 7.46/7.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf(dt_k8_funct_2, axiom,
% 7.46/7.67    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 7.46/7.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 7.46/7.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 7.46/7.67         ( v1_funct_1 @ E ) & 
% 7.46/7.67         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 7.46/7.67       ( ( v1_funct_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) ) & 
% 7.46/7.67         ( v1_funct_2 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ A @ C ) & 
% 7.46/7.67         ( m1_subset_1 @
% 7.46/7.67           ( k8_funct_2 @ A @ B @ C @ D @ E ) @ 
% 7.46/7.67           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 7.46/7.67  thf('64', plain,
% 7.46/7.67      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 7.46/7.67         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 7.46/7.67          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 7.46/7.67          | ~ (v1_funct_1 @ X33)
% 7.46/7.67          | ~ (v1_funct_1 @ X36)
% 7.46/7.67          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X37)))
% 7.46/7.67          | (m1_subset_1 @ (k8_funct_2 @ X34 @ X35 @ X37 @ X33 @ X36) @ 
% 7.46/7.67             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X37))))),
% 7.46/7.67      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 7.46/7.67  thf('65', plain,
% 7.46/7.67      (![X0 : $i, X1 : $i]:
% 7.46/7.67         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 7.46/7.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 7.46/7.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 7.46/7.67          | ~ (v1_funct_1 @ X1)
% 7.46/7.67          | ~ (v1_funct_1 @ sk_D)
% 7.46/7.67          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 7.46/7.67      inference('sup-', [status(thm)], ['63', '64'])).
% 7.46/7.67  thf('66', plain, ((v1_funct_1 @ sk_D)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('67', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('68', plain,
% 7.46/7.67      (![X0 : $i, X1 : $i]:
% 7.46/7.67         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 7.46/7.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 7.46/7.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 7.46/7.67          | ~ (v1_funct_1 @ X1))),
% 7.46/7.67      inference('demod', [status(thm)], ['65', '66', '67'])).
% 7.46/7.67  thf('69', plain,
% 7.46/7.67      ((~ (v1_funct_1 @ sk_E)
% 7.46/7.67        | (m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 7.46/7.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 7.46/7.67      inference('sup-', [status(thm)], ['62', '68'])).
% 7.46/7.67  thf('70', plain, ((v1_funct_1 @ sk_E)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('71', plain,
% 7.46/7.67      ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 7.46/7.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 7.46/7.67      inference('demod', [status(thm)], ['69', '70'])).
% 7.46/7.67  thf('72', plain,
% 7.46/7.67      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 7.46/7.67         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 7.46/7.67          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 7.46/7.67          | ~ (v1_funct_1 @ X38)
% 7.46/7.67          | (v1_xboole_0 @ X39)
% 7.46/7.67          | ~ (m1_subset_1 @ X41 @ X39)
% 7.46/7.67          | ((k3_funct_2 @ X39 @ X40 @ X38 @ X41) = (k1_funct_1 @ X38 @ X41)))),
% 7.46/7.67      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 7.46/7.67  thf('73', plain,
% 7.46/7.67      (![X0 : $i]:
% 7.46/7.67         (((k3_funct_2 @ sk_B @ sk_C @ 
% 7.46/7.67            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 7.46/7.67            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 7.46/7.67               X0))
% 7.46/7.67          | ~ (m1_subset_1 @ X0 @ sk_B)
% 7.46/7.67          | (v1_xboole_0 @ sk_B)
% 7.46/7.67          | ~ (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))
% 7.46/7.67          | ~ (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 7.46/7.67               sk_B @ sk_C))),
% 7.46/7.67      inference('sup-', [status(thm)], ['71', '72'])).
% 7.46/7.67  thf('74', plain,
% 7.46/7.67      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('75', plain,
% 7.46/7.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('76', plain,
% 7.46/7.67      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 7.46/7.67         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 7.46/7.67          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 7.46/7.67          | ~ (v1_funct_1 @ X33)
% 7.46/7.67          | ~ (v1_funct_1 @ X36)
% 7.46/7.67          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X37)))
% 7.46/7.67          | (v1_funct_1 @ (k8_funct_2 @ X34 @ X35 @ X37 @ X33 @ X36)))),
% 7.46/7.67      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 7.46/7.67  thf('77', plain,
% 7.46/7.67      (![X0 : $i, X1 : $i]:
% 7.46/7.67         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 7.46/7.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 7.46/7.67          | ~ (v1_funct_1 @ X0)
% 7.46/7.67          | ~ (v1_funct_1 @ sk_D)
% 7.46/7.67          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 7.46/7.67      inference('sup-', [status(thm)], ['75', '76'])).
% 7.46/7.67  thf('78', plain, ((v1_funct_1 @ sk_D)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('79', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('80', plain,
% 7.46/7.67      (![X0 : $i, X1 : $i]:
% 7.46/7.67         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 7.46/7.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 7.46/7.67          | ~ (v1_funct_1 @ X0))),
% 7.46/7.67      inference('demod', [status(thm)], ['77', '78', '79'])).
% 7.46/7.67  thf('81', plain,
% 7.46/7.67      ((~ (v1_funct_1 @ sk_E)
% 7.46/7.67        | (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E)))),
% 7.46/7.67      inference('sup-', [status(thm)], ['74', '80'])).
% 7.46/7.67  thf('82', plain, ((v1_funct_1 @ sk_E)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('83', plain,
% 7.46/7.67      ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))),
% 7.46/7.67      inference('demod', [status(thm)], ['81', '82'])).
% 7.46/7.67  thf('84', plain,
% 7.46/7.67      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('85', plain,
% 7.46/7.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('86', plain,
% 7.46/7.67      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 7.46/7.67         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 7.46/7.67          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 7.46/7.67          | ~ (v1_funct_1 @ X33)
% 7.46/7.67          | ~ (v1_funct_1 @ X36)
% 7.46/7.67          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X37)))
% 7.46/7.67          | (v1_funct_2 @ (k8_funct_2 @ X34 @ X35 @ X37 @ X33 @ X36) @ X34 @ 
% 7.46/7.67             X37))),
% 7.46/7.67      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 7.46/7.67  thf('87', plain,
% 7.46/7.67      (![X0 : $i, X1 : $i]:
% 7.46/7.67         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 7.46/7.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 7.46/7.67          | ~ (v1_funct_1 @ X1)
% 7.46/7.67          | ~ (v1_funct_1 @ sk_D)
% 7.46/7.67          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 7.46/7.67      inference('sup-', [status(thm)], ['85', '86'])).
% 7.46/7.67  thf('88', plain, ((v1_funct_1 @ sk_D)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('89', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('90', plain,
% 7.46/7.67      (![X0 : $i, X1 : $i]:
% 7.46/7.67         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 7.46/7.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 7.46/7.67          | ~ (v1_funct_1 @ X1))),
% 7.46/7.67      inference('demod', [status(thm)], ['87', '88', '89'])).
% 7.46/7.67  thf('91', plain,
% 7.46/7.67      ((~ (v1_funct_1 @ sk_E)
% 7.46/7.67        | (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 7.46/7.67           sk_B @ sk_C))),
% 7.46/7.67      inference('sup-', [status(thm)], ['84', '90'])).
% 7.46/7.67  thf('92', plain, ((v1_funct_1 @ sk_E)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('93', plain,
% 7.46/7.67      ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_B @ 
% 7.46/7.67        sk_C)),
% 7.46/7.67      inference('demod', [status(thm)], ['91', '92'])).
% 7.46/7.67  thf('94', plain,
% 7.46/7.67      (![X0 : $i]:
% 7.46/7.67         (((k3_funct_2 @ sk_B @ sk_C @ 
% 7.46/7.67            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 7.46/7.67            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 7.46/7.67               X0))
% 7.46/7.67          | ~ (m1_subset_1 @ X0 @ sk_B)
% 7.46/7.67          | (v1_xboole_0 @ sk_B))),
% 7.46/7.67      inference('demod', [status(thm)], ['73', '83', '93'])).
% 7.46/7.67  thf('95', plain, (~ (v1_xboole_0 @ sk_B)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('96', plain,
% 7.46/7.67      (![X0 : $i]:
% 7.46/7.67         (~ (m1_subset_1 @ X0 @ sk_B)
% 7.46/7.67          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 7.46/7.67              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 7.46/7.67              = (k1_funct_1 @ 
% 7.46/7.67                 (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)))),
% 7.46/7.67      inference('clc', [status(thm)], ['94', '95'])).
% 7.46/7.67  thf('97', plain,
% 7.46/7.67      (((k3_funct_2 @ sk_B @ sk_C @ 
% 7.46/7.67         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 7.46/7.67         = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F))),
% 7.46/7.67      inference('sup-', [status(thm)], ['61', '96'])).
% 7.46/7.67  thf('98', plain,
% 7.46/7.67      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 7.46/7.67         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 7.46/7.67      inference('demod', [status(thm)], ['60', '97'])).
% 7.46/7.67  thf('99', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 7.46/7.67      inference('simplify_reflect-', [status(thm)], ['48', '98'])).
% 7.46/7.67  thf('100', plain, (~ (v1_xboole_0 @ sk_A)),
% 7.46/7.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.46/7.67  thf('101', plain, (((sk_B) = (k1_xboole_0))),
% 7.46/7.67      inference('clc', [status(thm)], ['99', '100'])).
% 7.46/7.67  thf('102', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 7.46/7.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 7.46/7.67  thf('103', plain, ($false),
% 7.46/7.67      inference('demod', [status(thm)], ['0', '101', '102'])).
% 7.46/7.67  
% 7.46/7.67  % SZS output end Refutation
% 7.46/7.67  
% 7.50/7.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
