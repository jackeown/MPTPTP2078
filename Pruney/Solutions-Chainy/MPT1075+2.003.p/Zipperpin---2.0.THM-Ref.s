%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GhVRjv7wjy

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:26 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 215 expanded)
%              Number of leaves         :   37 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          : 1406 (5176 expanded)
%              Number of equality atoms :   48 ( 125 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X7 )
      | ( v1_funct_2 @ X6 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( v1_partfun1 @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ X30 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X30 @ X31 @ X34 @ X29 @ X33 ) @ X32 )
        = ( k1_funct_1 @ X33 @ ( k1_funct_1 @ X29 @ X32 ) ) )
      | ( X30 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X30 @ X31 @ X29 ) @ ( k1_relset_1 @ X31 @ X34 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ( v1_xboole_0 @ X31 ) ) ),
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
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D ) @ ( k1_relset_1 @ sk_A @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X3 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('35',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D ) @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','37','38','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['1','40'])).

thf('42',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ X26 )
      | ( ( k3_funct_2 @ X26 @ X27 @ X25 @ X28 )
        = ( k1_funct_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F )
    = ( k1_funct_1 @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['42','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( m1_subset_1 @ ( k8_funct_2 @ X21 @ X22 @ X24 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ X26 )
      | ( ( k3_funct_2 @ X26 @ X27 @ X25 @ X28 )
        = ( k1_funct_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( v1_funct_1 @ ( k8_funct_2 @ X21 @ X22 @ X24 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( v1_funct_2 @ ( k8_funct_2 @ X21 @ X22 @ X24 @ X20 @ X23 ) @ X21 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','76','86'])).

thf('88',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['54','89'])).

thf('91',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['53','90'])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['41','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','94','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GhVRjv7wjy
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:14:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.57/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.79  % Solved by: fo/fo7.sh
% 0.57/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.79  % done 324 iterations in 0.324s
% 0.57/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.79  % SZS output start Refutation
% 0.57/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.79  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.57/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.57/0.79  thf(sk_D_type, type, sk_D: $i).
% 0.57/0.79  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.57/0.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.57/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.57/0.79  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.57/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.57/0.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.57/0.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.57/0.79  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.57/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.79  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.57/0.79  thf(sk_E_type, type, sk_E: $i).
% 0.57/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.57/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.79  thf(sk_F_type, type, sk_F: $i).
% 0.57/0.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.57/0.79  thf(t192_funct_2, conjecture,
% 0.57/0.79    (![A:$i]:
% 0.57/0.79     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.57/0.79       ( ![B:$i]:
% 0.57/0.79         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.57/0.79           ( ![C:$i,D:$i]:
% 0.57/0.79             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.57/0.79                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.57/0.79               ( ![E:$i]:
% 0.57/0.79                 ( ( ( v1_funct_1 @ E ) & 
% 0.57/0.79                     ( m1_subset_1 @
% 0.57/0.79                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.57/0.79                   ( ![F:$i]:
% 0.57/0.79                     ( ( m1_subset_1 @ F @ B ) =>
% 0.57/0.79                       ( ( v1_partfun1 @ E @ A ) =>
% 0.57/0.79                         ( ( k3_funct_2 @
% 0.57/0.79                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.57/0.79                           ( k1_funct_1 @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.57/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.79    (~( ![A:$i]:
% 0.57/0.79        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.57/0.79          ( ![B:$i]:
% 0.57/0.79            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.57/0.79              ( ![C:$i,D:$i]:
% 0.57/0.79                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.57/0.79                    ( m1_subset_1 @
% 0.57/0.79                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.57/0.79                  ( ![E:$i]:
% 0.57/0.79                    ( ( ( v1_funct_1 @ E ) & 
% 0.57/0.79                        ( m1_subset_1 @
% 0.57/0.79                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.57/0.79                      ( ![F:$i]:
% 0.57/0.79                        ( ( m1_subset_1 @ F @ B ) =>
% 0.57/0.79                          ( ( v1_partfun1 @ E @ A ) =>
% 0.57/0.79                            ( ( k3_funct_2 @
% 0.57/0.79                                B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.57/0.79                              ( k1_funct_1 @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.57/0.79    inference('cnf.neg', [status(esa)], [t192_funct_2])).
% 0.57/0.79  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('2', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(cc1_funct_2, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.79       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.57/0.79         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.57/0.79  thf('3', plain,
% 0.57/0.79      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.57/0.79         (~ (v1_funct_1 @ X6)
% 0.57/0.79          | ~ (v1_partfun1 @ X6 @ X7)
% 0.57/0.79          | (v1_funct_2 @ X6 @ X7 @ X8)
% 0.57/0.79          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.57/0.79      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.57/0.79  thf('4', plain,
% 0.57/0.79      (((v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.57/0.79        | ~ (v1_partfun1 @ sk_E @ sk_A)
% 0.57/0.79        | ~ (v1_funct_1 @ sk_E))),
% 0.57/0.79      inference('sup-', [status(thm)], ['2', '3'])).
% 0.57/0.79  thf('5', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.57/0.79      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.57/0.79  thf(d1_funct_2, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.79       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.57/0.79           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.57/0.79             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.57/0.79         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.57/0.79           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.57/0.79             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.57/0.79  thf(zf_stmt_1, axiom,
% 0.57/0.79    (![C:$i,B:$i,A:$i]:
% 0.57/0.79     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.57/0.79       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.57/0.79  thf('8', plain,
% 0.57/0.79      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.57/0.79         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.57/0.79          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 0.57/0.79          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.57/0.79  thf('9', plain,
% 0.57/0.79      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_A)
% 0.57/0.79        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_C @ sk_E)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['7', '8'])).
% 0.57/0.79  thf('10', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.57/0.79  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.57/0.79  thf(zf_stmt_4, axiom,
% 0.57/0.79    (![B:$i,A:$i]:
% 0.57/0.79     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.57/0.79       ( zip_tseitin_0 @ B @ A ) ))).
% 0.57/0.79  thf(zf_stmt_5, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.79       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.57/0.79         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.57/0.79           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.57/0.79             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.57/0.79  thf('11', plain,
% 0.57/0.79      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.57/0.79         (~ (zip_tseitin_0 @ X17 @ X18)
% 0.57/0.79          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 0.57/0.79          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.57/0.79  thf('12', plain,
% 0.57/0.79      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.57/0.79      inference('sup-', [status(thm)], ['10', '11'])).
% 0.57/0.79  thf('13', plain,
% 0.57/0.79      (![X12 : $i, X13 : $i]:
% 0.57/0.79         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.57/0.79  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.57/0.79  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.57/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.57/0.79  thf('15', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.57/0.79      inference('sup+', [status(thm)], ['13', '14'])).
% 0.57/0.79  thf('16', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(cc2_partfun1, axiom,
% 0.57/0.79    (![A:$i,B:$i]:
% 0.57/0.79     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.57/0.79       ( ![C:$i]:
% 0.57/0.79         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.79           ( ~( v1_partfun1 @ C @ A ) ) ) ) ))).
% 0.57/0.79  thf('17', plain,
% 0.57/0.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.57/0.79         ((v1_xboole_0 @ X9)
% 0.57/0.79          | ~ (v1_xboole_0 @ X10)
% 0.57/0.79          | ~ (v1_partfun1 @ X11 @ X9)
% 0.57/0.79          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.57/0.79      inference('cnf', [status(esa)], [cc2_partfun1])).
% 0.57/0.79  thf('18', plain,
% 0.57/0.79      ((~ (v1_partfun1 @ sk_E @ sk_A)
% 0.57/0.79        | ~ (v1_xboole_0 @ sk_C)
% 0.57/0.79        | (v1_xboole_0 @ sk_A))),
% 0.57/0.79      inference('sup-', [status(thm)], ['16', '17'])).
% 0.57/0.79  thf('19', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('20', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_A))),
% 0.57/0.79      inference('demod', [status(thm)], ['18', '19'])).
% 0.57/0.79  thf('21', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('22', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.57/0.79      inference('clc', [status(thm)], ['20', '21'])).
% 0.57/0.79  thf('23', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 0.57/0.79      inference('sup-', [status(thm)], ['15', '22'])).
% 0.57/0.79  thf('24', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_A)),
% 0.57/0.79      inference('demod', [status(thm)], ['12', '23'])).
% 0.57/0.79  thf('25', plain, (((sk_A) = (k1_relset_1 @ sk_A @ sk_C @ sk_E))),
% 0.57/0.79      inference('demod', [status(thm)], ['9', '24'])).
% 0.57/0.79  thf('26', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(t185_funct_2, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.57/0.79       ( ![D:$i]:
% 0.57/0.79         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.57/0.79             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.57/0.79           ( ![E:$i]:
% 0.57/0.79             ( ( ( v1_funct_1 @ E ) & 
% 0.57/0.79                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.57/0.79               ( ![F:$i]:
% 0.57/0.79                 ( ( m1_subset_1 @ F @ B ) =>
% 0.57/0.79                   ( ( r1_tarski @
% 0.57/0.79                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.57/0.79                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.57/0.79                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.57/0.79                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.57/0.79                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.57/0.79  thf('27', plain,
% 0.57/0.79      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.57/0.79         (~ (v1_funct_1 @ X29)
% 0.57/0.79          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.57/0.79          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.57/0.79          | ~ (m1_subset_1 @ X32 @ X30)
% 0.57/0.79          | ((k1_funct_1 @ (k8_funct_2 @ X30 @ X31 @ X34 @ X29 @ X33) @ X32)
% 0.57/0.79              = (k1_funct_1 @ X33 @ (k1_funct_1 @ X29 @ X32)))
% 0.57/0.79          | ((X30) = (k1_xboole_0))
% 0.57/0.79          | ~ (r1_tarski @ (k2_relset_1 @ X30 @ X31 @ X29) @ 
% 0.57/0.79               (k1_relset_1 @ X31 @ X34 @ X33))
% 0.57/0.79          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X34)))
% 0.57/0.79          | ~ (v1_funct_1 @ X33)
% 0.57/0.79          | (v1_xboole_0 @ X31))),
% 0.57/0.79      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.57/0.79  thf('28', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.79         ((v1_xboole_0 @ sk_A)
% 0.57/0.79          | ~ (v1_funct_1 @ X0)
% 0.57/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.57/0.79          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_A @ sk_D) @ 
% 0.57/0.79               (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.57/0.79          | ((sk_B) = (k1_xboole_0))
% 0.57/0.79          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.57/0.79              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.57/0.79          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.57/0.79          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.57/0.79          | ~ (v1_funct_1 @ sk_D))),
% 0.57/0.79      inference('sup-', [status(thm)], ['26', '27'])).
% 0.57/0.79  thf('29', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('31', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.79         ((v1_xboole_0 @ sk_A)
% 0.57/0.79          | ~ (v1_funct_1 @ X0)
% 0.57/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.57/0.79          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_A @ sk_D) @ 
% 0.57/0.79               (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.57/0.79          | ((sk_B) = (k1_xboole_0))
% 0.57/0.79          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.57/0.79              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.57/0.79          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.57/0.79      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.57/0.79  thf('32', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_A @ sk_D) @ sk_A)
% 0.57/0.79          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.57/0.79          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.57/0.79              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.57/0.79          | ((sk_B) = (k1_xboole_0))
% 0.57/0.79          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.57/0.79          | ~ (v1_funct_1 @ sk_E)
% 0.57/0.79          | (v1_xboole_0 @ sk_A))),
% 0.57/0.79      inference('sup-', [status(thm)], ['25', '31'])).
% 0.57/0.79  thf('33', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(dt_k2_relset_1, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.79       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.57/0.79  thf('34', plain,
% 0.57/0.79      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.57/0.79         ((m1_subset_1 @ (k2_relset_1 @ X3 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.57/0.79          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.57/0.79      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.57/0.79  thf('35', plain,
% 0.57/0.79      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.79      inference('sup-', [status(thm)], ['33', '34'])).
% 0.57/0.79  thf(t3_subset, axiom,
% 0.57/0.79    (![A:$i,B:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.57/0.79  thf('36', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.57/0.79      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.79  thf('37', plain, ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_A @ sk_D) @ sk_A)),
% 0.57/0.79      inference('sup-', [status(thm)], ['35', '36'])).
% 0.57/0.79  thf('38', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('39', plain, ((v1_funct_1 @ sk_E)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('40', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.57/0.79          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.57/0.79              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.57/0.79          | ((sk_B) = (k1_xboole_0))
% 0.57/0.79          | (v1_xboole_0 @ sk_A))),
% 0.57/0.79      inference('demod', [status(thm)], ['32', '37', '38', '39'])).
% 0.57/0.79  thf('41', plain,
% 0.57/0.79      (((v1_xboole_0 @ sk_A)
% 0.57/0.79        | ((sk_B) = (k1_xboole_0))
% 0.57/0.79        | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.57/0.79            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.57/0.79      inference('sup-', [status(thm)], ['1', '40'])).
% 0.57/0.79  thf('42', plain,
% 0.57/0.79      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.57/0.79         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.57/0.79         != (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('43', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('44', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(redefinition_k3_funct_2, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.79     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.57/0.79         ( v1_funct_2 @ C @ A @ B ) & 
% 0.57/0.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.57/0.79         ( m1_subset_1 @ D @ A ) ) =>
% 0.57/0.79       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.57/0.79  thf('45', plain,
% 0.57/0.79      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.57/0.79         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.57/0.79          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.57/0.79          | ~ (v1_funct_1 @ X25)
% 0.57/0.79          | (v1_xboole_0 @ X26)
% 0.57/0.79          | ~ (m1_subset_1 @ X28 @ X26)
% 0.57/0.79          | ((k3_funct_2 @ X26 @ X27 @ X25 @ X28) = (k1_funct_1 @ X25 @ X28)))),
% 0.57/0.79      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.57/0.79  thf('46', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.57/0.79          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.57/0.79          | (v1_xboole_0 @ sk_B)
% 0.57/0.79          | ~ (v1_funct_1 @ sk_D)
% 0.57/0.79          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.57/0.79      inference('sup-', [status(thm)], ['44', '45'])).
% 0.57/0.79  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('48', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('49', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.57/0.79          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.57/0.79          | (v1_xboole_0 @ sk_B))),
% 0.57/0.79      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.57/0.79  thf('50', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('51', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.57/0.79          | ((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 0.57/0.79      inference('clc', [status(thm)], ['49', '50'])).
% 0.57/0.79  thf('52', plain,
% 0.57/0.79      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.57/0.79      inference('sup-', [status(thm)], ['43', '51'])).
% 0.57/0.79  thf('53', plain,
% 0.57/0.79      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.57/0.79         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.57/0.79         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.57/0.79      inference('demod', [status(thm)], ['42', '52'])).
% 0.57/0.79  thf('54', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('55', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('56', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(dt_k8_funct_2, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.57/0.79     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.57/0.79         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.57/0.79         ( v1_funct_1 @ E ) & 
% 0.57/0.79         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.57/0.79       ( ( v1_funct_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) ) & 
% 0.57/0.79         ( v1_funct_2 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ A @ C ) & 
% 0.57/0.79         ( m1_subset_1 @
% 0.57/0.79           ( k8_funct_2 @ A @ B @ C @ D @ E ) @ 
% 0.57/0.79           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.57/0.79  thf('57', plain,
% 0.57/0.79      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.57/0.79         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.57/0.79          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.57/0.79          | ~ (v1_funct_1 @ X20)
% 0.57/0.79          | ~ (v1_funct_1 @ X23)
% 0.57/0.79          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 0.57/0.79          | (m1_subset_1 @ (k8_funct_2 @ X21 @ X22 @ X24 @ X20 @ X23) @ 
% 0.57/0.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X24))))),
% 0.57/0.79      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.57/0.79  thf('58', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.57/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.57/0.79          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.57/0.79          | ~ (v1_funct_1 @ X1)
% 0.57/0.79          | ~ (v1_funct_1 @ sk_D)
% 0.57/0.79          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.57/0.79      inference('sup-', [status(thm)], ['56', '57'])).
% 0.57/0.79  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('61', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.57/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.57/0.79          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.57/0.79          | ~ (v1_funct_1 @ X1))),
% 0.57/0.79      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.57/0.79  thf('62', plain,
% 0.57/0.79      ((~ (v1_funct_1 @ sk_E)
% 0.57/0.79        | (m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.57/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.57/0.79      inference('sup-', [status(thm)], ['55', '61'])).
% 0.57/0.79  thf('63', plain, ((v1_funct_1 @ sk_E)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('64', plain,
% 0.57/0.79      ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.57/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.57/0.79      inference('demod', [status(thm)], ['62', '63'])).
% 0.57/0.79  thf('65', plain,
% 0.57/0.79      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.57/0.79         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.57/0.79          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.57/0.79          | ~ (v1_funct_1 @ X25)
% 0.57/0.79          | (v1_xboole_0 @ X26)
% 0.57/0.79          | ~ (m1_subset_1 @ X28 @ X26)
% 0.57/0.79          | ((k3_funct_2 @ X26 @ X27 @ X25 @ X28) = (k1_funct_1 @ X25 @ X28)))),
% 0.57/0.79      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.57/0.79  thf('66', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.57/0.79            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.57/0.79            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.57/0.79               X0))
% 0.57/0.79          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.57/0.79          | (v1_xboole_0 @ sk_B)
% 0.57/0.79          | ~ (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))
% 0.57/0.79          | ~ (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.57/0.79               sk_B @ sk_C))),
% 0.57/0.79      inference('sup-', [status(thm)], ['64', '65'])).
% 0.57/0.79  thf('67', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('68', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('69', plain,
% 0.57/0.79      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.57/0.79         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.57/0.79          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.57/0.79          | ~ (v1_funct_1 @ X20)
% 0.57/0.79          | ~ (v1_funct_1 @ X23)
% 0.57/0.79          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 0.57/0.79          | (v1_funct_1 @ (k8_funct_2 @ X21 @ X22 @ X24 @ X20 @ X23)))),
% 0.57/0.79      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.57/0.79  thf('70', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 0.57/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.57/0.79          | ~ (v1_funct_1 @ X0)
% 0.57/0.79          | ~ (v1_funct_1 @ sk_D)
% 0.57/0.79          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.57/0.79      inference('sup-', [status(thm)], ['68', '69'])).
% 0.57/0.79  thf('71', plain, ((v1_funct_1 @ sk_D)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('72', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('73', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 0.57/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.57/0.79          | ~ (v1_funct_1 @ X0))),
% 0.57/0.79      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.57/0.79  thf('74', plain,
% 0.57/0.79      ((~ (v1_funct_1 @ sk_E)
% 0.57/0.79        | (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['67', '73'])).
% 0.57/0.79  thf('75', plain, ((v1_funct_1 @ sk_E)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('76', plain,
% 0.57/0.79      ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))),
% 0.57/0.79      inference('demod', [status(thm)], ['74', '75'])).
% 0.57/0.79  thf('77', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('78', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('79', plain,
% 0.57/0.79      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.57/0.79         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.57/0.79          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.57/0.79          | ~ (v1_funct_1 @ X20)
% 0.57/0.79          | ~ (v1_funct_1 @ X23)
% 0.57/0.79          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 0.57/0.79          | (v1_funct_2 @ (k8_funct_2 @ X21 @ X22 @ X24 @ X20 @ X23) @ X21 @ 
% 0.57/0.79             X24))),
% 0.57/0.79      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.57/0.79  thf('80', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 0.57/0.79          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.57/0.79          | ~ (v1_funct_1 @ X1)
% 0.57/0.79          | ~ (v1_funct_1 @ sk_D)
% 0.57/0.79          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.57/0.79      inference('sup-', [status(thm)], ['78', '79'])).
% 0.57/0.79  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('82', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('83', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 0.57/0.79          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.57/0.79          | ~ (v1_funct_1 @ X1))),
% 0.57/0.79      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.57/0.79  thf('84', plain,
% 0.57/0.79      ((~ (v1_funct_1 @ sk_E)
% 0.57/0.79        | (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.57/0.79           sk_B @ sk_C))),
% 0.57/0.79      inference('sup-', [status(thm)], ['77', '83'])).
% 0.57/0.79  thf('85', plain, ((v1_funct_1 @ sk_E)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('86', plain,
% 0.57/0.79      ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_B @ 
% 0.57/0.79        sk_C)),
% 0.57/0.79      inference('demod', [status(thm)], ['84', '85'])).
% 0.57/0.79  thf('87', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.57/0.79            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.57/0.79            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.57/0.79               X0))
% 0.57/0.79          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.57/0.79          | (v1_xboole_0 @ sk_B))),
% 0.57/0.79      inference('demod', [status(thm)], ['66', '76', '86'])).
% 0.57/0.79  thf('88', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('89', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.57/0.79          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.57/0.79              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.57/0.79              = (k1_funct_1 @ 
% 0.57/0.79                 (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)))),
% 0.57/0.79      inference('clc', [status(thm)], ['87', '88'])).
% 0.57/0.79  thf('90', plain,
% 0.57/0.79      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.57/0.79         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.57/0.79         = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F))),
% 0.57/0.79      inference('sup-', [status(thm)], ['54', '89'])).
% 0.57/0.79  thf('91', plain,
% 0.57/0.79      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.57/0.79         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.57/0.79      inference('demod', [status(thm)], ['53', '90'])).
% 0.57/0.79  thf('92', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.57/0.79      inference('simplify_reflect-', [status(thm)], ['41', '91'])).
% 0.57/0.79  thf('93', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('94', plain, (((sk_B) = (k1_xboole_0))),
% 0.57/0.79      inference('clc', [status(thm)], ['92', '93'])).
% 0.57/0.79  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.57/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.57/0.79  thf('96', plain, ($false),
% 0.57/0.79      inference('demod', [status(thm)], ['0', '94', '95'])).
% 0.57/0.79  
% 0.57/0.79  % SZS output end Refutation
% 0.57/0.79  
% 0.57/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
