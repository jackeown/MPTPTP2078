%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kCXiFYnbEK

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:00 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 306 expanded)
%              Number of leaves         :   44 ( 109 expanded)
%              Depth                    :   14
%              Number of atoms          : 1078 (6069 expanded)
%              Number of equality atoms :   62 ( 352 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t28_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C )
              & ( v2_funct_1 @ E ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ B @ D )
                = B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C )
                & ( v2_funct_1 @ E ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ B @ D )
                  = B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('20',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k4_relset_1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('25',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('29',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['26','35'])).

thf('37',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['25','36'])).

thf(t51_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
                = ( k2_relat_1 @ A ) )
              & ( v2_funct_1 @ A ) )
           => ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X11 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) )
       != ( k2_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t51_funct_1])).

thf('39',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( r1_tarski @ ( k1_relat_1 @ sk_E ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
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

thf('48',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('50',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('51',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('52',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('53',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('58',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('59',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['49','56','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('63',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','44','45','46','60','61','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['25','36'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('65',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('66',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('71',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['42','43'])).

thf('75',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['25','36'])).

thf('77',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['42','43'])).

thf('78',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['68','75','76','77','78'])).

thf('80',plain,
    ( ( sk_C != sk_C )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['63','79'])).

thf('81',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','81'])).

thf('83',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('86',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['82','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kCXiFYnbEK
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:36:52 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.74/0.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/0.94  % Solved by: fo/fo7.sh
% 0.74/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.94  % done 503 iterations in 0.490s
% 0.74/0.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/0.94  % SZS output start Refutation
% 0.74/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.74/0.94  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.74/0.94  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.74/0.94  thf(sk_D_type, type, sk_D: $i).
% 0.74/0.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.94  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.74/0.94  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.74/0.94  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.74/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.94  thf(sk_E_type, type, sk_E: $i).
% 0.74/0.94  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.74/0.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/0.94  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.74/0.94  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.74/0.94  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.74/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.94  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.74/0.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.74/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.94  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.74/0.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.74/0.94  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.74/0.94  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.74/0.94  thf(sk_C_type, type, sk_C: $i).
% 0.74/0.94  thf(t28_funct_2, conjecture,
% 0.74/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.94     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.74/0.94         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.74/0.94       ( ![E:$i]:
% 0.74/0.94         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.74/0.94             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.74/0.94           ( ( ( ( k2_relset_1 @
% 0.74/0.94                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 0.74/0.94                 ( C ) ) & 
% 0.74/0.94               ( v2_funct_1 @ E ) ) =>
% 0.74/0.94             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.74/0.94               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 0.74/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.94    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.94        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.74/0.94            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.74/0.94          ( ![E:$i]:
% 0.74/0.94            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.74/0.94                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.74/0.94              ( ( ( ( k2_relset_1 @
% 0.74/0.94                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 0.74/0.94                    ( C ) ) & 
% 0.74/0.94                  ( v2_funct_1 @ E ) ) =>
% 0.74/0.94                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.74/0.94                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 0.74/0.94    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 0.74/0.94  thf('0', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(cc2_relset_1, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.94       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.74/0.94  thf('1', plain,
% 0.74/0.94      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.74/0.94         ((v5_relat_1 @ X13 @ X15)
% 0.74/0.94          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.74/0.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.74/0.94  thf('2', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.74/0.94      inference('sup-', [status(thm)], ['0', '1'])).
% 0.74/0.94  thf(d19_relat_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( v1_relat_1 @ B ) =>
% 0.74/0.94       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.74/0.94  thf('3', plain,
% 0.74/0.94      (![X5 : $i, X6 : $i]:
% 0.74/0.94         (~ (v5_relat_1 @ X5 @ X6)
% 0.74/0.94          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.74/0.94          | ~ (v1_relat_1 @ X5))),
% 0.74/0.94      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.74/0.94  thf('4', plain,
% 0.74/0.94      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.74/0.94      inference('sup-', [status(thm)], ['2', '3'])).
% 0.74/0.94  thf('5', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(cc2_relat_1, axiom,
% 0.74/0.94    (![A:$i]:
% 0.74/0.94     ( ( v1_relat_1 @ A ) =>
% 0.74/0.94       ( ![B:$i]:
% 0.74/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.74/0.94  thf('6', plain,
% 0.74/0.94      (![X3 : $i, X4 : $i]:
% 0.74/0.94         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.74/0.94          | (v1_relat_1 @ X3)
% 0.74/0.94          | ~ (v1_relat_1 @ X4))),
% 0.74/0.94      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.74/0.94  thf('7', plain,
% 0.74/0.94      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.74/0.94      inference('sup-', [status(thm)], ['5', '6'])).
% 0.74/0.94  thf(fc6_relat_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.74/0.94  thf('8', plain,
% 0.74/0.94      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.74/0.94      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.74/0.94  thf('9', plain, ((v1_relat_1 @ sk_D)),
% 0.74/0.94      inference('demod', [status(thm)], ['7', '8'])).
% 0.74/0.94  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.74/0.94      inference('demod', [status(thm)], ['4', '9'])).
% 0.74/0.94  thf(d10_xboole_0, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.74/0.94  thf('11', plain,
% 0.74/0.94      (![X0 : $i, X2 : $i]:
% 0.74/0.94         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.74/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/0.94  thf('12', plain,
% 0.74/0.94      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 0.74/0.94        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['10', '11'])).
% 0.74/0.94  thf('13', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('14', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(dt_k4_relset_1, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.74/0.94     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.74/0.94         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.74/0.94       ( m1_subset_1 @
% 0.74/0.94         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.74/0.94         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.74/0.94  thf('15', plain,
% 0.74/0.94      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.74/0.94         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.74/0.94          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.74/0.94          | (m1_subset_1 @ (k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19) @ 
% 0.74/0.94             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X21))))),
% 0.74/0.94      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.74/0.94  thf('16', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.94         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 0.74/0.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.74/0.94          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.74/0.94      inference('sup-', [status(thm)], ['14', '15'])).
% 0.74/0.94  thf('17', plain,
% 0.74/0.94      ((m1_subset_1 @ 
% 0.74/0.94        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.74/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['13', '16'])).
% 0.74/0.94  thf('18', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('19', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(redefinition_k4_relset_1, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.74/0.94     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.74/0.94         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.74/0.94       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.74/0.94  thf('20', plain,
% 0.74/0.94      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.74/0.94         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.74/0.94          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.74/0.94          | ((k4_relset_1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 0.74/0.94              = (k5_relat_1 @ X28 @ X31)))),
% 0.74/0.94      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.74/0.94  thf('21', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.94         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.74/0.94            = (k5_relat_1 @ sk_D @ X0))
% 0.74/0.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.74/0.94      inference('sup-', [status(thm)], ['19', '20'])).
% 0.74/0.94  thf('22', plain,
% 0.74/0.94      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.74/0.94         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.74/0.94      inference('sup-', [status(thm)], ['18', '21'])).
% 0.74/0.94  thf('23', plain,
% 0.74/0.94      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 0.74/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.74/0.94      inference('demod', [status(thm)], ['17', '22'])).
% 0.74/0.94  thf(redefinition_k2_relset_1, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.94       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.74/0.94  thf('24', plain,
% 0.74/0.94      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.74/0.94         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.74/0.94          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.74/0.94      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.74/0.94  thf('25', plain,
% 0.74/0.94      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 0.74/0.94         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['23', '24'])).
% 0.74/0.94  thf('26', plain,
% 0.74/0.94      (((k2_relset_1 @ sk_A @ sk_C @ 
% 0.74/0.94         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('27', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('28', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(redefinition_k1_partfun1, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.74/0.94     ( ( ( v1_funct_1 @ E ) & 
% 0.74/0.94         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.74/0.94         ( v1_funct_1 @ F ) & 
% 0.74/0.94         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.74/0.94       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.74/0.94  thf('29', plain,
% 0.74/0.94      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.74/0.94         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.74/0.94          | ~ (v1_funct_1 @ X42)
% 0.74/0.94          | ~ (v1_funct_1 @ X45)
% 0.74/0.94          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 0.74/0.94          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 0.74/0.94              = (k5_relat_1 @ X42 @ X45)))),
% 0.74/0.94      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.74/0.94  thf('30', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.94         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.74/0.94            = (k5_relat_1 @ sk_D @ X0))
% 0.74/0.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.74/0.94          | ~ (v1_funct_1 @ X0)
% 0.74/0.94          | ~ (v1_funct_1 @ sk_D))),
% 0.74/0.94      inference('sup-', [status(thm)], ['28', '29'])).
% 0.74/0.94  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('32', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.94         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.74/0.94            = (k5_relat_1 @ sk_D @ X0))
% 0.74/0.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.74/0.94          | ~ (v1_funct_1 @ X0))),
% 0.74/0.94      inference('demod', [status(thm)], ['30', '31'])).
% 0.74/0.94  thf('33', plain,
% 0.74/0.94      ((~ (v1_funct_1 @ sk_E)
% 0.74/0.94        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.74/0.94            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['27', '32'])).
% 0.74/0.94  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('35', plain,
% 0.74/0.94      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.74/0.94         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.74/0.94      inference('demod', [status(thm)], ['33', '34'])).
% 0.74/0.94  thf('36', plain,
% 0.74/0.94      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 0.74/0.94      inference('demod', [status(thm)], ['26', '35'])).
% 0.74/0.94  thf('37', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 0.74/0.94      inference('sup+', [status(thm)], ['25', '36'])).
% 0.74/0.94  thf(t51_funct_1, axiom,
% 0.74/0.94    (![A:$i]:
% 0.74/0.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.74/0.94       ( ![B:$i]:
% 0.74/0.94         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.74/0.94           ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) & 
% 0.74/0.94               ( v2_funct_1 @ A ) ) =>
% 0.74/0.94             ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.74/0.94  thf('38', plain,
% 0.74/0.94      (![X11 : $i, X12 : $i]:
% 0.74/0.94         (~ (v1_relat_1 @ X11)
% 0.74/0.94          | ~ (v1_funct_1 @ X11)
% 0.74/0.94          | (r1_tarski @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X11))
% 0.74/0.94          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ X12)) != (k2_relat_1 @ X12))
% 0.74/0.94          | ~ (v2_funct_1 @ X12)
% 0.74/0.94          | ~ (v1_funct_1 @ X12)
% 0.74/0.94          | ~ (v1_relat_1 @ X12))),
% 0.74/0.94      inference('cnf', [status(esa)], [t51_funct_1])).
% 0.74/0.94  thf('39', plain,
% 0.74/0.94      ((((sk_C) != (k2_relat_1 @ sk_E))
% 0.74/0.94        | ~ (v1_relat_1 @ sk_E)
% 0.74/0.94        | ~ (v1_funct_1 @ sk_E)
% 0.74/0.94        | ~ (v2_funct_1 @ sk_E)
% 0.74/0.94        | (r1_tarski @ (k1_relat_1 @ sk_E) @ (k2_relat_1 @ sk_D))
% 0.74/0.94        | ~ (v1_funct_1 @ sk_D)
% 0.74/0.94        | ~ (v1_relat_1 @ sk_D))),
% 0.74/0.94      inference('sup-', [status(thm)], ['37', '38'])).
% 0.74/0.94  thf('40', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('41', plain,
% 0.74/0.94      (![X3 : $i, X4 : $i]:
% 0.74/0.94         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.74/0.94          | (v1_relat_1 @ X3)
% 0.74/0.94          | ~ (v1_relat_1 @ X4))),
% 0.74/0.94      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.74/0.94  thf('42', plain,
% 0.74/0.94      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 0.74/0.94      inference('sup-', [status(thm)], ['40', '41'])).
% 0.74/0.94  thf('43', plain,
% 0.74/0.94      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.74/0.94      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.74/0.94  thf('44', plain, ((v1_relat_1 @ sk_E)),
% 0.74/0.94      inference('demod', [status(thm)], ['42', '43'])).
% 0.74/0.94  thf('45', plain, ((v1_funct_1 @ sk_E)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('46', plain, ((v2_funct_1 @ sk_E)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('47', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(d1_funct_2, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.94       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.74/0.94           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.74/0.94             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.74/0.94         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.74/0.94           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.74/0.94             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.74/0.94  thf(zf_stmt_1, axiom,
% 0.74/0.94    (![C:$i,B:$i,A:$i]:
% 0.74/0.94     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.74/0.94       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.74/0.94  thf('48', plain,
% 0.74/0.94      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.74/0.94         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.74/0.94          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 0.74/0.94          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.74/0.94  thf('49', plain,
% 0.74/0.94      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 0.74/0.94        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['47', '48'])).
% 0.74/0.94  thf(zf_stmt_2, axiom,
% 0.74/0.94    (![B:$i,A:$i]:
% 0.74/0.94     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.74/0.94       ( zip_tseitin_0 @ B @ A ) ))).
% 0.74/0.94  thf('50', plain,
% 0.74/0.94      (![X34 : $i, X35 : $i]:
% 0.74/0.94         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.74/0.94  thf('51', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.74/0.94  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.74/0.94  thf(zf_stmt_5, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.94       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.74/0.94         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.74/0.94           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.74/0.94             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.74/0.94  thf('52', plain,
% 0.74/0.94      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.74/0.94         (~ (zip_tseitin_0 @ X39 @ X40)
% 0.74/0.94          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 0.74/0.94          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.74/0.94  thf('53', plain,
% 0.74/0.94      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.74/0.94      inference('sup-', [status(thm)], ['51', '52'])).
% 0.74/0.94  thf('54', plain,
% 0.74/0.94      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 0.74/0.94      inference('sup-', [status(thm)], ['50', '53'])).
% 0.74/0.94  thf('55', plain, (((sk_C) != (k1_xboole_0))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('56', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 0.74/0.94      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.74/0.94  thf('57', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(redefinition_k1_relset_1, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.94       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.74/0.94  thf('58', plain,
% 0.74/0.94      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.74/0.94         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.74/0.94          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.74/0.94      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.74/0.94  thf('59', plain,
% 0.74/0.94      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.74/0.94      inference('sup-', [status(thm)], ['57', '58'])).
% 0.74/0.94  thf('60', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 0.74/0.94      inference('demod', [status(thm)], ['49', '56', '59'])).
% 0.74/0.94  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('62', plain, ((v1_relat_1 @ sk_D)),
% 0.74/0.94      inference('demod', [status(thm)], ['7', '8'])).
% 0.74/0.94  thf('63', plain,
% 0.74/0.94      ((((sk_C) != (k2_relat_1 @ sk_E))
% 0.74/0.94        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 0.74/0.94      inference('demod', [status(thm)],
% 0.74/0.94                ['39', '44', '45', '46', '60', '61', '62'])).
% 0.74/0.94  thf('64', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 0.74/0.94      inference('sup+', [status(thm)], ['25', '36'])).
% 0.74/0.94  thf(t45_relat_1, axiom,
% 0.74/0.94    (![A:$i]:
% 0.74/0.94     ( ( v1_relat_1 @ A ) =>
% 0.74/0.94       ( ![B:$i]:
% 0.74/0.94         ( ( v1_relat_1 @ B ) =>
% 0.74/0.94           ( r1_tarski @
% 0.74/0.94             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.74/0.94  thf('65', plain,
% 0.74/0.94      (![X9 : $i, X10 : $i]:
% 0.74/0.94         (~ (v1_relat_1 @ X9)
% 0.74/0.94          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X10 @ X9)) @ 
% 0.74/0.94             (k2_relat_1 @ X9))
% 0.74/0.94          | ~ (v1_relat_1 @ X10))),
% 0.74/0.94      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.74/0.94  thf('66', plain,
% 0.74/0.94      (![X0 : $i, X2 : $i]:
% 0.74/0.94         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.74/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/0.94  thf('67', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         (~ (v1_relat_1 @ X1)
% 0.74/0.94          | ~ (v1_relat_1 @ X0)
% 0.74/0.94          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.74/0.94               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.74/0.94          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.74/0.94      inference('sup-', [status(thm)], ['65', '66'])).
% 0.74/0.94  thf('68', plain,
% 0.74/0.94      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)
% 0.74/0.94        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 0.74/0.94        | ~ (v1_relat_1 @ sk_E)
% 0.74/0.94        | ~ (v1_relat_1 @ sk_D))),
% 0.74/0.94      inference('sup-', [status(thm)], ['64', '67'])).
% 0.74/0.94  thf('69', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('70', plain,
% 0.74/0.94      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.74/0.94         ((v5_relat_1 @ X13 @ X15)
% 0.74/0.94          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.74/0.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.74/0.94  thf('71', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 0.74/0.94      inference('sup-', [status(thm)], ['69', '70'])).
% 0.74/0.94  thf('72', plain,
% 0.74/0.94      (![X5 : $i, X6 : $i]:
% 0.74/0.94         (~ (v5_relat_1 @ X5 @ X6)
% 0.74/0.94          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.74/0.94          | ~ (v1_relat_1 @ X5))),
% 0.74/0.94      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.74/0.94  thf('73', plain,
% 0.74/0.94      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 0.74/0.94      inference('sup-', [status(thm)], ['71', '72'])).
% 0.74/0.94  thf('74', plain, ((v1_relat_1 @ sk_E)),
% 0.74/0.94      inference('demod', [status(thm)], ['42', '43'])).
% 0.74/0.94  thf('75', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 0.74/0.94      inference('demod', [status(thm)], ['73', '74'])).
% 0.74/0.94  thf('76', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 0.74/0.94      inference('sup+', [status(thm)], ['25', '36'])).
% 0.74/0.94  thf('77', plain, ((v1_relat_1 @ sk_E)),
% 0.74/0.94      inference('demod', [status(thm)], ['42', '43'])).
% 0.74/0.94  thf('78', plain, ((v1_relat_1 @ sk_D)),
% 0.74/0.94      inference('demod', [status(thm)], ['7', '8'])).
% 0.74/0.94  thf('79', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 0.74/0.94      inference('demod', [status(thm)], ['68', '75', '76', '77', '78'])).
% 0.74/0.94  thf('80', plain,
% 0.74/0.94      ((((sk_C) != (sk_C)) | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 0.74/0.94      inference('demod', [status(thm)], ['63', '79'])).
% 0.74/0.94  thf('81', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))),
% 0.74/0.94      inference('simplify', [status(thm)], ['80'])).
% 0.74/0.94  thf('82', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 0.74/0.94      inference('demod', [status(thm)], ['12', '81'])).
% 0.74/0.94  thf('83', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('84', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('85', plain,
% 0.74/0.94      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.74/0.94         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.74/0.94          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.74/0.94      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.74/0.94  thf('86', plain,
% 0.74/0.94      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.74/0.94      inference('sup-', [status(thm)], ['84', '85'])).
% 0.74/0.94  thf('87', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 0.74/0.94      inference('demod', [status(thm)], ['83', '86'])).
% 0.74/0.94  thf('88', plain, ($false),
% 0.74/0.94      inference('simplify_reflect-', [status(thm)], ['82', '87'])).
% 0.74/0.94  
% 0.74/0.94  % SZS output end Refutation
% 0.74/0.94  
% 0.75/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
