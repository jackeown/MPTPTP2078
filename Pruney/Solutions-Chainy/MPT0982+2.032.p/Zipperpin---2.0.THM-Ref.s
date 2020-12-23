%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SOKpI12Amc

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:59 EST 2020

% Result     : Theorem 18.83s
% Output     : Refutation 18.83s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 476 expanded)
%              Number of leaves         :   44 ( 160 expanded)
%              Depth                    :   19
%              Number of atoms          : 1299 (9751 expanded)
%              Number of equality atoms :   66 ( 565 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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

thf('13',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( ( k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43 )
        = ( k5_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['13','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X15 @ X16 @ X18 @ X19 @ X14 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('33',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['30','35','36'])).

thf('38',plain,
    ( sk_C
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup+',[status(thm)],['23','37'])).

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

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X9 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) )
       != ( k2_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t51_funct_1])).

thf('40',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( r1_tarski @ ( k1_relat_1 @ sk_E ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('45',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
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

thf('49',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('50',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('51',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('59',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('60',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['50','57','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('64',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['40','45','46','47','61','62','63'])).

thf('65',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['50','57','60'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X46: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X46 ) @ ( k2_relat_1 @ X46 ) ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_E ) ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['43','44'])).

thf('69',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('72',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('74',plain,(
    v5_relat_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E ) @ ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E ) ) @ ( k2_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('78',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_E ) ) )
    | ( v1_relat_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('81',plain,(
    v1_relat_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E ) ) @ ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['76','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('85',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) @ ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('88',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( sk_C
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup+',[status(thm)],['23','37'])).

thf('90',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('92',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['43','44'])).

thf('96',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( sk_C
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup+',[status(thm)],['23','37'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['88','89','96','97'])).

thf('99',plain,
    ( ( sk_C != sk_C )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','98'])).

thf('100',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','100'])).

thf('102',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('105',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['101','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SOKpI12Amc
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 18.83/19.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 18.83/19.07  % Solved by: fo/fo7.sh
% 18.83/19.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.83/19.07  % done 4705 iterations in 18.615s
% 18.83/19.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 18.83/19.07  % SZS output start Refutation
% 18.83/19.07  thf(sk_E_type, type, sk_E: $i).
% 18.83/19.07  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 18.83/19.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 18.83/19.07  thf(sk_C_type, type, sk_C: $i).
% 18.83/19.07  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 18.83/19.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 18.83/19.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 18.83/19.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 18.83/19.07  thf(sk_A_type, type, sk_A: $i).
% 18.83/19.07  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 18.83/19.07  thf(sk_B_type, type, sk_B: $i).
% 18.83/19.07  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 18.83/19.07  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 18.83/19.07  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 18.83/19.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 18.83/19.07  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 18.83/19.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 18.83/19.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 18.83/19.07  thf(sk_D_type, type, sk_D: $i).
% 18.83/19.07  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 18.83/19.07  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 18.83/19.07  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 18.83/19.07  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 18.83/19.07  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 18.83/19.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 18.83/19.07  thf(t28_funct_2, conjecture,
% 18.83/19.07    (![A:$i,B:$i,C:$i,D:$i]:
% 18.83/19.07     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 18.83/19.07         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.83/19.07       ( ![E:$i]:
% 18.83/19.07         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 18.83/19.07             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 18.83/19.07           ( ( ( ( k2_relset_1 @
% 18.83/19.07                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 18.83/19.07                 ( C ) ) & 
% 18.83/19.07               ( v2_funct_1 @ E ) ) =>
% 18.83/19.07             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 18.83/19.07               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 18.83/19.07  thf(zf_stmt_0, negated_conjecture,
% 18.83/19.07    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 18.83/19.07        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 18.83/19.07            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.83/19.07          ( ![E:$i]:
% 18.83/19.07            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 18.83/19.07                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 18.83/19.07              ( ( ( ( k2_relset_1 @
% 18.83/19.07                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 18.83/19.07                    ( C ) ) & 
% 18.83/19.07                  ( v2_funct_1 @ E ) ) =>
% 18.83/19.07                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 18.83/19.07                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 18.83/19.07    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 18.83/19.07  thf('0', plain,
% 18.83/19.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf(cc2_relset_1, axiom,
% 18.83/19.07    (![A:$i,B:$i,C:$i]:
% 18.83/19.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.83/19.07       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 18.83/19.07  thf('1', plain,
% 18.83/19.07      (![X11 : $i, X12 : $i, X13 : $i]:
% 18.83/19.07         ((v5_relat_1 @ X11 @ X13)
% 18.83/19.07          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 18.83/19.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 18.83/19.07  thf('2', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 18.83/19.07      inference('sup-', [status(thm)], ['0', '1'])).
% 18.83/19.07  thf(d19_relat_1, axiom,
% 18.83/19.07    (![A:$i,B:$i]:
% 18.83/19.07     ( ( v1_relat_1 @ B ) =>
% 18.83/19.07       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 18.83/19.07  thf('3', plain,
% 18.83/19.07      (![X5 : $i, X6 : $i]:
% 18.83/19.07         (~ (v5_relat_1 @ X5 @ X6)
% 18.83/19.07          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 18.83/19.07          | ~ (v1_relat_1 @ X5))),
% 18.83/19.07      inference('cnf', [status(esa)], [d19_relat_1])).
% 18.83/19.07  thf('4', plain,
% 18.83/19.07      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 18.83/19.07      inference('sup-', [status(thm)], ['2', '3'])).
% 18.83/19.07  thf('5', plain,
% 18.83/19.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf(cc2_relat_1, axiom,
% 18.83/19.07    (![A:$i]:
% 18.83/19.07     ( ( v1_relat_1 @ A ) =>
% 18.83/19.07       ( ![B:$i]:
% 18.83/19.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 18.83/19.07  thf('6', plain,
% 18.83/19.07      (![X3 : $i, X4 : $i]:
% 18.83/19.07         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 18.83/19.07          | (v1_relat_1 @ X3)
% 18.83/19.07          | ~ (v1_relat_1 @ X4))),
% 18.83/19.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 18.83/19.07  thf('7', plain,
% 18.83/19.07      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 18.83/19.07      inference('sup-', [status(thm)], ['5', '6'])).
% 18.83/19.07  thf(fc6_relat_1, axiom,
% 18.83/19.07    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 18.83/19.07  thf('8', plain,
% 18.83/19.07      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 18.83/19.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 18.83/19.07  thf('9', plain, ((v1_relat_1 @ sk_D)),
% 18.83/19.07      inference('demod', [status(thm)], ['7', '8'])).
% 18.83/19.07  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 18.83/19.07      inference('demod', [status(thm)], ['4', '9'])).
% 18.83/19.07  thf(d10_xboole_0, axiom,
% 18.83/19.07    (![A:$i,B:$i]:
% 18.83/19.07     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 18.83/19.07  thf('11', plain,
% 18.83/19.07      (![X0 : $i, X2 : $i]:
% 18.83/19.07         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 18.83/19.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 18.83/19.07  thf('12', plain,
% 18.83/19.07      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 18.83/19.07        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 18.83/19.07      inference('sup-', [status(thm)], ['10', '11'])).
% 18.83/19.07  thf('13', plain,
% 18.83/19.07      (((k2_relset_1 @ sk_A @ sk_C @ 
% 18.83/19.07         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf('14', plain,
% 18.83/19.07      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf('15', plain,
% 18.83/19.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf(redefinition_k1_partfun1, axiom,
% 18.83/19.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 18.83/19.07     ( ( ( v1_funct_1 @ E ) & 
% 18.83/19.07         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 18.83/19.07         ( v1_funct_1 @ F ) & 
% 18.83/19.07         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 18.83/19.07       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 18.83/19.07  thf('16', plain,
% 18.83/19.07      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 18.83/19.07         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 18.83/19.07          | ~ (v1_funct_1 @ X40)
% 18.83/19.07          | ~ (v1_funct_1 @ X43)
% 18.83/19.07          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 18.83/19.07          | ((k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43)
% 18.83/19.07              = (k5_relat_1 @ X40 @ X43)))),
% 18.83/19.07      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 18.83/19.07  thf('17', plain,
% 18.83/19.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.83/19.07         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 18.83/19.07            = (k5_relat_1 @ sk_D @ X0))
% 18.83/19.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 18.83/19.07          | ~ (v1_funct_1 @ X0)
% 18.83/19.07          | ~ (v1_funct_1 @ sk_D))),
% 18.83/19.07      inference('sup-', [status(thm)], ['15', '16'])).
% 18.83/19.07  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf('19', plain,
% 18.83/19.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.83/19.07         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 18.83/19.07            = (k5_relat_1 @ sk_D @ X0))
% 18.83/19.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 18.83/19.07          | ~ (v1_funct_1 @ X0))),
% 18.83/19.07      inference('demod', [status(thm)], ['17', '18'])).
% 18.83/19.07  thf('20', plain,
% 18.83/19.07      ((~ (v1_funct_1 @ sk_E)
% 18.83/19.07        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 18.83/19.07            = (k5_relat_1 @ sk_D @ sk_E)))),
% 18.83/19.07      inference('sup-', [status(thm)], ['14', '19'])).
% 18.83/19.07  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf('22', plain,
% 18.83/19.07      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 18.83/19.07         = (k5_relat_1 @ sk_D @ sk_E))),
% 18.83/19.07      inference('demod', [status(thm)], ['20', '21'])).
% 18.83/19.07  thf('23', plain,
% 18.83/19.07      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 18.83/19.07      inference('demod', [status(thm)], ['13', '22'])).
% 18.83/19.07  thf('24', plain,
% 18.83/19.07      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf('25', plain,
% 18.83/19.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf(dt_k4_relset_1, axiom,
% 18.83/19.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 18.83/19.07     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 18.83/19.07         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 18.83/19.07       ( m1_subset_1 @
% 18.83/19.07         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 18.83/19.07         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 18.83/19.07  thf('26', plain,
% 18.83/19.07      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 18.83/19.07         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 18.83/19.07          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 18.83/19.07          | (m1_subset_1 @ (k4_relset_1 @ X15 @ X16 @ X18 @ X19 @ X14 @ X17) @ 
% 18.83/19.07             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X19))))),
% 18.83/19.07      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 18.83/19.07  thf('27', plain,
% 18.83/19.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.83/19.07         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 18.83/19.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 18.83/19.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 18.83/19.07      inference('sup-', [status(thm)], ['25', '26'])).
% 18.83/19.07  thf('28', plain,
% 18.83/19.07      ((m1_subset_1 @ 
% 18.83/19.07        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 18.83/19.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 18.83/19.07      inference('sup-', [status(thm)], ['24', '27'])).
% 18.83/19.07  thf(redefinition_k2_relset_1, axiom,
% 18.83/19.07    (![A:$i,B:$i,C:$i]:
% 18.83/19.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.83/19.07       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 18.83/19.07  thf('29', plain,
% 18.83/19.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 18.83/19.07         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 18.83/19.07          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 18.83/19.07      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 18.83/19.07  thf('30', plain,
% 18.83/19.07      (((k2_relset_1 @ sk_A @ sk_C @ 
% 18.83/19.07         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))
% 18.83/19.07         = (k2_relat_1 @ 
% 18.83/19.07            (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 18.83/19.07      inference('sup-', [status(thm)], ['28', '29'])).
% 18.83/19.07  thf('31', plain,
% 18.83/19.07      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf('32', plain,
% 18.83/19.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf(redefinition_k4_relset_1, axiom,
% 18.83/19.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 18.83/19.07     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 18.83/19.07         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 18.83/19.07       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 18.83/19.07  thf('33', plain,
% 18.83/19.07      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 18.83/19.07         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 18.83/19.07          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 18.83/19.07          | ((k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 18.83/19.07              = (k5_relat_1 @ X26 @ X29)))),
% 18.83/19.07      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 18.83/19.07  thf('34', plain,
% 18.83/19.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.83/19.07         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 18.83/19.07            = (k5_relat_1 @ sk_D @ X0))
% 18.83/19.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 18.83/19.07      inference('sup-', [status(thm)], ['32', '33'])).
% 18.83/19.07  thf('35', plain,
% 18.83/19.07      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 18.83/19.07         = (k5_relat_1 @ sk_D @ sk_E))),
% 18.83/19.07      inference('sup-', [status(thm)], ['31', '34'])).
% 18.83/19.07  thf('36', plain,
% 18.83/19.07      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 18.83/19.07         = (k5_relat_1 @ sk_D @ sk_E))),
% 18.83/19.07      inference('sup-', [status(thm)], ['31', '34'])).
% 18.83/19.07  thf('37', plain,
% 18.83/19.07      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 18.83/19.07         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 18.83/19.07      inference('demod', [status(thm)], ['30', '35', '36'])).
% 18.83/19.07  thf('38', plain, (((sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 18.83/19.07      inference('sup+', [status(thm)], ['23', '37'])).
% 18.83/19.07  thf(t51_funct_1, axiom,
% 18.83/19.07    (![A:$i]:
% 18.83/19.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 18.83/19.07       ( ![B:$i]:
% 18.83/19.07         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 18.83/19.07           ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) & 
% 18.83/19.07               ( v2_funct_1 @ A ) ) =>
% 18.83/19.07             ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 18.83/19.07  thf('39', plain,
% 18.83/19.07      (![X9 : $i, X10 : $i]:
% 18.83/19.07         (~ (v1_relat_1 @ X9)
% 18.83/19.07          | ~ (v1_funct_1 @ X9)
% 18.83/19.07          | (r1_tarski @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X9))
% 18.83/19.07          | ((k2_relat_1 @ (k5_relat_1 @ X9 @ X10)) != (k2_relat_1 @ X10))
% 18.83/19.07          | ~ (v2_funct_1 @ X10)
% 18.83/19.07          | ~ (v1_funct_1 @ X10)
% 18.83/19.07          | ~ (v1_relat_1 @ X10))),
% 18.83/19.07      inference('cnf', [status(esa)], [t51_funct_1])).
% 18.83/19.07  thf('40', plain,
% 18.83/19.07      ((((sk_C) != (k2_relat_1 @ sk_E))
% 18.83/19.07        | ~ (v1_relat_1 @ sk_E)
% 18.83/19.07        | ~ (v1_funct_1 @ sk_E)
% 18.83/19.07        | ~ (v2_funct_1 @ sk_E)
% 18.83/19.07        | (r1_tarski @ (k1_relat_1 @ sk_E) @ (k2_relat_1 @ sk_D))
% 18.83/19.07        | ~ (v1_funct_1 @ sk_D)
% 18.83/19.07        | ~ (v1_relat_1 @ sk_D))),
% 18.83/19.07      inference('sup-', [status(thm)], ['38', '39'])).
% 18.83/19.07  thf('41', plain,
% 18.83/19.07      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf('42', plain,
% 18.83/19.07      (![X3 : $i, X4 : $i]:
% 18.83/19.07         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 18.83/19.07          | (v1_relat_1 @ X3)
% 18.83/19.07          | ~ (v1_relat_1 @ X4))),
% 18.83/19.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 18.83/19.07  thf('43', plain,
% 18.83/19.07      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 18.83/19.07      inference('sup-', [status(thm)], ['41', '42'])).
% 18.83/19.07  thf('44', plain,
% 18.83/19.07      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 18.83/19.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 18.83/19.07  thf('45', plain, ((v1_relat_1 @ sk_E)),
% 18.83/19.07      inference('demod', [status(thm)], ['43', '44'])).
% 18.83/19.07  thf('46', plain, ((v1_funct_1 @ sk_E)),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf('47', plain, ((v2_funct_1 @ sk_E)),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf('48', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf(d1_funct_2, axiom,
% 18.83/19.07    (![A:$i,B:$i,C:$i]:
% 18.83/19.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.83/19.07       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 18.83/19.07           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 18.83/19.07             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 18.83/19.07         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 18.83/19.07           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 18.83/19.07             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 18.83/19.07  thf(zf_stmt_1, axiom,
% 18.83/19.07    (![C:$i,B:$i,A:$i]:
% 18.83/19.07     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 18.83/19.07       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 18.83/19.07  thf('49', plain,
% 18.83/19.07      (![X34 : $i, X35 : $i, X36 : $i]:
% 18.83/19.07         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 18.83/19.07          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 18.83/19.07          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_1])).
% 18.83/19.07  thf('50', plain,
% 18.83/19.07      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 18.83/19.07        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 18.83/19.07      inference('sup-', [status(thm)], ['48', '49'])).
% 18.83/19.07  thf(zf_stmt_2, axiom,
% 18.83/19.07    (![B:$i,A:$i]:
% 18.83/19.07     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 18.83/19.07       ( zip_tseitin_0 @ B @ A ) ))).
% 18.83/19.07  thf('51', plain,
% 18.83/19.07      (![X32 : $i, X33 : $i]:
% 18.83/19.07         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 18.83/19.07  thf('52', plain,
% 18.83/19.07      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 18.83/19.07  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 18.83/19.07  thf(zf_stmt_5, axiom,
% 18.83/19.07    (![A:$i,B:$i,C:$i]:
% 18.83/19.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.83/19.07       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 18.83/19.07         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 18.83/19.07           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 18.83/19.07             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 18.83/19.07  thf('53', plain,
% 18.83/19.07      (![X37 : $i, X38 : $i, X39 : $i]:
% 18.83/19.07         (~ (zip_tseitin_0 @ X37 @ X38)
% 18.83/19.07          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 18.83/19.07          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 18.83/19.07  thf('54', plain,
% 18.83/19.07      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 18.83/19.07      inference('sup-', [status(thm)], ['52', '53'])).
% 18.83/19.07  thf('55', plain,
% 18.83/19.07      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 18.83/19.07      inference('sup-', [status(thm)], ['51', '54'])).
% 18.83/19.07  thf('56', plain, (((sk_C) != (k1_xboole_0))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf('57', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 18.83/19.07      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 18.83/19.07  thf('58', plain,
% 18.83/19.07      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf(redefinition_k1_relset_1, axiom,
% 18.83/19.07    (![A:$i,B:$i,C:$i]:
% 18.83/19.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.83/19.07       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 18.83/19.07  thf('59', plain,
% 18.83/19.07      (![X20 : $i, X21 : $i, X22 : $i]:
% 18.83/19.07         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 18.83/19.07          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 18.83/19.07      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 18.83/19.07  thf('60', plain,
% 18.83/19.07      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 18.83/19.07      inference('sup-', [status(thm)], ['58', '59'])).
% 18.83/19.07  thf('61', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 18.83/19.07      inference('demod', [status(thm)], ['50', '57', '60'])).
% 18.83/19.07  thf('62', plain, ((v1_funct_1 @ sk_D)),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 18.83/19.07      inference('demod', [status(thm)], ['7', '8'])).
% 18.83/19.07  thf('64', plain,
% 18.83/19.07      ((((sk_C) != (k2_relat_1 @ sk_E))
% 18.83/19.07        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 18.83/19.07      inference('demod', [status(thm)],
% 18.83/19.07                ['40', '45', '46', '47', '61', '62', '63'])).
% 18.83/19.07  thf('65', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 18.83/19.07      inference('demod', [status(thm)], ['50', '57', '60'])).
% 18.83/19.07  thf(t3_funct_2, axiom,
% 18.83/19.07    (![A:$i]:
% 18.83/19.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 18.83/19.07       ( ( v1_funct_1 @ A ) & 
% 18.83/19.07         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 18.83/19.07         ( m1_subset_1 @
% 18.83/19.07           A @ 
% 18.83/19.07           ( k1_zfmisc_1 @
% 18.83/19.07             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 18.83/19.07  thf('66', plain,
% 18.83/19.07      (![X46 : $i]:
% 18.83/19.07         ((m1_subset_1 @ X46 @ 
% 18.83/19.07           (k1_zfmisc_1 @ 
% 18.83/19.07            (k2_zfmisc_1 @ (k1_relat_1 @ X46) @ (k2_relat_1 @ X46))))
% 18.83/19.07          | ~ (v1_funct_1 @ X46)
% 18.83/19.07          | ~ (v1_relat_1 @ X46))),
% 18.83/19.07      inference('cnf', [status(esa)], [t3_funct_2])).
% 18.83/19.07  thf('67', plain,
% 18.83/19.07      (((m1_subset_1 @ sk_E @ 
% 18.83/19.07         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_E))))
% 18.83/19.07        | ~ (v1_relat_1 @ sk_E)
% 18.83/19.07        | ~ (v1_funct_1 @ sk_E))),
% 18.83/19.07      inference('sup+', [status(thm)], ['65', '66'])).
% 18.83/19.07  thf('68', plain, ((v1_relat_1 @ sk_E)),
% 18.83/19.07      inference('demod', [status(thm)], ['43', '44'])).
% 18.83/19.07  thf('69', plain, ((v1_funct_1 @ sk_E)),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf('70', plain,
% 18.83/19.07      ((m1_subset_1 @ sk_E @ 
% 18.83/19.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_E))))),
% 18.83/19.07      inference('demod', [status(thm)], ['67', '68', '69'])).
% 18.83/19.07  thf('71', plain,
% 18.83/19.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.83/19.07         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 18.83/19.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 18.83/19.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 18.83/19.07      inference('sup-', [status(thm)], ['25', '26'])).
% 18.83/19.07  thf('72', plain,
% 18.83/19.07      ((m1_subset_1 @ 
% 18.83/19.07        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ sk_E) @ 
% 18.83/19.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_E))))),
% 18.83/19.07      inference('sup-', [status(thm)], ['70', '71'])).
% 18.83/19.07  thf('73', plain,
% 18.83/19.07      (![X11 : $i, X12 : $i, X13 : $i]:
% 18.83/19.07         ((v5_relat_1 @ X11 @ X13)
% 18.83/19.07          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 18.83/19.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 18.83/19.07  thf('74', plain,
% 18.83/19.07      ((v5_relat_1 @ 
% 18.83/19.07        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ sk_E) @ 
% 18.83/19.07        (k2_relat_1 @ sk_E))),
% 18.83/19.07      inference('sup-', [status(thm)], ['72', '73'])).
% 18.83/19.07  thf('75', plain,
% 18.83/19.07      (![X5 : $i, X6 : $i]:
% 18.83/19.07         (~ (v5_relat_1 @ X5 @ X6)
% 18.83/19.07          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 18.83/19.07          | ~ (v1_relat_1 @ X5))),
% 18.83/19.07      inference('cnf', [status(esa)], [d19_relat_1])).
% 18.83/19.07  thf('76', plain,
% 18.83/19.07      ((~ (v1_relat_1 @ 
% 18.83/19.07           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ 
% 18.83/19.07            sk_E))
% 18.83/19.07        | (r1_tarski @ 
% 18.83/19.07           (k2_relat_1 @ 
% 18.83/19.07            (k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ 
% 18.83/19.07             sk_E)) @ 
% 18.83/19.07           (k2_relat_1 @ sk_E)))),
% 18.83/19.07      inference('sup-', [status(thm)], ['74', '75'])).
% 18.83/19.07  thf('77', plain,
% 18.83/19.07      ((m1_subset_1 @ 
% 18.83/19.07        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ sk_E) @ 
% 18.83/19.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_E))))),
% 18.83/19.07      inference('sup-', [status(thm)], ['70', '71'])).
% 18.83/19.07  thf('78', plain,
% 18.83/19.07      (![X3 : $i, X4 : $i]:
% 18.83/19.07         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 18.83/19.07          | (v1_relat_1 @ X3)
% 18.83/19.07          | ~ (v1_relat_1 @ X4))),
% 18.83/19.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 18.83/19.07  thf('79', plain,
% 18.83/19.07      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_E)))
% 18.83/19.07        | (v1_relat_1 @ 
% 18.83/19.07           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ 
% 18.83/19.07            sk_E)))),
% 18.83/19.07      inference('sup-', [status(thm)], ['77', '78'])).
% 18.83/19.07  thf('80', plain,
% 18.83/19.07      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 18.83/19.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 18.83/19.07  thf('81', plain,
% 18.83/19.07      ((v1_relat_1 @ 
% 18.83/19.07        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ sk_E))),
% 18.83/19.07      inference('demod', [status(thm)], ['79', '80'])).
% 18.83/19.07  thf('82', plain,
% 18.83/19.07      ((r1_tarski @ 
% 18.83/19.07        (k2_relat_1 @ 
% 18.83/19.07         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ sk_E)) @ 
% 18.83/19.07        (k2_relat_1 @ sk_E))),
% 18.83/19.07      inference('demod', [status(thm)], ['76', '81'])).
% 18.83/19.07  thf('83', plain,
% 18.83/19.07      ((m1_subset_1 @ sk_E @ 
% 18.83/19.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_E))))),
% 18.83/19.07      inference('demod', [status(thm)], ['67', '68', '69'])).
% 18.83/19.07  thf('84', plain,
% 18.83/19.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.83/19.07         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 18.83/19.07            = (k5_relat_1 @ sk_D @ X0))
% 18.83/19.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 18.83/19.07      inference('sup-', [status(thm)], ['32', '33'])).
% 18.83/19.07  thf('85', plain,
% 18.83/19.07      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ sk_E)
% 18.83/19.07         = (k5_relat_1 @ sk_D @ sk_E))),
% 18.83/19.07      inference('sup-', [status(thm)], ['83', '84'])).
% 18.83/19.07  thf('86', plain,
% 18.83/19.07      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) @ 
% 18.83/19.07        (k2_relat_1 @ sk_E))),
% 18.83/19.07      inference('demod', [status(thm)], ['82', '85'])).
% 18.83/19.07  thf('87', plain,
% 18.83/19.07      (![X0 : $i, X2 : $i]:
% 18.83/19.07         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 18.83/19.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 18.83/19.07  thf('88', plain,
% 18.83/19.07      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ 
% 18.83/19.07           (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 18.83/19.07        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))))),
% 18.83/19.07      inference('sup-', [status(thm)], ['86', '87'])).
% 18.83/19.07  thf('89', plain, (((sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 18.83/19.07      inference('sup+', [status(thm)], ['23', '37'])).
% 18.83/19.07  thf('90', plain,
% 18.83/19.07      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf('91', plain,
% 18.83/19.07      (![X11 : $i, X12 : $i, X13 : $i]:
% 18.83/19.07         ((v5_relat_1 @ X11 @ X13)
% 18.83/19.07          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 18.83/19.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 18.83/19.07  thf('92', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 18.83/19.07      inference('sup-', [status(thm)], ['90', '91'])).
% 18.83/19.07  thf('93', plain,
% 18.83/19.07      (![X5 : $i, X6 : $i]:
% 18.83/19.07         (~ (v5_relat_1 @ X5 @ X6)
% 18.83/19.07          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 18.83/19.07          | ~ (v1_relat_1 @ X5))),
% 18.83/19.07      inference('cnf', [status(esa)], [d19_relat_1])).
% 18.83/19.07  thf('94', plain,
% 18.83/19.07      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 18.83/19.07      inference('sup-', [status(thm)], ['92', '93'])).
% 18.83/19.07  thf('95', plain, ((v1_relat_1 @ sk_E)),
% 18.83/19.07      inference('demod', [status(thm)], ['43', '44'])).
% 18.83/19.07  thf('96', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 18.83/19.07      inference('demod', [status(thm)], ['94', '95'])).
% 18.83/19.07  thf('97', plain, (((sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 18.83/19.07      inference('sup+', [status(thm)], ['23', '37'])).
% 18.83/19.07  thf('98', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 18.83/19.07      inference('demod', [status(thm)], ['88', '89', '96', '97'])).
% 18.83/19.07  thf('99', plain,
% 18.83/19.07      ((((sk_C) != (sk_C)) | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 18.83/19.07      inference('demod', [status(thm)], ['64', '98'])).
% 18.83/19.07  thf('100', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))),
% 18.83/19.07      inference('simplify', [status(thm)], ['99'])).
% 18.83/19.07  thf('101', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 18.83/19.07      inference('demod', [status(thm)], ['12', '100'])).
% 18.83/19.07  thf('102', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf('103', plain,
% 18.83/19.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.83/19.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.83/19.07  thf('104', plain,
% 18.83/19.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 18.83/19.07         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 18.83/19.07          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 18.83/19.07      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 18.83/19.07  thf('105', plain,
% 18.83/19.07      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 18.83/19.07      inference('sup-', [status(thm)], ['103', '104'])).
% 18.83/19.07  thf('106', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 18.83/19.07      inference('demod', [status(thm)], ['102', '105'])).
% 18.83/19.07  thf('107', plain, ($false),
% 18.83/19.07      inference('simplify_reflect-', [status(thm)], ['101', '106'])).
% 18.83/19.07  
% 18.83/19.07  % SZS output end Refutation
% 18.83/19.07  
% 18.83/19.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
