%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qHgiRwuYH9

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:59 EST 2020

% Result     : Theorem 6.64s
% Output     : Refutation 6.64s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 286 expanded)
%              Number of leaves         :   41 ( 101 expanded)
%              Depth                    :   13
%              Number of atoms          : 1092 (6023 expanded)
%              Number of equality atoms :   64 ( 357 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('13',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('22',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k4_relset_1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['28','37'])).

thf('39',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['27','38'])).

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

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X9 ) @ ( k2_relat_1 @ X8 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) )
       != ( k2_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t51_funct_1])).

thf('41',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( r1_tarski @ ( k1_relat_1 @ sk_E ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('44',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['42','43'])).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('64',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['41','44','45','46','60','61','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['27','38'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('67',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) ) @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('68',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('73',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('76',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_E ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('79',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['27','38'])).

thf('81',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['42','43'])).

thf('82',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['62','63'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['70','79','80','81','82'])).

thf('84',plain,
    ( ( sk_C != sk_C )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['65','83'])).

thf('85',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['14','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qHgiRwuYH9
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 6.64/6.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.64/6.85  % Solved by: fo/fo7.sh
% 6.64/6.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.64/6.85  % done 918 iterations in 6.380s
% 6.64/6.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.64/6.85  % SZS output start Refutation
% 6.64/6.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.64/6.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.64/6.85  thf(sk_A_type, type, sk_A: $i).
% 6.64/6.85  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.64/6.85  thf(sk_D_type, type, sk_D: $i).
% 6.64/6.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.64/6.85  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.64/6.85  thf(sk_C_type, type, sk_C: $i).
% 6.64/6.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.64/6.85  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.64/6.85  thf(sk_E_type, type, sk_E: $i).
% 6.64/6.85  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 6.64/6.85  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 6.64/6.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.64/6.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.64/6.85  thf(sk_B_type, type, sk_B: $i).
% 6.64/6.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.64/6.85  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.64/6.85  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.64/6.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.64/6.85  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 6.64/6.85  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.64/6.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.64/6.85  thf(t28_funct_2, conjecture,
% 6.64/6.85    (![A:$i,B:$i,C:$i,D:$i]:
% 6.64/6.85     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.64/6.85         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.64/6.85       ( ![E:$i]:
% 6.64/6.85         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 6.64/6.85             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 6.64/6.85           ( ( ( ( k2_relset_1 @
% 6.64/6.85                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 6.64/6.85                 ( C ) ) & 
% 6.64/6.85               ( v2_funct_1 @ E ) ) =>
% 6.64/6.85             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 6.64/6.85               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 6.64/6.85  thf(zf_stmt_0, negated_conjecture,
% 6.64/6.85    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 6.64/6.85        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.64/6.85            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.64/6.85          ( ![E:$i]:
% 6.64/6.85            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 6.64/6.85                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 6.64/6.85              ( ( ( ( k2_relset_1 @
% 6.64/6.85                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 6.64/6.85                    ( C ) ) & 
% 6.64/6.85                  ( v2_funct_1 @ E ) ) =>
% 6.64/6.85                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 6.64/6.85                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 6.64/6.85    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 6.64/6.85  thf('0', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf(dt_k2_relset_1, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i]:
% 6.64/6.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.64/6.85       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 6.64/6.85  thf('1', plain,
% 6.64/6.85      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.64/6.85         ((m1_subset_1 @ (k2_relset_1 @ X13 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 6.64/6.85          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 6.64/6.85      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 6.64/6.85  thf('2', plain,
% 6.64/6.85      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 6.64/6.85      inference('sup-', [status(thm)], ['0', '1'])).
% 6.64/6.85  thf('3', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf(redefinition_k2_relset_1, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i]:
% 6.64/6.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.64/6.85       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.64/6.85  thf('4', plain,
% 6.64/6.85      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.64/6.85         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 6.64/6.85          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 6.64/6.85      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.64/6.85  thf('5', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 6.64/6.85      inference('sup-', [status(thm)], ['3', '4'])).
% 6.64/6.85  thf('6', plain, ((m1_subset_1 @ (k2_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 6.64/6.85      inference('demod', [status(thm)], ['2', '5'])).
% 6.64/6.85  thf(t3_subset, axiom,
% 6.64/6.85    (![A:$i,B:$i]:
% 6.64/6.85     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.64/6.85  thf('7', plain,
% 6.64/6.85      (![X3 : $i, X4 : $i]:
% 6.64/6.85         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 6.64/6.85      inference('cnf', [status(esa)], [t3_subset])).
% 6.64/6.85  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 6.64/6.85      inference('sup-', [status(thm)], ['6', '7'])).
% 6.64/6.85  thf(d10_xboole_0, axiom,
% 6.64/6.85    (![A:$i,B:$i]:
% 6.64/6.85     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.64/6.85  thf('9', plain,
% 6.64/6.85      (![X0 : $i, X2 : $i]:
% 6.64/6.85         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.64/6.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.64/6.85  thf('10', plain,
% 6.64/6.85      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 6.64/6.85        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['8', '9'])).
% 6.64/6.85  thf('11', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('12', plain,
% 6.64/6.85      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 6.64/6.85      inference('sup-', [status(thm)], ['3', '4'])).
% 6.64/6.85  thf('13', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 6.64/6.85      inference('demod', [status(thm)], ['11', '12'])).
% 6.64/6.85  thf('14', plain, (~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))),
% 6.64/6.85      inference('simplify_reflect-', [status(thm)], ['10', '13'])).
% 6.64/6.85  thf('15', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('16', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf(dt_k4_relset_1, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.64/6.85     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.64/6.85         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.64/6.85       ( m1_subset_1 @
% 6.64/6.85         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 6.64/6.85         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 6.64/6.85  thf('17', plain,
% 6.64/6.85      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 6.64/6.85         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 6.64/6.85          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 6.64/6.85          | (m1_subset_1 @ (k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19) @ 
% 6.64/6.85             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X21))))),
% 6.64/6.85      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 6.64/6.85  thf('18', plain,
% 6.64/6.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.64/6.85         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 6.64/6.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.64/6.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 6.64/6.85      inference('sup-', [status(thm)], ['16', '17'])).
% 6.64/6.85  thf('19', plain,
% 6.64/6.85      ((m1_subset_1 @ 
% 6.64/6.85        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 6.64/6.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['15', '18'])).
% 6.64/6.85  thf('20', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('21', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf(redefinition_k4_relset_1, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.64/6.85     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.64/6.85         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.64/6.85       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 6.64/6.85  thf('22', plain,
% 6.64/6.85      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 6.64/6.85         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 6.64/6.85          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 6.64/6.85          | ((k4_relset_1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 6.64/6.85              = (k5_relat_1 @ X28 @ X31)))),
% 6.64/6.85      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 6.64/6.85  thf('23', plain,
% 6.64/6.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.64/6.85         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 6.64/6.85            = (k5_relat_1 @ sk_D @ X0))
% 6.64/6.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 6.64/6.85      inference('sup-', [status(thm)], ['21', '22'])).
% 6.64/6.85  thf('24', plain,
% 6.64/6.85      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 6.64/6.85         = (k5_relat_1 @ sk_D @ sk_E))),
% 6.64/6.85      inference('sup-', [status(thm)], ['20', '23'])).
% 6.64/6.85  thf('25', plain,
% 6.64/6.85      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 6.64/6.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 6.64/6.85      inference('demod', [status(thm)], ['19', '24'])).
% 6.64/6.85  thf('26', plain,
% 6.64/6.85      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.64/6.85         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 6.64/6.85          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 6.64/6.85      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.64/6.85  thf('27', plain,
% 6.64/6.85      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 6.64/6.85         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['25', '26'])).
% 6.64/6.85  thf('28', plain,
% 6.64/6.85      (((k2_relset_1 @ sk_A @ sk_C @ 
% 6.64/6.85         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('29', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('30', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf(redefinition_k1_partfun1, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.64/6.85     ( ( ( v1_funct_1 @ E ) & 
% 6.64/6.85         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.64/6.85         ( v1_funct_1 @ F ) & 
% 6.64/6.85         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.64/6.85       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 6.64/6.85  thf('31', plain,
% 6.64/6.85      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 6.64/6.85         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 6.64/6.85          | ~ (v1_funct_1 @ X42)
% 6.64/6.85          | ~ (v1_funct_1 @ X45)
% 6.64/6.85          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 6.64/6.85          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 6.64/6.85              = (k5_relat_1 @ X42 @ X45)))),
% 6.64/6.85      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 6.64/6.85  thf('32', plain,
% 6.64/6.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.64/6.85         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 6.64/6.85            = (k5_relat_1 @ sk_D @ X0))
% 6.64/6.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.64/6.85          | ~ (v1_funct_1 @ X0)
% 6.64/6.85          | ~ (v1_funct_1 @ sk_D))),
% 6.64/6.85      inference('sup-', [status(thm)], ['30', '31'])).
% 6.64/6.85  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('34', plain,
% 6.64/6.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.64/6.85         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 6.64/6.85            = (k5_relat_1 @ sk_D @ X0))
% 6.64/6.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.64/6.85          | ~ (v1_funct_1 @ X0))),
% 6.64/6.85      inference('demod', [status(thm)], ['32', '33'])).
% 6.64/6.85  thf('35', plain,
% 6.64/6.85      ((~ (v1_funct_1 @ sk_E)
% 6.64/6.85        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 6.64/6.85            = (k5_relat_1 @ sk_D @ sk_E)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['29', '34'])).
% 6.64/6.85  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('37', plain,
% 6.64/6.85      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 6.64/6.85         = (k5_relat_1 @ sk_D @ sk_E))),
% 6.64/6.85      inference('demod', [status(thm)], ['35', '36'])).
% 6.64/6.85  thf('38', plain,
% 6.64/6.85      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 6.64/6.85      inference('demod', [status(thm)], ['28', '37'])).
% 6.64/6.85  thf('39', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 6.64/6.85      inference('sup+', [status(thm)], ['27', '38'])).
% 6.64/6.85  thf(t51_funct_1, axiom,
% 6.64/6.85    (![A:$i]:
% 6.64/6.85     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.64/6.85       ( ![B:$i]:
% 6.64/6.85         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.64/6.85           ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) & 
% 6.64/6.85               ( v2_funct_1 @ A ) ) =>
% 6.64/6.85             ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 6.64/6.85  thf('40', plain,
% 6.64/6.85      (![X8 : $i, X9 : $i]:
% 6.64/6.85         (~ (v1_relat_1 @ X8)
% 6.64/6.85          | ~ (v1_funct_1 @ X8)
% 6.64/6.85          | (r1_tarski @ (k1_relat_1 @ X9) @ (k2_relat_1 @ X8))
% 6.64/6.85          | ((k2_relat_1 @ (k5_relat_1 @ X8 @ X9)) != (k2_relat_1 @ X9))
% 6.64/6.85          | ~ (v2_funct_1 @ X9)
% 6.64/6.85          | ~ (v1_funct_1 @ X9)
% 6.64/6.85          | ~ (v1_relat_1 @ X9))),
% 6.64/6.85      inference('cnf', [status(esa)], [t51_funct_1])).
% 6.64/6.85  thf('41', plain,
% 6.64/6.85      ((((sk_C) != (k2_relat_1 @ sk_E))
% 6.64/6.85        | ~ (v1_relat_1 @ sk_E)
% 6.64/6.85        | ~ (v1_funct_1 @ sk_E)
% 6.64/6.85        | ~ (v2_funct_1 @ sk_E)
% 6.64/6.85        | (r1_tarski @ (k1_relat_1 @ sk_E) @ (k2_relat_1 @ sk_D))
% 6.64/6.85        | ~ (v1_funct_1 @ sk_D)
% 6.64/6.85        | ~ (v1_relat_1 @ sk_D))),
% 6.64/6.85      inference('sup-', [status(thm)], ['39', '40'])).
% 6.64/6.85  thf('42', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf(cc1_relset_1, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i]:
% 6.64/6.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.64/6.85       ( v1_relat_1 @ C ) ))).
% 6.64/6.85  thf('43', plain,
% 6.64/6.85      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.64/6.85         ((v1_relat_1 @ X10)
% 6.64/6.85          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 6.64/6.85      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.64/6.85  thf('44', plain, ((v1_relat_1 @ sk_E)),
% 6.64/6.85      inference('sup-', [status(thm)], ['42', '43'])).
% 6.64/6.85  thf('45', plain, ((v1_funct_1 @ sk_E)),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('46', plain, ((v2_funct_1 @ sk_E)),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('47', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf(d1_funct_2, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i]:
% 6.64/6.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.64/6.85       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.64/6.85           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.64/6.85             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.64/6.85         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.64/6.85           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.64/6.85             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.64/6.85  thf(zf_stmt_1, axiom,
% 6.64/6.85    (![C:$i,B:$i,A:$i]:
% 6.64/6.85     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.64/6.85       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.64/6.85  thf('48', plain,
% 6.64/6.85      (![X36 : $i, X37 : $i, X38 : $i]:
% 6.64/6.85         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 6.64/6.85          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 6.64/6.85          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.64/6.85  thf('49', plain,
% 6.64/6.85      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 6.64/6.85        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['47', '48'])).
% 6.64/6.85  thf(zf_stmt_2, axiom,
% 6.64/6.85    (![B:$i,A:$i]:
% 6.64/6.85     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.64/6.85       ( zip_tseitin_0 @ B @ A ) ))).
% 6.64/6.85  thf('50', plain,
% 6.64/6.85      (![X34 : $i, X35 : $i]:
% 6.64/6.85         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.64/6.85  thf('51', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.64/6.85  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 6.64/6.85  thf(zf_stmt_5, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i]:
% 6.64/6.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.64/6.85       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.64/6.85         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.64/6.85           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.64/6.85             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.64/6.85  thf('52', plain,
% 6.64/6.85      (![X39 : $i, X40 : $i, X41 : $i]:
% 6.64/6.85         (~ (zip_tseitin_0 @ X39 @ X40)
% 6.64/6.85          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 6.64/6.85          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.64/6.85  thf('53', plain,
% 6.64/6.85      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 6.64/6.85      inference('sup-', [status(thm)], ['51', '52'])).
% 6.64/6.85  thf('54', plain,
% 6.64/6.85      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 6.64/6.85      inference('sup-', [status(thm)], ['50', '53'])).
% 6.64/6.85  thf('55', plain, (((sk_C) != (k1_xboole_0))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('56', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 6.64/6.85      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 6.64/6.85  thf('57', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf(redefinition_k1_relset_1, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i]:
% 6.64/6.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.64/6.85       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.64/6.85  thf('58', plain,
% 6.64/6.85      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.64/6.85         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 6.64/6.85          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 6.64/6.85      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.64/6.85  thf('59', plain,
% 6.64/6.85      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 6.64/6.85      inference('sup-', [status(thm)], ['57', '58'])).
% 6.64/6.85  thf('60', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 6.64/6.85      inference('demod', [status(thm)], ['49', '56', '59'])).
% 6.64/6.85  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('62', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('63', plain,
% 6.64/6.85      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.64/6.85         ((v1_relat_1 @ X10)
% 6.64/6.85          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 6.64/6.85      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.64/6.85  thf('64', plain, ((v1_relat_1 @ sk_D)),
% 6.64/6.85      inference('sup-', [status(thm)], ['62', '63'])).
% 6.64/6.85  thf('65', plain,
% 6.64/6.85      ((((sk_C) != (k2_relat_1 @ sk_E))
% 6.64/6.85        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 6.64/6.85      inference('demod', [status(thm)],
% 6.64/6.85                ['41', '44', '45', '46', '60', '61', '64'])).
% 6.64/6.85  thf('66', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 6.64/6.85      inference('sup+', [status(thm)], ['27', '38'])).
% 6.64/6.85  thf(t45_relat_1, axiom,
% 6.64/6.85    (![A:$i]:
% 6.64/6.85     ( ( v1_relat_1 @ A ) =>
% 6.64/6.85       ( ![B:$i]:
% 6.64/6.85         ( ( v1_relat_1 @ B ) =>
% 6.64/6.85           ( r1_tarski @
% 6.64/6.85             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 6.64/6.85  thf('67', plain,
% 6.64/6.85      (![X6 : $i, X7 : $i]:
% 6.64/6.85         (~ (v1_relat_1 @ X6)
% 6.64/6.85          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X7 @ X6)) @ 
% 6.64/6.85             (k2_relat_1 @ X6))
% 6.64/6.85          | ~ (v1_relat_1 @ X7))),
% 6.64/6.85      inference('cnf', [status(esa)], [t45_relat_1])).
% 6.64/6.85  thf('68', plain,
% 6.64/6.85      (![X0 : $i, X2 : $i]:
% 6.64/6.85         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.64/6.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.64/6.85  thf('69', plain,
% 6.64/6.85      (![X0 : $i, X1 : $i]:
% 6.64/6.85         (~ (v1_relat_1 @ X1)
% 6.64/6.85          | ~ (v1_relat_1 @ X0)
% 6.64/6.85          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 6.64/6.85               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 6.64/6.85          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 6.64/6.85      inference('sup-', [status(thm)], ['67', '68'])).
% 6.64/6.85  thf('70', plain,
% 6.64/6.85      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)
% 6.64/6.85        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 6.64/6.85        | ~ (v1_relat_1 @ sk_E)
% 6.64/6.85        | ~ (v1_relat_1 @ sk_D))),
% 6.64/6.85      inference('sup-', [status(thm)], ['66', '69'])).
% 6.64/6.85  thf('71', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('72', plain,
% 6.64/6.85      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.64/6.85         ((m1_subset_1 @ (k2_relset_1 @ X13 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 6.64/6.85          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 6.64/6.85      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 6.64/6.85  thf('73', plain,
% 6.64/6.85      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_C @ sk_E) @ (k1_zfmisc_1 @ sk_C))),
% 6.64/6.85      inference('sup-', [status(thm)], ['71', '72'])).
% 6.64/6.85  thf('74', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('75', plain,
% 6.64/6.85      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.64/6.85         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 6.64/6.85          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 6.64/6.85      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.64/6.85  thf('76', plain,
% 6.64/6.85      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 6.64/6.85      inference('sup-', [status(thm)], ['74', '75'])).
% 6.64/6.85  thf('77', plain,
% 6.64/6.85      ((m1_subset_1 @ (k2_relat_1 @ sk_E) @ (k1_zfmisc_1 @ sk_C))),
% 6.64/6.85      inference('demod', [status(thm)], ['73', '76'])).
% 6.64/6.85  thf('78', plain,
% 6.64/6.85      (![X3 : $i, X4 : $i]:
% 6.64/6.85         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 6.64/6.85      inference('cnf', [status(esa)], [t3_subset])).
% 6.64/6.85  thf('79', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 6.64/6.85      inference('sup-', [status(thm)], ['77', '78'])).
% 6.64/6.85  thf('80', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 6.64/6.85      inference('sup+', [status(thm)], ['27', '38'])).
% 6.64/6.85  thf('81', plain, ((v1_relat_1 @ sk_E)),
% 6.64/6.85      inference('sup-', [status(thm)], ['42', '43'])).
% 6.64/6.85  thf('82', plain, ((v1_relat_1 @ sk_D)),
% 6.64/6.85      inference('sup-', [status(thm)], ['62', '63'])).
% 6.64/6.85  thf('83', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 6.64/6.85      inference('demod', [status(thm)], ['70', '79', '80', '81', '82'])).
% 6.64/6.85  thf('84', plain,
% 6.64/6.85      ((((sk_C) != (sk_C)) | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 6.64/6.85      inference('demod', [status(thm)], ['65', '83'])).
% 6.64/6.85  thf('85', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))),
% 6.64/6.85      inference('simplify', [status(thm)], ['84'])).
% 6.64/6.85  thf('86', plain, ($false), inference('demod', [status(thm)], ['14', '85'])).
% 6.64/6.85  
% 6.64/6.85  % SZS output end Refutation
% 6.64/6.85  
% 6.64/6.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
