%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KkKPqLEi13

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:00 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 298 expanded)
%              Number of leaves         :   42 ( 105 expanded)
%              Depth                    :   13
%              Number of atoms          : 1116 (6079 expanded)
%              Number of equality atoms :   64 ( 357 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X22 ) ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k4_relset_1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ ( k2_relat_1 @ X12 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) )
       != ( k2_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('46',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
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

thf('50',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('52',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('55',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('60',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('61',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['51','58','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('68',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['41','46','47','48','62','63','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['27','38'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('71',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('72',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('77',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('80',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_E ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('83',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['27','38'])).

thf('85',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['44','45'])).

thf('86',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['66','67'])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['74','83','84','85','86'])).

thf('88',plain,
    ( ( sk_C != sk_C )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['69','87'])).

thf('89',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['14','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KkKPqLEi13
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:56:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.76/2.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.76/2.99  % Solved by: fo/fo7.sh
% 2.76/2.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.76/2.99  % done 993 iterations in 2.533s
% 2.76/2.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.76/2.99  % SZS output start Refutation
% 2.76/2.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.76/2.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.76/2.99  thf(sk_A_type, type, sk_A: $i).
% 2.76/2.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.76/2.99  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 2.76/2.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.76/2.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.76/2.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.76/2.99  thf(sk_B_type, type, sk_B: $i).
% 2.76/2.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.76/2.99  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.76/2.99  thf(sk_E_type, type, sk_E: $i).
% 2.76/2.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.76/2.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.76/2.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.76/2.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.76/2.99  thf(sk_D_type, type, sk_D: $i).
% 2.76/2.99  thf(sk_C_type, type, sk_C: $i).
% 2.76/2.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.76/2.99  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.76/2.99  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.76/2.99  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.76/2.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.76/2.99  thf(t28_funct_2, conjecture,
% 2.76/2.99    (![A:$i,B:$i,C:$i,D:$i]:
% 2.76/2.99     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.76/2.99         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.76/2.99       ( ![E:$i]:
% 2.76/2.99         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.76/2.99             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.76/2.99           ( ( ( ( k2_relset_1 @
% 2.76/2.99                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.76/2.99                 ( C ) ) & 
% 2.76/2.99               ( v2_funct_1 @ E ) ) =>
% 2.76/2.99             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.76/2.99               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 2.76/2.99  thf(zf_stmt_0, negated_conjecture,
% 2.76/2.99    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.76/2.99        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.76/2.99            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.76/2.99          ( ![E:$i]:
% 2.76/2.99            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.76/2.99                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.76/2.99              ( ( ( ( k2_relset_1 @
% 2.76/2.99                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.76/2.99                    ( C ) ) & 
% 2.76/2.99                  ( v2_funct_1 @ E ) ) =>
% 2.76/2.99                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.76/2.99                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 2.76/2.99    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 2.76/2.99  thf('0', plain,
% 2.76/2.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf(dt_k2_relset_1, axiom,
% 2.76/2.99    (![A:$i,B:$i,C:$i]:
% 2.76/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.76/2.99       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 2.76/2.99  thf('1', plain,
% 2.76/2.99      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.76/2.99         ((m1_subset_1 @ (k2_relset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 2.76/2.99          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.76/2.99      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 2.76/2.99  thf('2', plain,
% 2.76/2.99      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 2.76/2.99      inference('sup-', [status(thm)], ['0', '1'])).
% 2.76/2.99  thf('3', plain,
% 2.76/2.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf(redefinition_k2_relset_1, axiom,
% 2.76/2.99    (![A:$i,B:$i,C:$i]:
% 2.76/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.76/2.99       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.76/2.99  thf('4', plain,
% 2.76/2.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.76/2.99         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 2.76/2.99          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 2.76/2.99      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.76/2.99  thf('5', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.76/2.99      inference('sup-', [status(thm)], ['3', '4'])).
% 2.76/2.99  thf('6', plain, ((m1_subset_1 @ (k2_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 2.76/2.99      inference('demod', [status(thm)], ['2', '5'])).
% 2.76/2.99  thf(t3_subset, axiom,
% 2.76/2.99    (![A:$i,B:$i]:
% 2.76/2.99     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.76/2.99  thf('7', plain,
% 2.76/2.99      (![X3 : $i, X4 : $i]:
% 2.76/2.99         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 2.76/2.99      inference('cnf', [status(esa)], [t3_subset])).
% 2.76/2.99  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 2.76/2.99      inference('sup-', [status(thm)], ['6', '7'])).
% 2.76/2.99  thf(d10_xboole_0, axiom,
% 2.76/2.99    (![A:$i,B:$i]:
% 2.76/2.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.76/2.99  thf('9', plain,
% 2.76/2.99      (![X0 : $i, X2 : $i]:
% 2.76/2.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.76/2.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.76/2.99  thf('10', plain,
% 2.76/2.99      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 2.76/2.99        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 2.76/2.99      inference('sup-', [status(thm)], ['8', '9'])).
% 2.76/2.99  thf('11', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('12', plain,
% 2.76/2.99      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.76/2.99      inference('sup-', [status(thm)], ['3', '4'])).
% 2.76/2.99  thf('13', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 2.76/2.99      inference('demod', [status(thm)], ['11', '12'])).
% 2.76/2.99  thf('14', plain, (~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))),
% 2.76/2.99      inference('simplify_reflect-', [status(thm)], ['10', '13'])).
% 2.76/2.99  thf('15', plain,
% 2.76/2.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('16', plain,
% 2.76/2.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf(dt_k4_relset_1, axiom,
% 2.76/2.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.76/2.99     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.76/2.99         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.76/2.99       ( m1_subset_1 @
% 2.76/2.99         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.76/2.99         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 2.76/2.99  thf('17', plain,
% 2.76/2.99      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 2.76/2.99         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 2.76/2.99          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 2.76/2.99          | (m1_subset_1 @ (k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20) @ 
% 2.76/2.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X22))))),
% 2.76/2.99      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 2.76/2.99  thf('18', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.76/2.99         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.76/2.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.76/2.99          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 2.76/2.99      inference('sup-', [status(thm)], ['16', '17'])).
% 2.76/2.99  thf('19', plain,
% 2.76/2.99      ((m1_subset_1 @ 
% 2.76/2.99        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 2.76/2.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.76/2.99      inference('sup-', [status(thm)], ['15', '18'])).
% 2.76/2.99  thf('20', plain,
% 2.76/2.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('21', plain,
% 2.76/2.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf(redefinition_k4_relset_1, axiom,
% 2.76/2.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.76/2.99     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.76/2.99         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.76/2.99       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.76/2.99  thf('22', plain,
% 2.76/2.99      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.76/2.99         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.76/2.99          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 2.76/2.99          | ((k4_relset_1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 2.76/2.99              = (k5_relat_1 @ X29 @ X32)))),
% 2.76/2.99      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 2.76/2.99  thf('23', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.76/2.99         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.76/2.99            = (k5_relat_1 @ sk_D @ X0))
% 2.76/2.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.76/2.99      inference('sup-', [status(thm)], ['21', '22'])).
% 2.76/2.99  thf('24', plain,
% 2.76/2.99      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.76/2.99         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.76/2.99      inference('sup-', [status(thm)], ['20', '23'])).
% 2.76/2.99  thf('25', plain,
% 2.76/2.99      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 2.76/2.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.76/2.99      inference('demod', [status(thm)], ['19', '24'])).
% 2.76/2.99  thf('26', plain,
% 2.76/2.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.76/2.99         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 2.76/2.99          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 2.76/2.99      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.76/2.99  thf('27', plain,
% 2.76/2.99      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 2.76/2.99         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 2.76/2.99      inference('sup-', [status(thm)], ['25', '26'])).
% 2.76/2.99  thf('28', plain,
% 2.76/2.99      (((k2_relset_1 @ sk_A @ sk_C @ 
% 2.76/2.99         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('29', plain,
% 2.76/2.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('30', plain,
% 2.76/2.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf(redefinition_k1_partfun1, axiom,
% 2.76/2.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.76/2.99     ( ( ( v1_funct_1 @ E ) & 
% 2.76/2.99         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.76/2.99         ( v1_funct_1 @ F ) & 
% 2.76/2.99         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.76/2.99       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.76/2.99  thf('31', plain,
% 2.76/2.99      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 2.76/2.99         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.76/2.99          | ~ (v1_funct_1 @ X43)
% 2.76/2.99          | ~ (v1_funct_1 @ X46)
% 2.76/2.99          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 2.76/2.99          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 2.76/2.99              = (k5_relat_1 @ X43 @ X46)))),
% 2.76/2.99      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.76/2.99  thf('32', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.76/2.99         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.76/2.99            = (k5_relat_1 @ sk_D @ X0))
% 2.76/2.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.76/2.99          | ~ (v1_funct_1 @ X0)
% 2.76/2.99          | ~ (v1_funct_1 @ sk_D))),
% 2.76/2.99      inference('sup-', [status(thm)], ['30', '31'])).
% 2.76/2.99  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('34', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.76/2.99         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.76/2.99            = (k5_relat_1 @ sk_D @ X0))
% 2.76/2.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.76/2.99          | ~ (v1_funct_1 @ X0))),
% 2.76/2.99      inference('demod', [status(thm)], ['32', '33'])).
% 2.76/2.99  thf('35', plain,
% 2.76/2.99      ((~ (v1_funct_1 @ sk_E)
% 2.76/2.99        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.76/2.99            = (k5_relat_1 @ sk_D @ sk_E)))),
% 2.76/2.99      inference('sup-', [status(thm)], ['29', '34'])).
% 2.76/2.99  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('37', plain,
% 2.76/2.99      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.76/2.99         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.76/2.99      inference('demod', [status(thm)], ['35', '36'])).
% 2.76/2.99  thf('38', plain,
% 2.76/2.99      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.76/2.99      inference('demod', [status(thm)], ['28', '37'])).
% 2.76/2.99  thf('39', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.76/2.99      inference('sup+', [status(thm)], ['27', '38'])).
% 2.76/2.99  thf(t51_funct_1, axiom,
% 2.76/2.99    (![A:$i]:
% 2.76/2.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.76/2.99       ( ![B:$i]:
% 2.76/2.99         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.76/2.99           ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) & 
% 2.76/2.99               ( v2_funct_1 @ A ) ) =>
% 2.76/2.99             ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 2.76/2.99  thf('40', plain,
% 2.76/2.99      (![X12 : $i, X13 : $i]:
% 2.76/2.99         (~ (v1_relat_1 @ X12)
% 2.76/2.99          | ~ (v1_funct_1 @ X12)
% 2.76/2.99          | (r1_tarski @ (k1_relat_1 @ X13) @ (k2_relat_1 @ X12))
% 2.76/2.99          | ((k2_relat_1 @ (k5_relat_1 @ X12 @ X13)) != (k2_relat_1 @ X13))
% 2.76/2.99          | ~ (v2_funct_1 @ X13)
% 2.76/2.99          | ~ (v1_funct_1 @ X13)
% 2.76/2.99          | ~ (v1_relat_1 @ X13))),
% 2.76/2.99      inference('cnf', [status(esa)], [t51_funct_1])).
% 2.76/2.99  thf('41', plain,
% 2.76/2.99      ((((sk_C) != (k2_relat_1 @ sk_E))
% 2.76/2.99        | ~ (v1_relat_1 @ sk_E)
% 2.76/2.99        | ~ (v1_funct_1 @ sk_E)
% 2.76/2.99        | ~ (v2_funct_1 @ sk_E)
% 2.76/2.99        | (r1_tarski @ (k1_relat_1 @ sk_E) @ (k2_relat_1 @ sk_D))
% 2.76/2.99        | ~ (v1_funct_1 @ sk_D)
% 2.76/2.99        | ~ (v1_relat_1 @ sk_D))),
% 2.76/2.99      inference('sup-', [status(thm)], ['39', '40'])).
% 2.76/2.99  thf('42', plain,
% 2.76/2.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf(cc2_relat_1, axiom,
% 2.76/2.99    (![A:$i]:
% 2.76/2.99     ( ( v1_relat_1 @ A ) =>
% 2.76/2.99       ( ![B:$i]:
% 2.76/2.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.76/2.99  thf('43', plain,
% 2.76/2.99      (![X6 : $i, X7 : $i]:
% 2.76/2.99         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 2.76/2.99          | (v1_relat_1 @ X6)
% 2.76/2.99          | ~ (v1_relat_1 @ X7))),
% 2.76/2.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.76/2.99  thf('44', plain,
% 2.76/2.99      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 2.76/2.99      inference('sup-', [status(thm)], ['42', '43'])).
% 2.76/2.99  thf(fc6_relat_1, axiom,
% 2.76/2.99    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.76/2.99  thf('45', plain,
% 2.76/2.99      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 2.76/2.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.76/2.99  thf('46', plain, ((v1_relat_1 @ sk_E)),
% 2.76/2.99      inference('demod', [status(thm)], ['44', '45'])).
% 2.76/2.99  thf('47', plain, ((v1_funct_1 @ sk_E)),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('48', plain, ((v2_funct_1 @ sk_E)),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('49', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf(d1_funct_2, axiom,
% 2.76/2.99    (![A:$i,B:$i,C:$i]:
% 2.76/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.76/2.99       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.76/2.99           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.76/2.99             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.76/2.99         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.76/2.99           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.76/2.99             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.76/2.99  thf(zf_stmt_1, axiom,
% 2.76/2.99    (![C:$i,B:$i,A:$i]:
% 2.76/2.99     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.76/2.99       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.76/2.99  thf('50', plain,
% 2.76/2.99      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.76/2.99         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 2.76/2.99          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 2.76/2.99          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.76/2.99  thf('51', plain,
% 2.76/2.99      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 2.76/2.99        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 2.76/2.99      inference('sup-', [status(thm)], ['49', '50'])).
% 2.76/2.99  thf(zf_stmt_2, axiom,
% 2.76/2.99    (![B:$i,A:$i]:
% 2.76/2.99     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.76/2.99       ( zip_tseitin_0 @ B @ A ) ))).
% 2.76/2.99  thf('52', plain,
% 2.76/2.99      (![X35 : $i, X36 : $i]:
% 2.76/2.99         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.76/2.99  thf('53', plain,
% 2.76/2.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.76/2.99  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.76/2.99  thf(zf_stmt_5, axiom,
% 2.76/2.99    (![A:$i,B:$i,C:$i]:
% 2.76/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.76/2.99       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.76/2.99         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.76/2.99           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.76/2.99             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.76/2.99  thf('54', plain,
% 2.76/2.99      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.76/2.99         (~ (zip_tseitin_0 @ X40 @ X41)
% 2.76/2.99          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 2.76/2.99          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.76/2.99  thf('55', plain,
% 2.76/2.99      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 2.76/2.99      inference('sup-', [status(thm)], ['53', '54'])).
% 2.76/2.99  thf('56', plain,
% 2.76/2.99      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 2.76/2.99      inference('sup-', [status(thm)], ['52', '55'])).
% 2.76/2.99  thf('57', plain, (((sk_C) != (k1_xboole_0))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('58', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 2.76/2.99      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 2.76/2.99  thf('59', plain,
% 2.76/2.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf(redefinition_k1_relset_1, axiom,
% 2.76/2.99    (![A:$i,B:$i,C:$i]:
% 2.76/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.76/2.99       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.76/2.99  thf('60', plain,
% 2.76/2.99      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.76/2.99         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 2.76/2.99          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 2.76/2.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.76/2.99  thf('61', plain,
% 2.76/2.99      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 2.76/2.99      inference('sup-', [status(thm)], ['59', '60'])).
% 2.76/2.99  thf('62', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.76/2.99      inference('demod', [status(thm)], ['51', '58', '61'])).
% 2.76/2.99  thf('63', plain, ((v1_funct_1 @ sk_D)),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('64', plain,
% 2.76/2.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('65', plain,
% 2.76/2.99      (![X6 : $i, X7 : $i]:
% 2.76/2.99         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 2.76/2.99          | (v1_relat_1 @ X6)
% 2.76/2.99          | ~ (v1_relat_1 @ X7))),
% 2.76/2.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.76/2.99  thf('66', plain,
% 2.76/2.99      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 2.76/2.99      inference('sup-', [status(thm)], ['64', '65'])).
% 2.76/2.99  thf('67', plain,
% 2.76/2.99      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 2.76/2.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.76/2.99  thf('68', plain, ((v1_relat_1 @ sk_D)),
% 2.76/2.99      inference('demod', [status(thm)], ['66', '67'])).
% 2.76/2.99  thf('69', plain,
% 2.76/2.99      ((((sk_C) != (k2_relat_1 @ sk_E))
% 2.76/2.99        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 2.76/2.99      inference('demod', [status(thm)],
% 2.76/2.99                ['41', '46', '47', '48', '62', '63', '68'])).
% 2.76/2.99  thf('70', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.76/2.99      inference('sup+', [status(thm)], ['27', '38'])).
% 2.76/2.99  thf(t45_relat_1, axiom,
% 2.76/2.99    (![A:$i]:
% 2.76/2.99     ( ( v1_relat_1 @ A ) =>
% 2.76/2.99       ( ![B:$i]:
% 2.76/2.99         ( ( v1_relat_1 @ B ) =>
% 2.76/2.99           ( r1_tarski @
% 2.76/2.99             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 2.76/2.99  thf('71', plain,
% 2.76/2.99      (![X10 : $i, X11 : $i]:
% 2.76/2.99         (~ (v1_relat_1 @ X10)
% 2.76/2.99          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 2.76/2.99             (k2_relat_1 @ X10))
% 2.76/2.99          | ~ (v1_relat_1 @ X11))),
% 2.76/2.99      inference('cnf', [status(esa)], [t45_relat_1])).
% 2.76/2.99  thf('72', plain,
% 2.76/2.99      (![X0 : $i, X2 : $i]:
% 2.76/2.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.76/2.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.76/2.99  thf('73', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i]:
% 2.76/2.99         (~ (v1_relat_1 @ X1)
% 2.76/2.99          | ~ (v1_relat_1 @ X0)
% 2.76/2.99          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 2.76/2.99               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 2.76/2.99          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 2.76/2.99      inference('sup-', [status(thm)], ['71', '72'])).
% 2.76/2.99  thf('74', plain,
% 2.76/2.99      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)
% 2.76/2.99        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 2.76/2.99        | ~ (v1_relat_1 @ sk_E)
% 2.76/2.99        | ~ (v1_relat_1 @ sk_D))),
% 2.76/2.99      inference('sup-', [status(thm)], ['70', '73'])).
% 2.76/2.99  thf('75', plain,
% 2.76/2.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('76', plain,
% 2.76/2.99      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.76/2.99         ((m1_subset_1 @ (k2_relset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 2.76/2.99          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.76/2.99      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 2.76/2.99  thf('77', plain,
% 2.76/2.99      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_C @ sk_E) @ (k1_zfmisc_1 @ sk_C))),
% 2.76/2.99      inference('sup-', [status(thm)], ['75', '76'])).
% 2.76/2.99  thf('78', plain,
% 2.76/2.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('79', plain,
% 2.76/2.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.76/2.99         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 2.76/2.99          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 2.76/2.99      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.76/2.99  thf('80', plain,
% 2.76/2.99      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 2.76/2.99      inference('sup-', [status(thm)], ['78', '79'])).
% 2.76/2.99  thf('81', plain,
% 2.76/2.99      ((m1_subset_1 @ (k2_relat_1 @ sk_E) @ (k1_zfmisc_1 @ sk_C))),
% 2.76/2.99      inference('demod', [status(thm)], ['77', '80'])).
% 2.76/2.99  thf('82', plain,
% 2.76/2.99      (![X3 : $i, X4 : $i]:
% 2.76/2.99         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 2.76/2.99      inference('cnf', [status(esa)], [t3_subset])).
% 2.76/2.99  thf('83', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 2.76/2.99      inference('sup-', [status(thm)], ['81', '82'])).
% 2.76/2.99  thf('84', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.76/2.99      inference('sup+', [status(thm)], ['27', '38'])).
% 2.76/2.99  thf('85', plain, ((v1_relat_1 @ sk_E)),
% 2.76/2.99      inference('demod', [status(thm)], ['44', '45'])).
% 2.76/2.99  thf('86', plain, ((v1_relat_1 @ sk_D)),
% 2.76/2.99      inference('demod', [status(thm)], ['66', '67'])).
% 2.76/2.99  thf('87', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 2.76/2.99      inference('demod', [status(thm)], ['74', '83', '84', '85', '86'])).
% 2.76/2.99  thf('88', plain,
% 2.76/2.99      ((((sk_C) != (sk_C)) | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 2.76/2.99      inference('demod', [status(thm)], ['69', '87'])).
% 2.76/2.99  thf('89', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))),
% 2.76/2.99      inference('simplify', [status(thm)], ['88'])).
% 2.76/2.99  thf('90', plain, ($false), inference('demod', [status(thm)], ['14', '89'])).
% 2.76/2.99  
% 2.76/2.99  % SZS output end Refutation
% 2.76/2.99  
% 2.76/3.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
