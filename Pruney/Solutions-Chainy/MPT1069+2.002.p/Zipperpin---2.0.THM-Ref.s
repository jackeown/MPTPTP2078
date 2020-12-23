%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.buEh2kkH45

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 301 expanded)
%              Number of leaves         :   49 ( 109 expanded)
%              Depth                    :   31
%              Number of atoms          : 1626 (6798 expanded)
%              Number of equality atoms :  103 ( 298 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t186_funct_2,conjecture,(
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
                        = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
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
                          = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t186_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc6_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ~ ( v1_xboole_0 @ C )
              & ( v1_funct_2 @ C @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc6_funct_2])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_relat_1 @ E )
            & ( v1_funct_1 @ E ) )
         => ( ( r2_hidden @ C @ A )
           => ( ( B = k1_xboole_0 )
              | ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C )
                = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ~ ( v1_funct_1 @ X38 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X39 @ X38 ) @ X40 )
        = ( k1_funct_1 @ X38 @ ( k1_funct_1 @ X39 @ X40 ) ) )
      | ( X41 = k1_xboole_0 )
      | ~ ( r2_hidden @ X40 @ X42 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_2])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( sk_C = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( sk_C = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('22',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
            & ( v1_funct_2 @ D @ A @ C )
            & ( v1_funct_1 @ D ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ A )
     => ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ A ) ) ) ) )).

thf('28',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( zip_tseitin_1 @ X52 @ X53 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X53 @ X52 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) )
      | ( zip_tseitin_0 @ X54 @ X55 @ X53 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X53 @ X52 @ X54 ) @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ X0 )
      | ( zip_tseitin_0 @ sk_D @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( v1_funct_1 @ sk_D )
      | ( zip_tseitin_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ X0 )
      | ( zip_tseitin_0 @ sk_D @ X0 @ sk_B )
      | ( zip_tseitin_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ ( k1_relat_1 @ sk_E ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( v1_funct_2 @ X47 @ X49 @ X48 )
      | ~ ( zip_tseitin_0 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ ( k1_relat_1 @ sk_E ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('37',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ~ ( zip_tseitin_0 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('38',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('39',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X43 @ X44 )
      | ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X46 @ X43 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( zip_tseitin_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( zip_tseitin_1 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['21','44'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('46',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( ( k7_partfun1 @ X31 @ X30 @ X29 )
        = ( k1_funct_1 @ X30 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v5_relat_1 @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('49',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('50',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['47','50','51'])).

thf('53',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','52'])).

thf('54',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) )
           => ( ( B = k1_xboole_0 )
              | ( ( k8_funct_2 @ A @ B @ C @ D @ E )
                = ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k8_funct_2 @ X27 @ X25 @ X26 @ X28 @ X24 )
        = ( k1_partfun1 @ X27 @ X25 @ X25 @ X26 @ X28 @ X24 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X27 @ X25 @ X28 ) @ ( k1_relset_1 @ X25 @ X26 @ X24 ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X25 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('59',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('64',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','70','71','72','73'])).

thf('75',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','76'])).

thf('78',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['48','49'])).

thf('81',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('84',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('86',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('87',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('91',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('92',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ k1_xboole_0 ) )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('94',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('95',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['94'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('96',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('97',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['93','95','96'])).

thf('98',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('99',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('101',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('105',plain,(
    sk_D = k1_xboole_0 ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('107',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['7','105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('109',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['109','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.buEh2kkH45
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 134 iterations in 0.092s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.55  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(t186_funct_2, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.55       ( ![D:$i]:
% 0.20/0.55         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.55             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.55           ( ![E:$i]:
% 0.20/0.55             ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.20/0.55               ( ![F:$i]:
% 0.20/0.55                 ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.55                   ( ( r1_tarski @
% 0.20/0.55                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.20/0.55                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.20/0.55                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.20/0.55                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.55        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.55          ( ![D:$i]:
% 0.20/0.55            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.55                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.55              ( ![E:$i]:
% 0.20/0.55                ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55                    ( m1_subset_1 @
% 0.20/0.55                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.20/0.55                  ( ![F:$i]:
% 0.20/0.55                    ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.55                      ( ( r1_tarski @
% 0.20/0.55                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.20/0.55                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.20/0.55                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55                          ( ( k1_funct_1 @
% 0.20/0.55                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.20/0.55                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc6_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.20/0.55       ( ![C:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.20/0.55             ( ( v1_funct_1 @ C ) & ( ~( v1_xboole_0 @ C ) ) & 
% 0.20/0.55               ( v1_funct_2 @ C @ A @ B ) ) ) ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X21)
% 0.20/0.55          | (v1_xboole_0 @ X22)
% 0.20/0.55          | ~ (v1_funct_1 @ X23)
% 0.20/0.55          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.20/0.55          | ~ (v1_xboole_0 @ X23)
% 0.20/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc6_funct_2])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      ((~ (v1_xboole_0 @ sk_D)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.55        | (v1_xboole_0 @ sk_C)
% 0.20/0.55        | (v1_xboole_0 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf('3', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.20/0.55  thf('6', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('7', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_D))),
% 0.20/0.55      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf('8', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t2_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i]:
% 0.20/0.55         ((r2_hidden @ X6 @ X7)
% 0.20/0.55          | (v1_xboole_0 @ X7)
% 0.20/0.55          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.55  thf('10', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t21_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55       ( ![E:$i]:
% 0.20/0.55         ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.20/0.55           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.55             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55               ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 0.20/0.55                 ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X38)
% 0.20/0.55          | ~ (v1_funct_1 @ X38)
% 0.20/0.55          | ((k1_funct_1 @ (k5_relat_1 @ X39 @ X38) @ X40)
% 0.20/0.55              = (k1_funct_1 @ X38 @ (k1_funct_1 @ X39 @ X40)))
% 0.20/0.55          | ((X41) = (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ X40 @ X42)
% 0.20/0.55          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.20/0.55          | ~ (v1_funct_2 @ X39 @ X42 @ X41)
% 0.20/0.55          | ~ (v1_funct_1 @ X39))),
% 0.20/0.55      inference('cnf', [status(esa)], [t21_funct_2])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ sk_D)
% 0.20/0.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.20/0.55          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.55          | ((sk_C) = (k1_xboole_0))
% 0.20/0.55          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.20/0.55              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.20/0.55          | ~ (v1_funct_1 @ X1)
% 0.20/0.55          | ~ (v1_relat_1 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.55  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('15', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.55          | ((sk_C) = (k1_xboole_0))
% 0.20/0.55          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.20/0.55              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.20/0.55          | ~ (v1_funct_1 @ X1)
% 0.20/0.55          | ~ (v1_relat_1 @ X1))),
% 0.20/0.55      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ sk_B)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 0.20/0.55              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.20/0.55          | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '16'])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc2_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.55         ((v5_relat_1 @ X12 @ X14)
% 0.20/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.55  thf('20', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf('21', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.55        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.55         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.20/0.55          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.20/0.55      inference('demod', [status(thm)], ['22', '25'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t8_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.55         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.20/0.55       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.20/0.55         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.20/0.55             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.20/0.55           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_2, axiom,
% 0.20/0.55    (![B:$i,A:$i]:
% 0.20/0.55     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.20/0.55       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_4, axiom,
% 0.20/0.55    (![D:$i,C:$i,A:$i]:
% 0.20/0.55     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 0.20/0.55       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.20/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_5, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.20/0.55         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.20/0.55         ((zip_tseitin_1 @ X52 @ X53)
% 0.20/0.55          | ~ (v1_funct_1 @ X54)
% 0.20/0.55          | ~ (v1_funct_2 @ X54 @ X53 @ X52)
% 0.20/0.55          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52)))
% 0.20/0.55          | (zip_tseitin_0 @ X54 @ X55 @ X53)
% 0.20/0.55          | ~ (r1_tarski @ (k2_relset_1 @ X53 @ X52 @ X54) @ X55))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55          | (zip_tseitin_0 @ sk_D @ X0 @ sk_B)
% 0.20/0.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.20/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.55          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.55  thf('30', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55          | (zip_tseitin_0 @ sk_D @ X0 @ sk_B)
% 0.20/0.55          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55        | (zip_tseitin_0 @ sk_D @ (k1_relat_1 @ sk_E) @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '32'])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.20/0.55         ((v1_funct_2 @ X47 @ X49 @ X48) | ~ (zip_tseitin_0 @ X47 @ X48 @ X49))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55        | (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55        | (zip_tseitin_0 @ sk_D @ (k1_relat_1 @ sk_E) @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '32'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.20/0.55         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 0.20/0.55          | ~ (zip_tseitin_0 @ X47 @ X48 @ X49))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55        | (m1_subset_1 @ sk_D @ 
% 0.20/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.55  thf(t7_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X43 @ X44)
% 0.20/0.55          | ((X45) = (k1_xboole_0))
% 0.20/0.55          | ~ (v1_funct_1 @ X46)
% 0.20/0.55          | ~ (v1_funct_2 @ X46 @ X44 @ X45)
% 0.20/0.55          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.20/0.55          | (r2_hidden @ (k1_funct_1 @ X46 @ X43) @ X45))),
% 0.20/0.55      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.20/0.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))
% 0.20/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.55          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.55  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.20/0.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))
% 0.20/0.55          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.55          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.55          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.20/0.55          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['35', '42'])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.20/0.55          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.55          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.20/0.55      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      (((v1_xboole_0 @ sk_B)
% 0.20/0.55        | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.55        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['21', '44'])).
% 0.20/0.55  thf(d8_partfun1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.55       ( ![C:$i]:
% 0.20/0.55         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.55           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X29 @ (k1_relat_1 @ X30))
% 0.20/0.55          | ((k7_partfun1 @ X31 @ X30 @ X29) = (k1_funct_1 @ X30 @ X29))
% 0.20/0.55          | ~ (v1_funct_1 @ X30)
% 0.20/0.55          | ~ (v5_relat_1 @ X30 @ X31)
% 0.20/0.55          | ~ (v1_relat_1 @ X30))),
% 0.20/0.55      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.55          | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | ~ (v1_relat_1 @ sk_E)
% 0.20/0.55          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.55          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.20/0.55              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc1_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( v1_relat_1 @ C ) ))).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.55         ((v1_relat_1 @ X9)
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.55  thf('50', plain, ((v1_relat_1 @ sk_E)),
% 0.20/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('51', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.55          | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.20/0.55          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.20/0.55              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '50', '51'])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.20/0.55          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['20', '52'])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.20/0.55      inference('demod', [status(thm)], ['22', '25'])).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d12_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55       ( ![E:$i]:
% 0.20/0.55         ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.55           ( ( r1_tarski @
% 0.20/0.55               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 0.20/0.55             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 0.20/0.55                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ X24)
% 0.20/0.55          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.20/0.55          | ((k8_funct_2 @ X27 @ X25 @ X26 @ X28 @ X24)
% 0.20/0.55              = (k1_partfun1 @ X27 @ X25 @ X25 @ X26 @ X28 @ X24))
% 0.20/0.55          | ~ (r1_tarski @ (k2_relset_1 @ X27 @ X25 @ X28) @ 
% 0.20/0.55               (k1_relset_1 @ X25 @ X26 @ X24))
% 0.20/0.55          | ((X25) = (k1_xboole_0))
% 0.20/0.55          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X25)))
% 0.20/0.55          | ~ (v1_funct_2 @ X28 @ X27 @ X25)
% 0.20/0.55          | ~ (v1_funct_1 @ X28))),
% 0.20/0.55      inference('cnf', [status(esa)], [d12_funct_2])).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.20/0.55          | ((sk_C) = (k1_xboole_0))
% 0.20/0.55          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 0.20/0.55               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 0.20/0.55          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 0.20/0.55              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E))
% 0.20/0.55          | ~ (v1_funct_1 @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('59', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.20/0.55          | ((sk_C) = (k1_xboole_0))
% 0.20/0.55          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ (k1_relat_1 @ sk_E))
% 0.20/0.55          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 0.20/0.55              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E)))),
% 0.20/0.55      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.20/0.55          = (k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 0.20/0.55        | ((sk_C) = (k1_xboole_0))
% 0.20/0.55        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 0.20/0.55        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['54', '60'])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k1_partfun1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.55         ( v1_funct_1 @ F ) & 
% 0.20/0.55         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.20/0.55       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.20/0.55          | ~ (v1_funct_1 @ X32)
% 0.20/0.55          | ~ (v1_funct_1 @ X35)
% 0.20/0.55          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.20/0.55          | ((k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 0.20/0.55              = (k5_relat_1 @ X32 @ X35)))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 0.20/0.55            = (k5_relat_1 @ sk_D @ X0))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.55  thf('66', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 0.20/0.55            = (k5_relat_1 @ sk_D @ X0))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.20/0.55          | ~ (v1_funct_1 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      ((~ (v1_funct_1 @ sk_E)
% 0.20/0.55        | ((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.20/0.55            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['62', '67'])).
% 0.20/0.55  thf('69', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      (((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.20/0.55         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.20/0.55      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('72', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('74', plain,
% 0.20/0.55      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.20/0.55          = (k5_relat_1 @ sk_D @ sk_E))
% 0.20/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['61', '70', '71', '72', '73'])).
% 0.20/0.55  thf('75', plain,
% 0.20/0.55      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.20/0.55         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.20/0.55          != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.20/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.55  thf('77', plain,
% 0.20/0.55      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.20/0.55          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.20/0.55        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.55        | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['53', '76'])).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.20/0.55          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.20/0.55        | ((sk_C) = (k1_xboole_0))
% 0.20/0.55        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.55        | ~ (v1_relat_1 @ sk_E)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | ((sk_C) = (k1_xboole_0))
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '77'])).
% 0.20/0.55  thf('79', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('80', plain, ((v1_relat_1 @ sk_E)),
% 0.20/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('81', plain,
% 0.20/0.55      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.20/0.55          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.20/0.55        | ((sk_C) = (k1_xboole_0))
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | ((sk_C) = (k1_xboole_0))
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.20/0.55  thf('82', plain,
% 0.20/0.55      ((((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.55        | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['81'])).
% 0.20/0.55  thf('83', plain,
% 0.20/0.55      (![X50 : $i, X51 : $i]:
% 0.20/0.55         (((X50) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X50 @ X51))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.55  thf('84', plain,
% 0.20/0.55      ((((sk_C) = (k1_xboole_0))
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.55  thf('85', plain,
% 0.20/0.55      ((((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['84'])).
% 0.20/0.55  thf(l13_xboole_0, axiom,
% 0.20/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.55  thf('86', plain,
% 0.20/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.55  thf('87', plain,
% 0.20/0.55      ((((sk_C) = (k1_xboole_0))
% 0.20/0.55        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['85', '86'])).
% 0.20/0.55  thf('88', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('89', plain,
% 0.20/0.55      ((((sk_C) = (k1_xboole_0)) | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 0.20/0.55  thf('90', plain,
% 0.20/0.55      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55        | (m1_subset_1 @ sk_D @ 
% 0.20/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.55  thf(cc1_subset_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.20/0.55  thf('91', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.20/0.55          | (v1_xboole_0 @ X4)
% 0.20/0.55          | ~ (v1_xboole_0 @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.55  thf('92', plain,
% 0.20/0.55      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.55        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E)))
% 0.20/0.55        | (v1_xboole_0 @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['90', '91'])).
% 0.20/0.55  thf('93', plain,
% 0.20/0.55      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ k1_xboole_0))
% 0.20/0.55        | ((sk_C) = (k1_xboole_0))
% 0.20/0.55        | (v1_xboole_0 @ sk_D)
% 0.20/0.55        | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['89', '92'])).
% 0.20/0.55  thf(t113_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.55  thf('94', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i]:
% 0.20/0.55         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.55  thf('95', plain,
% 0.20/0.55      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['94'])).
% 0.20/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.55  thf('96', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.55  thf('97', plain,
% 0.20/0.55      ((((sk_C) = (k1_xboole_0))
% 0.20/0.55        | (v1_xboole_0 @ sk_D)
% 0.20/0.55        | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['93', '95', '96'])).
% 0.20/0.55  thf('98', plain,
% 0.20/0.55      (![X50 : $i, X51 : $i]:
% 0.20/0.55         (((X50) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X50 @ X51))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.55  thf('99', plain, (((v1_xboole_0 @ sk_D) | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.55      inference('clc', [status(thm)], ['97', '98'])).
% 0.20/0.55  thf('100', plain,
% 0.20/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.55  thf('101', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['99', '100'])).
% 0.20/0.55  thf('102', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('103', plain,
% 0.20/0.55      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.55  thf('104', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.55  thf('105', plain, (((sk_D) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['103', '104'])).
% 0.20/0.55  thf('106', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.55  thf('107', plain, ((v1_xboole_0 @ sk_B)),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '105', '106'])).
% 0.20/0.55  thf('108', plain,
% 0.20/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.55  thf('109', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['107', '108'])).
% 0.20/0.55  thf('110', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('111', plain, ($false),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['109', '110'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
