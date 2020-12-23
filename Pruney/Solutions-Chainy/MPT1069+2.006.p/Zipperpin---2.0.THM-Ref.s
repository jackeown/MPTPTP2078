%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j0P3hZ18gG

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 261 expanded)
%              Number of leaves         :   45 (  96 expanded)
%              Depth                    :   28
%              Number of atoms          : 1360 (5763 expanded)
%              Number of equality atoms :   75 ( 242 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( zip_tseitin_1 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ( zip_tseitin_0 @ X41 @ X42 @ X40 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X40 @ X39 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ X0 )
      | ( zip_tseitin_0 @ sk_D @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( v1_funct_1 @ sk_D )
      | ( zip_tseitin_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ X0 )
      | ( zip_tseitin_0 @ sk_D @ X0 @ sk_B )
      | ( zip_tseitin_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ ( k1_relat_1 @ sk_E ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_funct_2 @ X34 @ X36 @ X35 )
      | ~ ( zip_tseitin_0 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ ( k1_relat_1 @ sk_E ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('29',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( zip_tseitin_0 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('30',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('31',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( X32 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X33 @ X30 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( zip_tseitin_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( zip_tseitin_1 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['13','36'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( ( k7_partfun1 @ X23 @ X22 @ X21 )
        = ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v5_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('39',plain,(
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
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('42',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['39','42','43'])).

thf('45',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','44'])).

thf('46',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('50',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ X25 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X25 @ X26 @ X29 @ X24 @ X28 ) @ X27 )
        = ( k1_funct_1 @ X28 @ ( k1_funct_1 @ X24 @ X27 ) ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X25 @ X26 @ X24 ) @ ( k1_relset_1 @ X26 @ X29 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['47','63'])).

thf('65',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['46','64'])).

thf('66',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('69',plain,
    ( ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('75',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('76',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ k1_xboole_0 ) )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('79',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['77','79','80'])).

thf('82',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('85',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('89',plain,(
    sk_D = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['7','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('93',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j0P3hZ18gG
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:35:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 97 iterations in 0.052s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.51  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(t186_funct_2, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.51       ( ![D:$i]:
% 0.21/0.51         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.51             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.51           ( ![E:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.51                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.21/0.51               ( ![F:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.51                   ( ( r1_tarski @
% 0.21/0.51                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.21/0.51                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.21/0.51                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.51                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.21/0.51                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.51          ( ![D:$i]:
% 0.21/0.51            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.51                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.51              ( ![E:$i]:
% 0.21/0.51                ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.51                    ( m1_subset_1 @
% 0.21/0.51                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.21/0.51                  ( ![F:$i]:
% 0.21/0.51                    ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.51                      ( ( r1_tarski @
% 0.21/0.51                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.21/0.51                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.21/0.51                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.51                          ( ( k1_funct_1 @
% 0.21/0.51                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.21/0.51                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc6_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.51             ( ( v1_funct_1 @ C ) & ( ~( v1_xboole_0 @ C ) ) & 
% 0.21/0.51               ( v1_funct_2 @ C @ A @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X18)
% 0.21/0.51          | (v1_xboole_0 @ X19)
% 0.21/0.51          | ~ (v1_funct_1 @ X20)
% 0.21/0.51          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.21/0.51          | ~ (v1_xboole_0 @ X20)
% 0.21/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc6_funct_2])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((~ (v1_xboole_0 @ sk_D)
% 0.21/0.51        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_D)
% 0.21/0.51        | (v1_xboole_0 @ sk_C)
% 0.21/0.51        | (v1_xboole_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf('3', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.51  thf('6', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.51         ((v5_relat_1 @ X12 @ X14)
% 0.21/0.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.51  thf('10', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf('11', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t2_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         ((r2_hidden @ X6 @ X7)
% 0.21/0.51          | (v1_xboole_0 @ X7)
% 0.21/0.51          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.51  thf('13', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.51        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.51         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.21/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t8_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.51         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.21/0.51       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.21/0.51         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.21/0.51             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.21/0.51           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.21/0.51  thf(zf_stmt_2, axiom,
% 0.21/0.51    (![B:$i,A:$i]:
% 0.21/0.51     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.21/0.51       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.21/0.51  thf(zf_stmt_4, axiom,
% 0.21/0.51    (![D:$i,C:$i,A:$i]:
% 0.21/0.51     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 0.21/0.51       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.21/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_5, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.21/0.51         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.51         ((zip_tseitin_1 @ X39 @ X40)
% 0.21/0.51          | ~ (v1_funct_1 @ X41)
% 0.21/0.51          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 0.21/0.51          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.21/0.51          | (zip_tseitin_0 @ X41 @ X42 @ X40)
% 0.21/0.51          | ~ (r1_tarski @ (k2_relset_1 @ X40 @ X39 @ X41) @ X42))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ X0)
% 0.21/0.51          | (zip_tseitin_0 @ sk_D @ X0 @ sk_B)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.51          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ X0)
% 0.21/0.51          | (zip_tseitin_0 @ sk_D @ X0 @ sk_B)
% 0.21/0.51          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.21/0.51        | (zip_tseitin_0 @ sk_D @ (k1_relat_1 @ sk_E) @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['18', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.51         ((v1_funct_2 @ X34 @ X36 @ X35) | ~ (zip_tseitin_0 @ X34 @ X35 @ X36))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.21/0.51        | (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.21/0.51        | (zip_tseitin_0 @ sk_D @ (k1_relat_1 @ sk_E) @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['18', '24'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.51         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.21/0.51          | ~ (zip_tseitin_0 @ X34 @ X35 @ X36))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.21/0.51        | (m1_subset_1 @ sk_D @ 
% 0.21/0.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf(t7_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.51           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X30 @ X31)
% 0.21/0.51          | ((X32) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_funct_1 @ X33)
% 0.21/0.51          | ~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.21/0.51          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.21/0.51          | (r2_hidden @ (k1_funct_1 @ X33 @ X30) @ X32))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((zip_tseitin_1 @ sk_C @ sk_B)
% 0.21/0.51          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))
% 0.21/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.51          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((zip_tseitin_1 @ sk_C @ sk_B)
% 0.21/0.51          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))
% 0.21/0.51          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((zip_tseitin_1 @ sk_C @ sk_B)
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.51          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.51          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.21/0.51          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.21/0.51          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.51          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_B)
% 0.21/0.51        | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.21/0.51        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.51        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '36'])).
% 0.21/0.51  thf(d8_partfun1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.51           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X21 @ (k1_relat_1 @ X22))
% 0.21/0.51          | ((k7_partfun1 @ X23 @ X22 @ X21) = (k1_funct_1 @ X22 @ X21))
% 0.21/0.51          | ~ (v1_funct_1 @ X22)
% 0.21/0.51          | ~ (v5_relat_1 @ X22 @ X23)
% 0.21/0.51          | ~ (v1_relat_1 @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.51          | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.21/0.51          | (v1_xboole_0 @ sk_B)
% 0.21/0.51          | ~ (v1_relat_1 @ sk_E)
% 0.21/0.51          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.51          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.51              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc1_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( v1_relat_1 @ C ) ))).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.51         ((v1_relat_1 @ X9)
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.51  thf('42', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.51          | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.21/0.51          | (v1_xboole_0 @ sk_B)
% 0.21/0.51          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.21/0.51          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.51              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.21/0.51      inference('demod', [status(thm)], ['39', '42', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.51          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.21/0.51        | (v1_xboole_0 @ sk_B)
% 0.21/0.51        | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.21/0.51        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.21/0.51         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('47', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t185_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.51       ( ![D:$i]:
% 0.21/0.51         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.51             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.51           ( ![E:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.51                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.21/0.51               ( ![F:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.51                   ( ( r1_tarski @
% 0.21/0.51                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.21/0.51                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.21/0.51                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.51                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.21/0.51                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X24)
% 0.21/0.51          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.21/0.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.21/0.51          | ~ (m1_subset_1 @ X27 @ X25)
% 0.21/0.51          | ((k1_funct_1 @ (k8_funct_2 @ X25 @ X26 @ X29 @ X24 @ X28) @ X27)
% 0.21/0.51              = (k1_funct_1 @ X28 @ (k1_funct_1 @ X24 @ X27)))
% 0.21/0.51          | ((X25) = (k1_xboole_0))
% 0.21/0.51          | ~ (r1_tarski @ (k2_relset_1 @ X25 @ X26 @ X24) @ 
% 0.21/0.51               (k1_relset_1 @ X26 @ X29 @ X28))
% 0.21/0.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X29)))
% 0.21/0.51          | ~ (v1_funct_1 @ X28)
% 0.21/0.51          | (v1_xboole_0 @ X26))),
% 0.21/0.51      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ sk_C)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.21/0.51          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.51               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.21/0.51          | ((sk_B) = (k1_xboole_0))
% 0.21/0.51          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.21/0.51              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('53', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ sk_C)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.21/0.51          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.51               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.21/0.51          | ((sk_B) = (k1_xboole_0))
% 0.21/0.51          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.21/0.51              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.21/0.51  thf('55', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ sk_C)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.21/0.51          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.51               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.21/0.51          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.21/0.51              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.51             (k1_relat_1 @ sk_E))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.51          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.21/0.51              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.51          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 0.21/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.51          | (v1_xboole_0 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['48', '56'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '17'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('60', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.51          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.21/0.51              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.51          | (v1_xboole_0 @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.21/0.51  thf('62', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.21/0.51            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['61', '62'])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.21/0.51         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['47', '63'])).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.51         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.51      inference('demod', [status(thm)], ['46', '64'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.51          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.21/0.51        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.51        | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.21/0.51        | (v1_xboole_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['45', '65'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_B)
% 0.21/0.51        | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.21/0.51        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (![X37 : $i, X38 : $i]:
% 0.21/0.51         (((X37) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X37 @ X38))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      ((((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.51        | (v1_xboole_0 @ sk_B)
% 0.21/0.51        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.51  thf(l13_xboole_0, axiom,
% 0.21/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      ((((sk_C) = (k1_xboole_0))
% 0.21/0.51        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.51  thf('72', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      ((((sk_C) = (k1_xboole_0)) | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.21/0.51        | (m1_subset_1 @ sk_D @ 
% 0.21/0.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf(cc1_subset_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.21/0.51          | (v1_xboole_0 @ X4)
% 0.21/0.51          | ~ (v1_xboole_0 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.21/0.51        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E)))
% 0.21/0.51        | (v1_xboole_0 @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ k1_xboole_0))
% 0.21/0.51        | ((sk_C) = (k1_xboole_0))
% 0.21/0.51        | (v1_xboole_0 @ sk_D)
% 0.21/0.51        | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['73', '76'])).
% 0.21/0.51  thf(t113_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]:
% 0.21/0.51         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['78'])).
% 0.21/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.51  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.51  thf('81', plain,
% 0.21/0.51      ((((sk_C) = (k1_xboole_0))
% 0.21/0.51        | (v1_xboole_0 @ sk_D)
% 0.21/0.51        | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['77', '79', '80'])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      (![X37 : $i, X38 : $i]:
% 0.21/0.51         (((X37) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X37 @ X38))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.51  thf('83', plain, (((v1_xboole_0 @ sk_D) | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.51      inference('clc', [status(thm)], ['81', '82'])).
% 0.21/0.51  thf('84', plain,
% 0.21/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.51  thf('85', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.51  thf('86', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('87', plain,
% 0.21/0.51      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_D) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.51  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.51  thf('89', plain, (((sk_D) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['87', '88'])).
% 0.21/0.51  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.51  thf('91', plain, ((v1_xboole_0 @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '89', '90'])).
% 0.21/0.51  thf('92', plain,
% 0.21/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.51  thf('93', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.51  thf('94', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('95', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
