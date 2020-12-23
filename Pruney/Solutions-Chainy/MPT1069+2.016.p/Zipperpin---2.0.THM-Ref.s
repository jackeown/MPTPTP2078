%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PAHt678RyR

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 264 expanded)
%              Number of leaves         :   46 (  97 expanded)
%              Depth                    :   28
%              Number of atoms          : 1374 (5777 expanded)
%              Number of equality atoms :   75 ( 242 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( zip_tseitin_1 @ X40 @ X41 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ( zip_tseitin_0 @ X42 @ X43 @ X41 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X41 @ X40 @ X42 ) @ X43 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v1_funct_2 @ X35 @ X37 @ X36 )
      | ~ ( zip_tseitin_0 @ X35 @ X36 @ X37 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( zip_tseitin_0 @ X35 @ X36 @ X37 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ( X33 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X34 @ X31 ) @ X33 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( ( k7_partfun1 @ X24 @ X23 @ X22 )
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['39','44','45'])).

thf('47',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','46'])).

thf('48',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ X26 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X26 @ X27 @ X30 @ X25 @ X29 ) @ X28 )
        = ( k1_funct_1 @ X29 @ ( k1_funct_1 @ X25 @ X28 ) ) )
      | ( X26 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X26 @ X27 @ X25 ) @ ( k1_relset_1 @ X27 @ X30 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('53',plain,(
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
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['49','65'])).

thf('67',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['48','66'])).

thf('68',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X38 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('71',plain,
    ( ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('72',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('73',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('77',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('78',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ k1_xboole_0 ) )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('81',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['79','81','82'])).

thf('84',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X38 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('85',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('87',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,(
    sk_D = k1_xboole_0 ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('93',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['7','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('95',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PAHt678RyR
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 98 iterations in 0.042s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.20/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.49  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(t186_funct_2, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.49       ( ![D:$i]:
% 0.20/0.49         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.49             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.49           ( ![E:$i]:
% 0.20/0.49             ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.49                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.20/0.49               ( ![F:$i]:
% 0.20/0.49                 ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.49                   ( ( r1_tarski @
% 0.20/0.49                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.20/0.49                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.20/0.49                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.49                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.20/0.49                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.49          ( ![D:$i]:
% 0.20/0.49            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.49                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.49              ( ![E:$i]:
% 0.20/0.49                ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.49                    ( m1_subset_1 @
% 0.20/0.49                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.20/0.49                  ( ![F:$i]:
% 0.20/0.49                    ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.49                      ( ( r1_tarski @
% 0.20/0.49                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.20/0.49                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.20/0.49                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.49                          ( ( k1_funct_1 @
% 0.20/0.49                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.20/0.49                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc6_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.20/0.49             ( ( v1_funct_1 @ C ) & ( ~( v1_xboole_0 @ C ) ) & 
% 0.20/0.49               ( v1_funct_2 @ C @ A @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X19)
% 0.20/0.49          | (v1_xboole_0 @ X20)
% 0.20/0.49          | ~ (v1_funct_1 @ X21)
% 0.20/0.49          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.20/0.49          | ~ (v1_xboole_0 @ X21)
% 0.20/0.49          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc6_funct_2])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((~ (v1_xboole_0 @ sk_D)
% 0.20/0.49        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.49        | (v1_xboole_0 @ sk_C)
% 0.20/0.49        | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf('3', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.20/0.49  thf('6', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_D))),
% 0.20/0.49      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         ((v5_relat_1 @ X13 @ X15)
% 0.20/0.49          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.49  thf('10', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t2_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.49       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         ((r2_hidden @ X6 @ X7)
% 0.20/0.49          | (v1_xboole_0 @ X7)
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.49  thf('13', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.49        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.49         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.20/0.49          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t8_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.49         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.20/0.49       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.20/0.49         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.20/0.49             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.20/0.49           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_2, axiom,
% 0.20/0.49    (![B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.20/0.49       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_4, axiom,
% 0.20/0.49    (![D:$i,C:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 0.20/0.49       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.20/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_5, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.20/0.49         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.49         ((zip_tseitin_1 @ X40 @ X41)
% 0.20/0.49          | ~ (v1_funct_1 @ X42)
% 0.20/0.49          | ~ (v1_funct_2 @ X42 @ X41 @ X40)
% 0.20/0.49          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.20/0.49          | (zip_tseitin_0 @ X42 @ X43 @ X41)
% 0.20/0.49          | ~ (r1_tarski @ (k2_relset_1 @ X41 @ X40 @ X42) @ X43))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.49          | (zip_tseitin_0 @ sk_D @ X0 @ sk_B)
% 0.20/0.49          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.49          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.49          | (zip_tseitin_0 @ sk_D @ X0 @ sk_B)
% 0.20/0.49          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.49        | (zip_tseitin_0 @ sk_D @ (k1_relat_1 @ sk_E) @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.49         ((v1_funct_2 @ X35 @ X37 @ X36) | ~ (zip_tseitin_0 @ X35 @ X36 @ X37))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.49        | (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.49        | (zip_tseitin_0 @ sk_D @ (k1_relat_1 @ sk_E) @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '24'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.20/0.49          | ~ (zip_tseitin_0 @ X35 @ X36 @ X37))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.49        | (m1_subset_1 @ sk_D @ 
% 0.20/0.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf(t7_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.49         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.49           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X31 @ X32)
% 0.20/0.49          | ((X33) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_funct_1 @ X34)
% 0.20/0.49          | ~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.20/0.49          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.20/0.49          | (r2_hidden @ (k1_funct_1 @ X34 @ X31) @ X33))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.49          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.20/0.49          | ~ (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))
% 0.20/0.49          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.49          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.49          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.20/0.49          | ~ (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))
% 0.20/0.49          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.49          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.49          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.20/0.49          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.20/0.49          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.49          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_B)
% 0.20/0.49        | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.49        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.49        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '36'])).
% 0.20/0.49  thf(d8_partfun1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.49           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 0.20/0.49          | ((k7_partfun1 @ X24 @ X23 @ X22) = (k1_funct_1 @ X23 @ X22))
% 0.20/0.49          | ~ (v1_funct_1 @ X23)
% 0.20/0.49          | ~ (v5_relat_1 @ X23 @ X24)
% 0.20/0.49          | ~ (v1_relat_1 @ X23))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.49          | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.49          | (v1_xboole_0 @ sk_B)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_E)
% 0.20/0.49          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.49          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.20/0.49              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.49          | (v1_relat_1 @ X8)
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_E))),
% 0.20/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf(fc6_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.49  thf('44', plain, ((v1_relat_1 @ sk_E)),
% 0.20/0.49      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('45', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.49          | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.49          | (v1_xboole_0 @ sk_B)
% 0.20/0.49          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.20/0.49          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.20/0.49              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.20/0.49      inference('demod', [status(thm)], ['39', '44', '45'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.20/0.49          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.20/0.49        | (v1_xboole_0 @ sk_B)
% 0.20/0.49        | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.49        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '46'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.20/0.49         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('49', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t185_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.49       ( ![D:$i]:
% 0.20/0.49         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.49             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.49           ( ![E:$i]:
% 0.20/0.49             ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.49                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.20/0.49               ( ![F:$i]:
% 0.20/0.49                 ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.49                   ( ( r1_tarski @
% 0.20/0.49                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.20/0.49                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.20/0.49                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.49                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.20/0.49                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.49         (~ (v1_funct_1 @ X25)
% 0.20/0.49          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.20/0.49          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.20/0.49          | ~ (m1_subset_1 @ X28 @ X26)
% 0.20/0.49          | ((k1_funct_1 @ (k8_funct_2 @ X26 @ X27 @ X30 @ X25 @ X29) @ X28)
% 0.20/0.49              = (k1_funct_1 @ X29 @ (k1_funct_1 @ X25 @ X28)))
% 0.20/0.49          | ((X26) = (k1_xboole_0))
% 0.20/0.49          | ~ (r1_tarski @ (k2_relset_1 @ X26 @ X27 @ X25) @ 
% 0.20/0.49               (k1_relset_1 @ X27 @ X30 @ X29))
% 0.20/0.49          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X30)))
% 0.20/0.49          | ~ (v1_funct_1 @ X29)
% 0.20/0.49          | (v1_xboole_0 @ X27))),
% 0.20/0.49      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_C)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.20/0.49          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.49               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.20/0.49          | ((sk_B) = (k1_xboole_0))
% 0.20/0.49          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.20/0.49              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.20/0.49          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.49  thf('54', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_C)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.20/0.49          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.49               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.20/0.49          | ((sk_B) = (k1_xboole_0))
% 0.20/0.49          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.20/0.49              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.20/0.49  thf('57', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_C)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.20/0.49          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.49               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.20/0.49          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.20/0.49              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.49             (k1_relat_1 @ sk_E))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.20/0.49          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.20/0.49              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.20/0.49          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 0.20/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.49          | (v1_xboole_0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['50', '58'])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '17'])).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('62', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.20/0.49          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.20/0.49              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.20/0.49          | (v1_xboole_0 @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.20/0.49  thf('64', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.20/0.49            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['63', '64'])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.20/0.49         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['49', '65'])).
% 0.20/0.49  thf('67', plain,
% 0.20/0.49      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.20/0.49         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.20/0.49      inference('demod', [status(thm)], ['48', '66'])).
% 0.20/0.49  thf('68', plain,
% 0.20/0.49      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.20/0.49          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.20/0.49        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.49        | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.49        | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['47', '67'])).
% 0.20/0.49  thf('69', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_B)
% 0.20/0.49        | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.49        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      (![X38 : $i, X39 : $i]:
% 0.20/0.49         (((X38) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X38 @ X39))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      ((((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.49        | (v1_xboole_0 @ sk_B)
% 0.20/0.49        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.49  thf(l13_xboole_0, axiom,
% 0.20/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('72', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.49  thf('73', plain,
% 0.20/0.49      ((((sk_C) = (k1_xboole_0))
% 0.20/0.49        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.49  thf('74', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('75', plain,
% 0.20/0.49      ((((sk_C) = (k1_xboole_0)) | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.20/0.49  thf('76', plain,
% 0.20/0.49      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.49        | (m1_subset_1 @ sk_D @ 
% 0.20/0.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf(cc1_subset_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.20/0.49  thf('77', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.20/0.49          | (v1_xboole_0 @ X4)
% 0.20/0.49          | ~ (v1_xboole_0 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.49  thf('78', plain,
% 0.20/0.49      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.20/0.49        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E)))
% 0.20/0.49        | (v1_xboole_0 @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.49  thf('79', plain,
% 0.20/0.49      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ k1_xboole_0))
% 0.20/0.49        | ((sk_C) = (k1_xboole_0))
% 0.20/0.49        | (v1_xboole_0 @ sk_D)
% 0.20/0.49        | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['75', '78'])).
% 0.20/0.49  thf(t113_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf('80', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.49  thf('81', plain,
% 0.20/0.49      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['80'])).
% 0.20/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.49  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf('83', plain,
% 0.20/0.49      ((((sk_C) = (k1_xboole_0))
% 0.20/0.49        | (v1_xboole_0 @ sk_D)
% 0.20/0.49        | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['79', '81', '82'])).
% 0.20/0.49  thf('84', plain,
% 0.20/0.49      (![X38 : $i, X39 : $i]:
% 0.20/0.49         (((X38) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X38 @ X39))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.49  thf('85', plain, (((v1_xboole_0 @ sk_D) | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.49      inference('clc', [status(thm)], ['83', '84'])).
% 0.20/0.49  thf('86', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.49  thf('87', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['85', '86'])).
% 0.20/0.49  thf('88', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('89', plain,
% 0.20/0.49      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.49  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf('91', plain, (((sk_D) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['89', '90'])).
% 0.20/0.49  thf('92', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf('93', plain, ((v1_xboole_0 @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '91', '92'])).
% 0.20/0.49  thf('94', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.49  thf('95', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.49  thf('96', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('97', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
