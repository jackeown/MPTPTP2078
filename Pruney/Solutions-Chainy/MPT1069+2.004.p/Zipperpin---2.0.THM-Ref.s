%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.84c4EUQxaJ

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:01 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 288 expanded)
%              Number of leaves         :   48 ( 105 expanded)
%              Depth                    :   22
%              Number of atoms          : 1395 (5930 expanded)
%              Number of equality atoms :   66 ( 237 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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

thf('13',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( zip_tseitin_1 @ X48 @ X49 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X49 @ X48 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ( zip_tseitin_0 @ X50 @ X51 @ X49 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X49 @ X48 @ X50 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ X0 )
      | ( zip_tseitin_0 @ sk_D @ X0 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ X0 )
      | ( zip_tseitin_0 @ sk_D @ X0 @ sk_B_1 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( zip_tseitin_0 @ sk_D @ ( k1_relat_1 @ sk_E ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( v1_funct_2 @ X43 @ X45 @ X44 )
      | ~ ( zip_tseitin_0 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( v1_funct_2 @ sk_D @ sk_B_1 @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( zip_tseitin_0 @ sk_D @ ( k1_relat_1 @ sk_E ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('22',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( zip_tseitin_0 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('24',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ( X41 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X42 @ X39 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['6','29'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('31',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ X31 ) )
      | ( ( k7_partfun1 @ X32 @ X31 @ X30 )
        = ( k1_funct_1 @ X31 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v5_relat_1 @ X31 @ X32 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['32','35','36'])).

thf('38',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','37'])).

thf('39',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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

thf('43',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ X34 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X34 @ X35 @ X38 @ X33 @ X37 ) @ X36 )
        = ( k1_funct_1 @ X37 @ ( k1_funct_1 @ X33 @ X36 ) ) )
      | ( X34 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X34 @ X35 @ X33 ) @ ( k1_relset_1 @ X35 @ X38 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['40','56'])).

thf('58',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['39','57'])).

thf('59',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('61',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['69'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['60','72'])).

thf('74',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('75',plain,
    ( ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('77',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('78',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_E ) ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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

thf('80',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc6_funct_2])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['70','71'])).

thf('88',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_E ) ) )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['78','88'])).

thf('90',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','89'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('91',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('92',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['90','92','93'])).

thf('95',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('96',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','96','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.84c4EUQxaJ
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:57:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.70/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.88  % Solved by: fo/fo7.sh
% 0.70/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.88  % done 707 iterations in 0.428s
% 0.70/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.88  % SZS output start Refutation
% 0.70/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.70/0.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.70/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.70/0.88  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.70/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.88  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.70/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.88  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.70/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.70/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.88  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.70/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.70/0.88  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.70/0.88  thf(sk_F_type, type, sk_F: $i).
% 0.70/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.88  thf(sk_D_type, type, sk_D: $i).
% 0.70/0.88  thf(sk_E_type, type, sk_E: $i).
% 0.70/0.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.70/0.88  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.70/0.88  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.70/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.88  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.70/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.70/0.88  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.70/0.88  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.70/0.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.70/0.88  thf(t186_funct_2, conjecture,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.70/0.88       ( ![D:$i]:
% 0.70/0.88         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.70/0.88             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.70/0.88           ( ![E:$i]:
% 0.70/0.88             ( ( ( v1_funct_1 @ E ) & 
% 0.70/0.88                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.70/0.88               ( ![F:$i]:
% 0.70/0.88                 ( ( m1_subset_1 @ F @ B ) =>
% 0.70/0.88                   ( ( r1_tarski @
% 0.70/0.88                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.70/0.88                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.70/0.88                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.70/0.88                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.70/0.88                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.70/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.88    (~( ![A:$i,B:$i,C:$i]:
% 0.70/0.88        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.70/0.88          ( ![D:$i]:
% 0.70/0.88            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.70/0.88                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.70/0.88              ( ![E:$i]:
% 0.70/0.88                ( ( ( v1_funct_1 @ E ) & 
% 0.70/0.88                    ( m1_subset_1 @
% 0.70/0.88                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.70/0.88                  ( ![F:$i]:
% 0.70/0.88                    ( ( m1_subset_1 @ F @ B ) =>
% 0.70/0.88                      ( ( r1_tarski @
% 0.70/0.88                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.70/0.88                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.70/0.88                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.70/0.88                          ( ( k1_funct_1 @
% 0.70/0.88                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.70/0.88                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.70/0.88    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.70/0.88  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('1', plain,
% 0.70/0.88      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(cc2_relset_1, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.88       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.70/0.88  thf('2', plain,
% 0.70/0.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.70/0.88         ((v5_relat_1 @ X21 @ X23)
% 0.70/0.88          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.70/0.88      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.70/0.88  thf('3', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.70/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.88  thf('4', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(t2_subset, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( m1_subset_1 @ A @ B ) =>
% 0.70/0.88       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.70/0.88  thf('5', plain,
% 0.70/0.88      (![X15 : $i, X16 : $i]:
% 0.70/0.88         ((r2_hidden @ X15 @ X16)
% 0.70/0.88          | (v1_xboole_0 @ X16)
% 0.70/0.88          | ~ (m1_subset_1 @ X15 @ X16))),
% 0.70/0.88      inference('cnf', [status(esa)], [t2_subset])).
% 0.70/0.88  thf('6', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['4', '5'])).
% 0.70/0.88  thf('7', plain,
% 0.70/0.88      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.70/0.88        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('8', plain,
% 0.70/0.88      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(redefinition_k1_relset_1, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.88       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.70/0.88  thf('9', plain,
% 0.70/0.88      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.70/0.88         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.70/0.88          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.70/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.70/0.88  thf('10', plain,
% 0.70/0.88      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.70/0.88      inference('sup-', [status(thm)], ['8', '9'])).
% 0.70/0.88  thf('11', plain,
% 0.70/0.88      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.70/0.88        (k1_relat_1 @ sk_E))),
% 0.70/0.88      inference('demod', [status(thm)], ['7', '10'])).
% 0.70/0.88  thf('12', plain,
% 0.70/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(t8_funct_2, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.88     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.70/0.88         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.70/0.88       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.70/0.88         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.70/0.88             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.70/0.88           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.70/0.88  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.70/0.88  thf(zf_stmt_2, axiom,
% 0.70/0.88    (![B:$i,A:$i]:
% 0.70/0.88     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.70/0.88       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.70/0.88  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.70/0.88  thf(zf_stmt_4, axiom,
% 0.70/0.88    (![D:$i,C:$i,A:$i]:
% 0.70/0.88     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 0.70/0.88       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.70/0.88         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.70/0.88  thf(zf_stmt_5, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.88     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.70/0.88         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.88       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.70/0.88         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 0.70/0.88  thf('13', plain,
% 0.70/0.88      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.70/0.88         ((zip_tseitin_1 @ X48 @ X49)
% 0.70/0.88          | ~ (v1_funct_1 @ X50)
% 0.70/0.88          | ~ (v1_funct_2 @ X50 @ X49 @ X48)
% 0.70/0.88          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 0.70/0.88          | (zip_tseitin_0 @ X50 @ X51 @ X49)
% 0.70/0.88          | ~ (r1_tarski @ (k2_relset_1 @ X49 @ X48 @ X50) @ X51))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.70/0.88  thf('14', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ X0)
% 0.70/0.88          | (zip_tseitin_0 @ sk_D @ X0 @ sk_B_1)
% 0.70/0.88          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 0.70/0.88          | ~ (v1_funct_1 @ sk_D)
% 0.70/0.88          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['12', '13'])).
% 0.70/0.88  thf('15', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('17', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ X0)
% 0.70/0.88          | (zip_tseitin_0 @ sk_D @ X0 @ sk_B_1)
% 0.70/0.88          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1))),
% 0.70/0.88      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.70/0.88  thf('18', plain,
% 0.70/0.88      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 0.70/0.88        | (zip_tseitin_0 @ sk_D @ (k1_relat_1 @ sk_E) @ sk_B_1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['11', '17'])).
% 0.70/0.88  thf('19', plain,
% 0.70/0.88      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.70/0.88         ((v1_funct_2 @ X43 @ X45 @ X44) | ~ (zip_tseitin_0 @ X43 @ X44 @ X45))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.70/0.88  thf('20', plain,
% 0.70/0.88      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 0.70/0.88        | (v1_funct_2 @ sk_D @ sk_B_1 @ (k1_relat_1 @ sk_E)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['18', '19'])).
% 0.70/0.88  thf('21', plain,
% 0.70/0.88      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 0.70/0.88        | (zip_tseitin_0 @ sk_D @ (k1_relat_1 @ sk_E) @ sk_B_1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['11', '17'])).
% 0.70/0.88  thf('22', plain,
% 0.70/0.88      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.70/0.88         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.70/0.88          | ~ (zip_tseitin_0 @ X43 @ X44 @ X45))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.70/0.88  thf('23', plain,
% 0.70/0.88      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 0.70/0.88        | (m1_subset_1 @ sk_D @ 
% 0.70/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_E)))))),
% 0.70/0.88      inference('sup-', [status(thm)], ['21', '22'])).
% 0.70/0.88  thf(t7_funct_2, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.88     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.70/0.88         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.88       ( ( r2_hidden @ C @ A ) =>
% 0.70/0.88         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.70/0.88           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.70/0.88  thf('24', plain,
% 0.70/0.88      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X39 @ X40)
% 0.70/0.88          | ((X41) = (k1_xboole_0))
% 0.70/0.88          | ~ (v1_funct_1 @ X42)
% 0.70/0.88          | ~ (v1_funct_2 @ X42 @ X40 @ X41)
% 0.70/0.88          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.70/0.88          | (r2_hidden @ (k1_funct_1 @ X42 @ X39) @ X41))),
% 0.70/0.88      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.70/0.88  thf('25', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 0.70/0.88          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.70/0.88          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ (k1_relat_1 @ sk_E))
% 0.70/0.88          | ~ (v1_funct_1 @ sk_D)
% 0.70/0.88          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.70/0.88          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['23', '24'])).
% 0.70/0.88  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('27', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 0.70/0.88          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.70/0.88          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ (k1_relat_1 @ sk_E))
% 0.70/0.88          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.70/0.88          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.70/0.88      inference('demod', [status(thm)], ['25', '26'])).
% 0.70/0.88  thf('28', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 0.70/0.88          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.70/0.88          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.70/0.88          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.70/0.88          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['20', '27'])).
% 0.70/0.88  thf('29', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.70/0.88          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.70/0.88          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.70/0.88          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1))),
% 0.70/0.88      inference('simplify', [status(thm)], ['28'])).
% 0.70/0.88  thf('30', plain,
% 0.70/0.88      (((v1_xboole_0 @ sk_B_1)
% 0.70/0.88        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 0.70/0.88        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.70/0.88        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['6', '29'])).
% 0.70/0.88  thf(d8_partfun1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.70/0.88       ( ![C:$i]:
% 0.70/0.88         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.70/0.88           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.70/0.88  thf('31', plain,
% 0.70/0.88      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X30 @ (k1_relat_1 @ X31))
% 0.70/0.88          | ((k7_partfun1 @ X32 @ X31 @ X30) = (k1_funct_1 @ X31 @ X30))
% 0.70/0.88          | ~ (v1_funct_1 @ X31)
% 0.70/0.88          | ~ (v5_relat_1 @ X31 @ X32)
% 0.70/0.88          | ~ (v1_relat_1 @ X31))),
% 0.70/0.88      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.70/0.88  thf('32', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.70/0.88          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 0.70/0.88          | (v1_xboole_0 @ sk_B_1)
% 0.70/0.88          | ~ (v1_relat_1 @ sk_E)
% 0.70/0.88          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.70/0.88          | ~ (v1_funct_1 @ sk_E)
% 0.70/0.88          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.70/0.88              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.70/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.70/0.88  thf('33', plain,
% 0.70/0.88      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(cc1_relset_1, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.88       ( v1_relat_1 @ C ) ))).
% 0.70/0.88  thf('34', plain,
% 0.70/0.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.70/0.88         ((v1_relat_1 @ X18)
% 0.70/0.88          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.70/0.88      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.70/0.88  thf('35', plain, ((v1_relat_1 @ sk_E)),
% 0.70/0.88      inference('sup-', [status(thm)], ['33', '34'])).
% 0.70/0.88  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('37', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.70/0.88          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 0.70/0.88          | (v1_xboole_0 @ sk_B_1)
% 0.70/0.88          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.70/0.88          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.70/0.88              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.70/0.88      inference('demod', [status(thm)], ['32', '35', '36'])).
% 0.70/0.88  thf('38', plain,
% 0.70/0.88      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.70/0.88          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.70/0.88        | (v1_xboole_0 @ sk_B_1)
% 0.70/0.88        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 0.70/0.88        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['3', '37'])).
% 0.70/0.88  thf('39', plain,
% 0.70/0.88      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.70/0.88         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('40', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('41', plain,
% 0.70/0.88      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.70/0.88      inference('sup-', [status(thm)], ['8', '9'])).
% 0.70/0.88  thf('42', plain,
% 0.70/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(t185_funct_2, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.70/0.88       ( ![D:$i]:
% 0.70/0.88         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.70/0.88             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.70/0.88           ( ![E:$i]:
% 0.70/0.88             ( ( ( v1_funct_1 @ E ) & 
% 0.70/0.88                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.70/0.88               ( ![F:$i]:
% 0.70/0.88                 ( ( m1_subset_1 @ F @ B ) =>
% 0.70/0.88                   ( ( r1_tarski @
% 0.70/0.88                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.70/0.88                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.70/0.88                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.70/0.88                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.70/0.88                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.70/0.88  thf('43', plain,
% 0.70/0.88      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.70/0.88         (~ (v1_funct_1 @ X33)
% 0.70/0.88          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.70/0.88          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.70/0.88          | ~ (m1_subset_1 @ X36 @ X34)
% 0.70/0.88          | ((k1_funct_1 @ (k8_funct_2 @ X34 @ X35 @ X38 @ X33 @ X37) @ X36)
% 0.70/0.88              = (k1_funct_1 @ X37 @ (k1_funct_1 @ X33 @ X36)))
% 0.70/0.88          | ((X34) = (k1_xboole_0))
% 0.70/0.88          | ~ (r1_tarski @ (k2_relset_1 @ X34 @ X35 @ X33) @ 
% 0.70/0.88               (k1_relset_1 @ X35 @ X38 @ X37))
% 0.70/0.88          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X38)))
% 0.70/0.88          | ~ (v1_funct_1 @ X37)
% 0.70/0.88          | (v1_xboole_0 @ X35))),
% 0.70/0.88      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.70/0.88  thf('44', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         ((v1_xboole_0 @ sk_C_1)
% 0.70/0.88          | ~ (v1_funct_1 @ X0)
% 0.70/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.70/0.88          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.70/0.88               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.70/0.88          | ((sk_B_1) = (k1_xboole_0))
% 0.70/0.88          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.70/0.88              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.70/0.88          | ~ (m1_subset_1 @ X2 @ sk_B_1)
% 0.70/0.88          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 0.70/0.88          | ~ (v1_funct_1 @ sk_D))),
% 0.70/0.88      inference('sup-', [status(thm)], ['42', '43'])).
% 0.70/0.88  thf('45', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('47', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         ((v1_xboole_0 @ sk_C_1)
% 0.70/0.88          | ~ (v1_funct_1 @ X0)
% 0.70/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.70/0.88          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.70/0.88               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.70/0.88          | ((sk_B_1) = (k1_xboole_0))
% 0.70/0.88          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.70/0.88              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.70/0.88          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 0.70/0.88      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.70/0.88  thf('48', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('49', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         ((v1_xboole_0 @ sk_C_1)
% 0.70/0.88          | ~ (v1_funct_1 @ X0)
% 0.70/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.70/0.88          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.70/0.88               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.70/0.88          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.70/0.89              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.70/0.89          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 0.70/0.89      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.70/0.89  thf('50', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.70/0.89             (k1_relat_1 @ sk_E))
% 0.70/0.89          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.70/0.89          | ((k1_funct_1 @ 
% 0.70/0.89              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.70/0.89              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.70/0.89          | ~ (m1_subset_1 @ sk_E @ 
% 0.70/0.89               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 0.70/0.89          | ~ (v1_funct_1 @ sk_E)
% 0.70/0.89          | (v1_xboole_0 @ sk_C_1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['41', '49'])).
% 0.70/0.89  thf('51', plain,
% 0.70/0.89      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.70/0.89        (k1_relat_1 @ sk_E))),
% 0.70/0.89      inference('demod', [status(thm)], ['7', '10'])).
% 0.70/0.89  thf('52', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('53', plain, ((v1_funct_1 @ sk_E)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('54', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.70/0.89          | ((k1_funct_1 @ 
% 0.70/0.89              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.70/0.89              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.70/0.89          | (v1_xboole_0 @ sk_C_1))),
% 0.70/0.89      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.70/0.89  thf('55', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('56', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.70/0.89            X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.70/0.89          | ~ (m1_subset_1 @ X0 @ sk_B_1))),
% 0.70/0.89      inference('clc', [status(thm)], ['54', '55'])).
% 0.70/0.89  thf('57', plain,
% 0.70/0.89      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.70/0.89         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['40', '56'])).
% 0.70/0.89  thf('58', plain,
% 0.70/0.89      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.70/0.89         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.70/0.89      inference('demod', [status(thm)], ['39', '57'])).
% 0.70/0.89  thf('59', plain,
% 0.70/0.89      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.70/0.89          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.70/0.89        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.70/0.89        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 0.70/0.89        | (v1_xboole_0 @ sk_B_1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['38', '58'])).
% 0.70/0.89  thf('60', plain,
% 0.70/0.89      (((v1_xboole_0 @ sk_B_1)
% 0.70/0.89        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 0.70/0.89        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.70/0.89      inference('simplify', [status(thm)], ['59'])).
% 0.70/0.89  thf(d3_tarski, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( r1_tarski @ A @ B ) <=>
% 0.70/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.70/0.89  thf('61', plain,
% 0.70/0.89      (![X4 : $i, X6 : $i]:
% 0.70/0.89         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.89  thf(d1_xboole_0, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.70/0.89  thf('62', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.89  thf('63', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['61', '62'])).
% 0.70/0.89  thf('64', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['61', '62'])).
% 0.70/0.89  thf(d10_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.89  thf('65', plain,
% 0.70/0.89      (![X7 : $i, X9 : $i]:
% 0.70/0.89         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.70/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.89  thf('66', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['64', '65'])).
% 0.70/0.89  thf('67', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['63', '66'])).
% 0.70/0.89  thf('68', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('69', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (((X0) != (k1_xboole_0))
% 0.70/0.89          | ~ (v1_xboole_0 @ sk_B_1)
% 0.70/0.89          | ~ (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['67', '68'])).
% 0.70/0.89  thf('70', plain,
% 0.70/0.89      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.70/0.89      inference('simplify', [status(thm)], ['69'])).
% 0.70/0.89  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.70/0.89  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.89  thf('72', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.70/0.89      inference('simplify_reflect+', [status(thm)], ['70', '71'])).
% 0.70/0.89  thf('73', plain,
% 0.70/0.89      ((((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.70/0.89        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1))),
% 0.70/0.89      inference('clc', [status(thm)], ['60', '72'])).
% 0.70/0.89  thf('74', plain,
% 0.70/0.89      (![X46 : $i, X47 : $i]:
% 0.70/0.89         (((X46) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X46 @ X47))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.70/0.89  thf('75', plain,
% 0.70/0.89      ((((k1_relat_1 @ sk_E) = (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['73', '74'])).
% 0.70/0.89  thf('76', plain,
% 0.70/0.89      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 0.70/0.89        | (m1_subset_1 @ sk_D @ 
% 0.70/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_E)))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['21', '22'])).
% 0.70/0.89  thf(cc1_subset_1, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( v1_xboole_0 @ A ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.70/0.89  thf('77', plain,
% 0.70/0.89      (![X13 : $i, X14 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.70/0.89          | (v1_xboole_0 @ X13)
% 0.70/0.89          | ~ (v1_xboole_0 @ X14))),
% 0.70/0.89      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.70/0.89  thf('78', plain,
% 0.70/0.89      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 0.70/0.89        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_E)))
% 0.70/0.89        | (v1_xboole_0 @ sk_D))),
% 0.70/0.89      inference('sup-', [status(thm)], ['76', '77'])).
% 0.70/0.89  thf('79', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(cc6_funct_2, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.70/0.89       ( ![C:$i]:
% 0.70/0.89         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.89           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.70/0.89             ( ( v1_funct_1 @ C ) & ( ~( v1_xboole_0 @ C ) ) & 
% 0.70/0.89               ( v1_funct_2 @ C @ A @ B ) ) ) ) ) ))).
% 0.70/0.89  thf('80', plain,
% 0.70/0.89      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.70/0.89         ((v1_xboole_0 @ X27)
% 0.70/0.89          | (v1_xboole_0 @ X28)
% 0.70/0.89          | ~ (v1_funct_1 @ X29)
% 0.70/0.89          | ~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.70/0.89          | ~ (v1_xboole_0 @ X29)
% 0.70/0.89          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.70/0.89      inference('cnf', [status(esa)], [cc6_funct_2])).
% 0.70/0.89  thf('81', plain,
% 0.70/0.89      ((~ (v1_xboole_0 @ sk_D)
% 0.70/0.89        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 0.70/0.89        | ~ (v1_funct_1 @ sk_D)
% 0.70/0.89        | (v1_xboole_0 @ sk_C_1)
% 0.70/0.89        | (v1_xboole_0 @ sk_B_1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['79', '80'])).
% 0.70/0.89  thf('82', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('83', plain, ((v1_funct_1 @ sk_D)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('84', plain,
% 0.70/0.89      ((~ (v1_xboole_0 @ sk_D)
% 0.70/0.89        | (v1_xboole_0 @ sk_C_1)
% 0.70/0.89        | (v1_xboole_0 @ sk_B_1))),
% 0.70/0.89      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.70/0.89  thf('85', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('86', plain, (((v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_D))),
% 0.70/0.89      inference('clc', [status(thm)], ['84', '85'])).
% 0.70/0.89  thf('87', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.70/0.89      inference('simplify_reflect+', [status(thm)], ['70', '71'])).
% 0.70/0.89  thf('88', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.70/0.89      inference('clc', [status(thm)], ['86', '87'])).
% 0.70/0.89  thf('89', plain,
% 0.70/0.89      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_E)))
% 0.70/0.89        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1))),
% 0.70/0.89      inference('clc', [status(thm)], ['78', '88'])).
% 0.70/0.89  thf('90', plain,
% 0.70/0.89      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0))
% 0.70/0.89        | ((sk_C_1) = (k1_xboole_0))
% 0.70/0.89        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['75', '89'])).
% 0.70/0.89  thf(t113_zfmisc_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.70/0.89       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.70/0.89  thf('91', plain,
% 0.70/0.89      (![X11 : $i, X12 : $i]:
% 0.70/0.89         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.70/0.89          | ((X12) != (k1_xboole_0)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.70/0.89  thf('92', plain,
% 0.70/0.89      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.89      inference('simplify', [status(thm)], ['91'])).
% 0.70/0.89  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.89  thf('94', plain,
% 0.70/0.89      ((((sk_C_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1))),
% 0.70/0.89      inference('demod', [status(thm)], ['90', '92', '93'])).
% 0.70/0.89  thf('95', plain,
% 0.70/0.89      (![X46 : $i, X47 : $i]:
% 0.70/0.89         (((X46) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X46 @ X47))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.70/0.89  thf('96', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.70/0.89      inference('clc', [status(thm)], ['94', '95'])).
% 0.70/0.89  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.89  thf('98', plain, ($false),
% 0.70/0.89      inference('demod', [status(thm)], ['0', '96', '97'])).
% 0.70/0.89  
% 0.70/0.89  % SZS output end Refutation
% 0.70/0.89  
% 0.70/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
