%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3dhmqEfXMo

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:40 EST 2020

% Result     : Theorem 21.27s
% Output     : Refutation 21.27s
% Verified   : 
% Statistics : Number of formulae       :  203 (1898 expanded)
%              Number of leaves         :   42 ( 573 expanded)
%              Depth                    :   26
%              Number of atoms          : 1570 (23210 expanded)
%              Number of equality atoms :  139 (1817 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t38_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
            & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
            & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X40 @ X41 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X44 @ X45 @ X43 @ X46 )
        = ( k7_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('13',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X40 @ X41 @ X39 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X30 )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('38',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['13','37'])).

thf('39',plain,(
    r1_tarski @ sk_C @ sk_A ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('40',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['40','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('45',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('53',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('62',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('63',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('68',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('69',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('72',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('74',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('77',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('79',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('81',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X15 @ X16 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('85',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('86',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['84','85'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('93',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf('97',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['84','85'])).

thf('98',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['91','98'])).

thf('100',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('101',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X44 @ X45 @ X43 @ X46 )
        = ( k7_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','105'])).

thf('107',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('108',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('109',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('110',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('111',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('112',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('113',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','105'])).

thf('114',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('115',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('116',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('124',plain,(
    ! [X31: $i] :
      ( zip_tseitin_0 @ X31 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('126',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['122','128'])).

thf('130',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['63','72','77','106','107','108','109','110','111','112','113','114','129'])).

thf('131',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('132',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['130','131'])).

thf('133',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['60','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','133'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(condensation,[status(thm)],['137'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('139',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['39','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('145',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ sk_B @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('151',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ~ ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['149','152'])).

thf('154',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['60','132'])).

thf('155',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['148','155'])).

thf('157',plain,
    ( ( sk_C != sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['143','156'])).

thf('158',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    $false ),
    inference(demod,[status(thm)],['38','158'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3dhmqEfXMo
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:10:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 21.27/21.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 21.27/21.45  % Solved by: fo/fo7.sh
% 21.27/21.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.27/21.45  % done 13152 iterations in 20.982s
% 21.27/21.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 21.27/21.45  % SZS output start Refutation
% 21.27/21.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 21.27/21.45  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 21.27/21.45  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 21.27/21.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 21.27/21.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 21.27/21.45  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 21.27/21.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 21.27/21.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 21.27/21.45  thf(sk_D_type, type, sk_D: $i).
% 21.27/21.45  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 21.27/21.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 21.27/21.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 21.27/21.45  thf(sk_A_type, type, sk_A: $i).
% 21.27/21.45  thf(sk_B_type, type, sk_B: $i).
% 21.27/21.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 21.27/21.45  thf(sk_C_type, type, sk_C: $i).
% 21.27/21.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 21.27/21.45  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 21.27/21.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 21.27/21.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 21.27/21.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 21.27/21.45  thf(t38_funct_2, conjecture,
% 21.27/21.45    (![A:$i,B:$i,C:$i,D:$i]:
% 21.27/21.45     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 21.27/21.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.27/21.45       ( ( r1_tarski @ C @ A ) =>
% 21.27/21.45         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 21.27/21.45           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 21.27/21.45             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 21.27/21.45             ( m1_subset_1 @
% 21.27/21.45               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 21.27/21.45               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 21.27/21.45  thf(zf_stmt_0, negated_conjecture,
% 21.27/21.45    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 21.27/21.45        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 21.27/21.45            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.27/21.45          ( ( r1_tarski @ C @ A ) =>
% 21.27/21.45            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 21.27/21.45              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 21.27/21.45                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 21.27/21.45                ( m1_subset_1 @
% 21.27/21.45                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 21.27/21.45                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 21.27/21.45    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 21.27/21.45  thf('0', plain,
% 21.27/21.45      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 21.27/21.45        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 21.27/21.45             sk_B)
% 21.27/21.45        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 21.27/21.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 21.27/21.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.45  thf('1', plain,
% 21.27/21.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.27/21.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.45  thf(dt_k2_partfun1, axiom,
% 21.27/21.45    (![A:$i,B:$i,C:$i,D:$i]:
% 21.27/21.45     ( ( ( v1_funct_1 @ C ) & 
% 21.27/21.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.27/21.45       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 21.27/21.45         ( m1_subset_1 @
% 21.27/21.45           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 21.27/21.45           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 21.27/21.45  thf('2', plain,
% 21.27/21.45      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 21.27/21.45         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 21.27/21.45          | ~ (v1_funct_1 @ X39)
% 21.27/21.45          | (v1_funct_1 @ (k2_partfun1 @ X40 @ X41 @ X39 @ X42)))),
% 21.27/21.45      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 21.27/21.45  thf('3', plain,
% 21.27/21.45      (![X0 : $i]:
% 21.27/21.45         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 21.27/21.45          | ~ (v1_funct_1 @ sk_D))),
% 21.27/21.45      inference('sup-', [status(thm)], ['1', '2'])).
% 21.27/21.45  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 21.27/21.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.45  thf('5', plain,
% 21.27/21.45      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 21.27/21.45      inference('demod', [status(thm)], ['3', '4'])).
% 21.27/21.45  thf('6', plain,
% 21.27/21.45      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 21.27/21.45        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 21.27/21.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 21.27/21.45      inference('demod', [status(thm)], ['0', '5'])).
% 21.27/21.45  thf('7', plain,
% 21.27/21.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.27/21.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.45  thf(redefinition_k2_partfun1, axiom,
% 21.27/21.45    (![A:$i,B:$i,C:$i,D:$i]:
% 21.27/21.45     ( ( ( v1_funct_1 @ C ) & 
% 21.27/21.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.27/21.45       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 21.27/21.45  thf('8', plain,
% 21.27/21.45      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 21.27/21.45         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 21.27/21.45          | ~ (v1_funct_1 @ X43)
% 21.27/21.45          | ((k2_partfun1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 21.27/21.45      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 21.27/21.45  thf('9', plain,
% 21.27/21.45      (![X0 : $i]:
% 21.27/21.45         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 21.27/21.45          | ~ (v1_funct_1 @ sk_D))),
% 21.27/21.45      inference('sup-', [status(thm)], ['7', '8'])).
% 21.27/21.45  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 21.27/21.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.45  thf('11', plain,
% 21.27/21.45      (![X0 : $i]:
% 21.27/21.45         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 21.27/21.45      inference('demod', [status(thm)], ['9', '10'])).
% 21.27/21.45  thf('12', plain,
% 21.27/21.45      (![X0 : $i]:
% 21.27/21.45         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 21.27/21.45      inference('demod', [status(thm)], ['9', '10'])).
% 21.27/21.45  thf('13', plain,
% 21.27/21.45      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 21.27/21.45        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 21.27/21.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 21.27/21.45      inference('demod', [status(thm)], ['6', '11', '12'])).
% 21.27/21.45  thf('14', plain,
% 21.27/21.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.27/21.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.45  thf('15', plain,
% 21.27/21.45      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 21.27/21.45         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 21.27/21.45          | ~ (v1_funct_1 @ X39)
% 21.27/21.45          | (m1_subset_1 @ (k2_partfun1 @ X40 @ X41 @ X39 @ X42) @ 
% 21.27/21.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 21.27/21.45      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 21.27/21.45  thf('16', plain,
% 21.27/21.45      (![X0 : $i]:
% 21.27/21.45         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 21.27/21.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 21.27/21.45          | ~ (v1_funct_1 @ sk_D))),
% 21.27/21.45      inference('sup-', [status(thm)], ['14', '15'])).
% 21.27/21.45  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 21.27/21.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.45  thf('18', plain,
% 21.27/21.45      (![X0 : $i]:
% 21.27/21.45         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 21.27/21.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.27/21.45      inference('demod', [status(thm)], ['16', '17'])).
% 21.27/21.45  thf('19', plain,
% 21.27/21.45      (![X0 : $i]:
% 21.27/21.45         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 21.27/21.45      inference('demod', [status(thm)], ['9', '10'])).
% 21.27/21.45  thf('20', plain,
% 21.27/21.45      (![X0 : $i]:
% 21.27/21.45         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 21.27/21.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.27/21.45      inference('demod', [status(thm)], ['18', '19'])).
% 21.27/21.45  thf(cc2_relset_1, axiom,
% 21.27/21.45    (![A:$i,B:$i,C:$i]:
% 21.27/21.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.27/21.45       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 21.27/21.45  thf('21', plain,
% 21.27/21.45      (![X22 : $i, X23 : $i, X24 : $i]:
% 21.27/21.45         ((v5_relat_1 @ X22 @ X24)
% 21.27/21.45          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 21.27/21.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 21.27/21.45  thf('22', plain,
% 21.27/21.45      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 21.27/21.45      inference('sup-', [status(thm)], ['20', '21'])).
% 21.27/21.45  thf(d19_relat_1, axiom,
% 21.27/21.45    (![A:$i,B:$i]:
% 21.27/21.45     ( ( v1_relat_1 @ B ) =>
% 21.27/21.45       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 21.27/21.45  thf('23', plain,
% 21.27/21.45      (![X7 : $i, X8 : $i]:
% 21.27/21.45         (~ (v5_relat_1 @ X7 @ X8)
% 21.27/21.45          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 21.27/21.45          | ~ (v1_relat_1 @ X7))),
% 21.27/21.45      inference('cnf', [status(esa)], [d19_relat_1])).
% 21.27/21.45  thf('24', plain,
% 21.27/21.45      (![X0 : $i]:
% 21.27/21.45         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 21.27/21.45          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 21.27/21.45      inference('sup-', [status(thm)], ['22', '23'])).
% 21.27/21.45  thf('25', plain,
% 21.27/21.45      (![X0 : $i]:
% 21.27/21.45         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 21.27/21.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.27/21.45      inference('demod', [status(thm)], ['18', '19'])).
% 21.27/21.45  thf(cc1_relset_1, axiom,
% 21.27/21.45    (![A:$i,B:$i,C:$i]:
% 21.27/21.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.27/21.45       ( v1_relat_1 @ C ) ))).
% 21.27/21.45  thf('26', plain,
% 21.27/21.45      (![X19 : $i, X20 : $i, X21 : $i]:
% 21.27/21.45         ((v1_relat_1 @ X19)
% 21.27/21.45          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 21.27/21.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 21.27/21.45  thf('27', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 21.27/21.45      inference('sup-', [status(thm)], ['25', '26'])).
% 21.27/21.45  thf('28', plain,
% 21.27/21.45      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 21.27/21.45      inference('demod', [status(thm)], ['24', '27'])).
% 21.27/21.45  thf(t87_relat_1, axiom,
% 21.27/21.45    (![A:$i,B:$i]:
% 21.27/21.45     ( ( v1_relat_1 @ B ) =>
% 21.27/21.45       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 21.27/21.45  thf('29', plain,
% 21.27/21.45      (![X13 : $i, X14 : $i]:
% 21.27/21.45         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X13 @ X14)) @ X14)
% 21.27/21.45          | ~ (v1_relat_1 @ X13))),
% 21.27/21.45      inference('cnf', [status(esa)], [t87_relat_1])).
% 21.27/21.45  thf(t11_relset_1, axiom,
% 21.27/21.45    (![A:$i,B:$i,C:$i]:
% 21.27/21.45     ( ( v1_relat_1 @ C ) =>
% 21.27/21.45       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 21.27/21.45           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 21.27/21.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 21.27/21.45  thf('30', plain,
% 21.27/21.45      (![X28 : $i, X29 : $i, X30 : $i]:
% 21.27/21.45         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 21.27/21.45          | ~ (r1_tarski @ (k2_relat_1 @ X28) @ X30)
% 21.27/21.45          | (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 21.27/21.45          | ~ (v1_relat_1 @ X28))),
% 21.27/21.45      inference('cnf', [status(esa)], [t11_relset_1])).
% 21.27/21.45  thf('31', plain,
% 21.27/21.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.27/21.45         (~ (v1_relat_1 @ X1)
% 21.27/21.45          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 21.27/21.45          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 21.27/21.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 21.27/21.45          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 21.27/21.45      inference('sup-', [status(thm)], ['29', '30'])).
% 21.27/21.45  thf('32', plain,
% 21.27/21.45      (![X0 : $i]:
% 21.27/21.45         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 21.27/21.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 21.27/21.45          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 21.27/21.45          | ~ (v1_relat_1 @ sk_D))),
% 21.27/21.45      inference('sup-', [status(thm)], ['28', '31'])).
% 21.27/21.45  thf('33', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 21.27/21.45      inference('sup-', [status(thm)], ['25', '26'])).
% 21.27/21.45  thf('34', plain,
% 21.27/21.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.27/21.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.45  thf('35', plain,
% 21.27/21.45      (![X19 : $i, X20 : $i, X21 : $i]:
% 21.27/21.45         ((v1_relat_1 @ X19)
% 21.27/21.45          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 21.27/21.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 21.27/21.45  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 21.27/21.45      inference('sup-', [status(thm)], ['34', '35'])).
% 21.27/21.45  thf('37', plain,
% 21.27/21.45      (![X0 : $i]:
% 21.27/21.45         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 21.27/21.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 21.27/21.45      inference('demod', [status(thm)], ['32', '33', '36'])).
% 21.27/21.45  thf('38', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 21.27/21.45      inference('demod', [status(thm)], ['13', '37'])).
% 21.27/21.45  thf('39', plain, ((r1_tarski @ sk_C @ sk_A)),
% 21.27/21.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.45  thf(d1_funct_2, axiom,
% 21.27/21.45    (![A:$i,B:$i,C:$i]:
% 21.27/21.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.27/21.45       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 21.27/21.45           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 21.27/21.45             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 21.27/21.45         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 21.27/21.45           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 21.27/21.45             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 21.27/21.45  thf(zf_stmt_1, axiom,
% 21.27/21.45    (![B:$i,A:$i]:
% 21.27/21.45     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 21.27/21.45       ( zip_tseitin_0 @ B @ A ) ))).
% 21.27/21.45  thf('40', plain,
% 21.27/21.45      (![X31 : $i, X32 : $i]:
% 21.27/21.45         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 21.27/21.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 21.27/21.45  thf(t113_zfmisc_1, axiom,
% 21.27/21.45    (![A:$i,B:$i]:
% 21.27/21.45     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 21.27/21.45       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 21.27/21.45  thf('41', plain,
% 21.27/21.45      (![X2 : $i, X3 : $i]:
% 21.27/21.45         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 21.27/21.45      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 21.27/21.45  thf('42', plain,
% 21.27/21.45      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 21.27/21.45      inference('simplify', [status(thm)], ['41'])).
% 21.27/21.45  thf('43', plain,
% 21.27/21.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.27/21.45         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 21.27/21.45      inference('sup+', [status(thm)], ['40', '42'])).
% 21.27/21.45  thf('44', plain,
% 21.27/21.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.27/21.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.45  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 21.27/21.45  thf(zf_stmt_3, axiom,
% 21.27/21.45    (![C:$i,B:$i,A:$i]:
% 21.27/21.45     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 21.27/21.45       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 21.27/21.45  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 21.27/21.45  thf(zf_stmt_5, axiom,
% 21.27/21.45    (![A:$i,B:$i,C:$i]:
% 21.27/21.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.27/21.45       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 21.27/21.45         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 21.27/21.45           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 21.27/21.45             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 21.27/21.45  thf('45', plain,
% 21.27/21.45      (![X36 : $i, X37 : $i, X38 : $i]:
% 21.27/21.45         (~ (zip_tseitin_0 @ X36 @ X37)
% 21.27/21.45          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 21.27/21.45          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 21.27/21.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 21.27/21.45  thf('46', plain,
% 21.27/21.45      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 21.27/21.45      inference('sup-', [status(thm)], ['44', '45'])).
% 21.27/21.45  thf('47', plain,
% 21.27/21.45      (![X0 : $i]:
% 21.27/21.45         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 21.27/21.45          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 21.27/21.45      inference('sup-', [status(thm)], ['43', '46'])).
% 21.27/21.45  thf('48', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 21.27/21.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.45  thf('49', plain,
% 21.27/21.45      (![X33 : $i, X34 : $i, X35 : $i]:
% 21.27/21.45         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 21.27/21.45          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 21.27/21.45          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 21.27/21.45      inference('cnf', [status(esa)], [zf_stmt_3])).
% 21.27/21.45  thf('50', plain,
% 21.27/21.45      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 21.27/21.45        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 21.27/21.45      inference('sup-', [status(thm)], ['48', '49'])).
% 21.27/21.45  thf('51', plain,
% 21.27/21.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.27/21.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.45  thf(redefinition_k1_relset_1, axiom,
% 21.27/21.46    (![A:$i,B:$i,C:$i]:
% 21.27/21.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.27/21.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 21.27/21.46  thf('52', plain,
% 21.27/21.46      (![X25 : $i, X26 : $i, X27 : $i]:
% 21.27/21.46         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 21.27/21.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 21.27/21.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 21.27/21.46  thf('53', plain,
% 21.27/21.46      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 21.27/21.46      inference('sup-', [status(thm)], ['51', '52'])).
% 21.27/21.46  thf('54', plain,
% 21.27/21.46      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.27/21.46      inference('demod', [status(thm)], ['50', '53'])).
% 21.27/21.46  thf('55', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 21.27/21.46          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.27/21.46      inference('sup-', [status(thm)], ['47', '54'])).
% 21.27/21.46  thf('56', plain,
% 21.27/21.46      (![X1 : $i, X2 : $i]:
% 21.27/21.46         (((X1) = (k1_xboole_0))
% 21.27/21.46          | ((X2) = (k1_xboole_0))
% 21.27/21.46          | ((k2_zfmisc_1 @ X2 @ X1) != (k1_xboole_0)))),
% 21.27/21.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 21.27/21.46  thf('57', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         (((k1_xboole_0) != (k1_xboole_0))
% 21.27/21.46          | ((sk_A) = (k1_relat_1 @ sk_D))
% 21.27/21.46          | ((sk_B) = (k1_xboole_0))
% 21.27/21.46          | ((X0) = (k1_xboole_0)))),
% 21.27/21.46      inference('sup-', [status(thm)], ['55', '56'])).
% 21.27/21.46  thf('58', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         (((X0) = (k1_xboole_0))
% 21.27/21.46          | ((sk_B) = (k1_xboole_0))
% 21.27/21.46          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.27/21.46      inference('simplify', [status(thm)], ['57'])).
% 21.27/21.46  thf('59', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 21.27/21.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.46  thf('60', plain,
% 21.27/21.46      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 21.27/21.46      inference('split', [status(esa)], ['59'])).
% 21.27/21.46  thf('61', plain,
% 21.27/21.46      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('split', [status(esa)], ['59'])).
% 21.27/21.46  thf('62', plain,
% 21.27/21.46      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 21.27/21.46        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 21.27/21.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 21.27/21.46      inference('demod', [status(thm)], ['0', '5'])).
% 21.27/21.46  thf('63', plain,
% 21.27/21.46      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 21.27/21.46            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 21.27/21.46         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 21.27/21.46              sk_B)))
% 21.27/21.46         <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('sup-', [status(thm)], ['61', '62'])).
% 21.27/21.46  thf('64', plain,
% 21.27/21.46      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('split', [status(esa)], ['59'])).
% 21.27/21.46  thf('65', plain,
% 21.27/21.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.27/21.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.46  thf('66', plain,
% 21.27/21.46      (((m1_subset_1 @ sk_D @ 
% 21.27/21.46         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 21.27/21.46         <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('sup+', [status(thm)], ['64', '65'])).
% 21.27/21.46  thf('67', plain,
% 21.27/21.46      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 21.27/21.46      inference('simplify', [status(thm)], ['41'])).
% 21.27/21.46  thf('68', plain,
% 21.27/21.46      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 21.27/21.46         <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('demod', [status(thm)], ['66', '67'])).
% 21.27/21.46  thf(t3_subset, axiom,
% 21.27/21.46    (![A:$i,B:$i]:
% 21.27/21.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 21.27/21.46  thf('69', plain,
% 21.27/21.46      (![X4 : $i, X5 : $i]:
% 21.27/21.46         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 21.27/21.46      inference('cnf', [status(esa)], [t3_subset])).
% 21.27/21.46  thf('70', plain,
% 21.27/21.46      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('sup-', [status(thm)], ['68', '69'])).
% 21.27/21.46  thf(t3_xboole_1, axiom,
% 21.27/21.46    (![A:$i]:
% 21.27/21.46     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 21.27/21.46  thf('71', plain,
% 21.27/21.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 21.27/21.46      inference('cnf', [status(esa)], [t3_xboole_1])).
% 21.27/21.46  thf('72', plain,
% 21.27/21.46      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('sup-', [status(thm)], ['70', '71'])).
% 21.27/21.46  thf('73', plain,
% 21.27/21.46      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('split', [status(esa)], ['59'])).
% 21.27/21.46  thf('74', plain, ((r1_tarski @ sk_C @ sk_A)),
% 21.27/21.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.46  thf('75', plain,
% 21.27/21.46      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('sup+', [status(thm)], ['73', '74'])).
% 21.27/21.46  thf('76', plain,
% 21.27/21.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 21.27/21.46      inference('cnf', [status(esa)], [t3_xboole_1])).
% 21.27/21.46  thf('77', plain,
% 21.27/21.46      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('sup-', [status(thm)], ['75', '76'])).
% 21.27/21.46  thf('78', plain,
% 21.27/21.46      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('sup-', [status(thm)], ['70', '71'])).
% 21.27/21.46  thf('79', plain, ((v1_funct_1 @ sk_D)),
% 21.27/21.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.27/21.46  thf('80', plain,
% 21.27/21.46      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('sup+', [status(thm)], ['78', '79'])).
% 21.27/21.46  thf(t88_relat_1, axiom,
% 21.27/21.46    (![A:$i,B:$i]:
% 21.27/21.46     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 21.27/21.46  thf('81', plain,
% 21.27/21.46      (![X15 : $i, X16 : $i]:
% 21.27/21.46         ((r1_tarski @ (k7_relat_1 @ X15 @ X16) @ X15) | ~ (v1_relat_1 @ X15))),
% 21.27/21.46      inference('cnf', [status(esa)], [t88_relat_1])).
% 21.27/21.46  thf('82', plain,
% 21.27/21.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 21.27/21.46      inference('cnf', [status(esa)], [t3_xboole_1])).
% 21.27/21.46  thf('83', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         (~ (v1_relat_1 @ k1_xboole_0)
% 21.27/21.46          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 21.27/21.46      inference('sup-', [status(thm)], ['81', '82'])).
% 21.27/21.46  thf('84', plain,
% 21.27/21.46      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 21.27/21.46      inference('simplify', [status(thm)], ['41'])).
% 21.27/21.46  thf(fc6_relat_1, axiom,
% 21.27/21.46    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 21.27/21.46  thf('85', plain,
% 21.27/21.46      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 21.27/21.46      inference('cnf', [status(esa)], [fc6_relat_1])).
% 21.27/21.46  thf('86', plain, ((v1_relat_1 @ k1_xboole_0)),
% 21.27/21.46      inference('sup+', [status(thm)], ['84', '85'])).
% 21.27/21.46  thf('87', plain,
% 21.27/21.46      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 21.27/21.46      inference('demod', [status(thm)], ['83', '86'])).
% 21.27/21.46  thf('88', plain,
% 21.27/21.46      (![X13 : $i, X14 : $i]:
% 21.27/21.46         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X13 @ X14)) @ X14)
% 21.27/21.46          | ~ (v1_relat_1 @ X13))),
% 21.27/21.46      inference('cnf', [status(esa)], [t87_relat_1])).
% 21.27/21.46  thf('89', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         ((r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 21.27/21.46          | ~ (v1_relat_1 @ k1_xboole_0))),
% 21.27/21.46      inference('sup+', [status(thm)], ['87', '88'])).
% 21.27/21.46  thf('90', plain, ((v1_relat_1 @ k1_xboole_0)),
% 21.27/21.46      inference('sup+', [status(thm)], ['84', '85'])).
% 21.27/21.46  thf('91', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 21.27/21.46      inference('demod', [status(thm)], ['89', '90'])).
% 21.27/21.46  thf('92', plain,
% 21.27/21.46      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 21.27/21.46      inference('demod', [status(thm)], ['83', '86'])).
% 21.27/21.46  thf('93', plain,
% 21.27/21.46      (![X13 : $i, X14 : $i]:
% 21.27/21.46         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X13 @ X14)) @ X14)
% 21.27/21.46          | ~ (v1_relat_1 @ X13))),
% 21.27/21.46      inference('cnf', [status(esa)], [t87_relat_1])).
% 21.27/21.46  thf('94', plain,
% 21.27/21.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 21.27/21.46      inference('cnf', [status(esa)], [t3_xboole_1])).
% 21.27/21.46  thf('95', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         (~ (v1_relat_1 @ X0)
% 21.27/21.46          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 21.27/21.46      inference('sup-', [status(thm)], ['93', '94'])).
% 21.27/21.46  thf('96', plain,
% 21.27/21.46      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 21.27/21.46        | ~ (v1_relat_1 @ k1_xboole_0))),
% 21.27/21.46      inference('sup+', [status(thm)], ['92', '95'])).
% 21.27/21.46  thf('97', plain, ((v1_relat_1 @ k1_xboole_0)),
% 21.27/21.46      inference('sup+', [status(thm)], ['84', '85'])).
% 21.27/21.46  thf('98', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 21.27/21.46      inference('demod', [status(thm)], ['96', '97'])).
% 21.27/21.46  thf('99', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 21.27/21.46      inference('demod', [status(thm)], ['91', '98'])).
% 21.27/21.46  thf('100', plain,
% 21.27/21.46      (![X4 : $i, X6 : $i]:
% 21.27/21.46         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 21.27/21.46      inference('cnf', [status(esa)], [t3_subset])).
% 21.27/21.46  thf('101', plain,
% 21.27/21.46      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 21.27/21.46      inference('sup-', [status(thm)], ['99', '100'])).
% 21.27/21.46  thf('102', plain,
% 21.27/21.46      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 21.27/21.46         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 21.27/21.46          | ~ (v1_funct_1 @ X43)
% 21.27/21.46          | ((k2_partfun1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 21.27/21.46      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 21.27/21.46  thf('103', plain,
% 21.27/21.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.27/21.46         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 21.27/21.46            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 21.27/21.46          | ~ (v1_funct_1 @ k1_xboole_0))),
% 21.27/21.46      inference('sup-', [status(thm)], ['101', '102'])).
% 21.27/21.46  thf('104', plain,
% 21.27/21.46      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 21.27/21.46      inference('demod', [status(thm)], ['83', '86'])).
% 21.27/21.46  thf('105', plain,
% 21.27/21.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.27/21.46         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 21.27/21.46          | ~ (v1_funct_1 @ k1_xboole_0))),
% 21.27/21.46      inference('demod', [status(thm)], ['103', '104'])).
% 21.27/21.46  thf('106', plain,
% 21.27/21.46      ((![X0 : $i, X1 : $i, X2 : $i]:
% 21.27/21.46          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 21.27/21.46         <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('sup-', [status(thm)], ['80', '105'])).
% 21.27/21.46  thf('107', plain,
% 21.27/21.46      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('sup-', [status(thm)], ['75', '76'])).
% 21.27/21.46  thf('108', plain,
% 21.27/21.46      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 21.27/21.46      inference('simplify', [status(thm)], ['41'])).
% 21.27/21.46  thf('109', plain,
% 21.27/21.46      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 21.27/21.46      inference('sup-', [status(thm)], ['99', '100'])).
% 21.27/21.46  thf('110', plain,
% 21.27/21.46      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('split', [status(esa)], ['59'])).
% 21.27/21.46  thf('111', plain,
% 21.27/21.46      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('sup-', [status(thm)], ['70', '71'])).
% 21.27/21.46  thf('112', plain,
% 21.27/21.46      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('sup-', [status(thm)], ['75', '76'])).
% 21.27/21.46  thf('113', plain,
% 21.27/21.46      ((![X0 : $i, X1 : $i, X2 : $i]:
% 21.27/21.46          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 21.27/21.46         <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('sup-', [status(thm)], ['80', '105'])).
% 21.27/21.46  thf('114', plain,
% 21.27/21.46      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 21.27/21.46      inference('sup-', [status(thm)], ['75', '76'])).
% 21.27/21.46  thf('115', plain,
% 21.27/21.46      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 21.27/21.46      inference('sup-', [status(thm)], ['99', '100'])).
% 21.27/21.46  thf('116', plain,
% 21.27/21.46      (![X25 : $i, X26 : $i, X27 : $i]:
% 21.27/21.46         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 21.27/21.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 21.27/21.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 21.27/21.46  thf('117', plain,
% 21.27/21.46      (![X0 : $i, X1 : $i]:
% 21.27/21.46         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 21.27/21.46      inference('sup-', [status(thm)], ['115', '116'])).
% 21.27/21.46  thf('118', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 21.27/21.46      inference('demod', [status(thm)], ['96', '97'])).
% 21.27/21.46  thf('119', plain,
% 21.27/21.46      (![X0 : $i, X1 : $i]:
% 21.27/21.46         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 21.27/21.46      inference('demod', [status(thm)], ['117', '118'])).
% 21.27/21.46  thf('120', plain,
% 21.27/21.46      (![X33 : $i, X34 : $i, X35 : $i]:
% 21.27/21.46         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 21.27/21.46          | (v1_funct_2 @ X35 @ X33 @ X34)
% 21.27/21.46          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 21.27/21.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 21.27/21.46  thf('121', plain,
% 21.27/21.46      (![X0 : $i, X1 : $i]:
% 21.27/21.46         (((X1) != (k1_xboole_0))
% 21.27/21.46          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 21.27/21.46          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 21.27/21.46      inference('sup-', [status(thm)], ['119', '120'])).
% 21.27/21.46  thf('122', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 21.27/21.46          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 21.27/21.46      inference('simplify', [status(thm)], ['121'])).
% 21.27/21.46  thf('123', plain,
% 21.27/21.46      (![X31 : $i, X32 : $i]:
% 21.27/21.46         ((zip_tseitin_0 @ X31 @ X32) | ((X32) != (k1_xboole_0)))),
% 21.27/21.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 21.27/21.46  thf('124', plain, (![X31 : $i]: (zip_tseitin_0 @ X31 @ k1_xboole_0)),
% 21.27/21.46      inference('simplify', [status(thm)], ['123'])).
% 21.27/21.46  thf('125', plain,
% 21.27/21.46      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 21.27/21.46      inference('sup-', [status(thm)], ['99', '100'])).
% 21.27/21.46  thf('126', plain,
% 21.27/21.46      (![X36 : $i, X37 : $i, X38 : $i]:
% 21.27/21.46         (~ (zip_tseitin_0 @ X36 @ X37)
% 21.27/21.46          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 21.27/21.46          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 21.27/21.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 21.27/21.46  thf('127', plain,
% 21.27/21.46      (![X0 : $i, X1 : $i]:
% 21.27/21.46         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 21.27/21.46      inference('sup-', [status(thm)], ['125', '126'])).
% 21.27/21.46  thf('128', plain,
% 21.27/21.46      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 21.27/21.46      inference('sup-', [status(thm)], ['124', '127'])).
% 21.27/21.46  thf('129', plain,
% 21.27/21.46      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 21.27/21.46      inference('demod', [status(thm)], ['122', '128'])).
% 21.27/21.46  thf('130', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 21.27/21.46      inference('demod', [status(thm)],
% 21.27/21.46                ['63', '72', '77', '106', '107', '108', '109', '110', '111', 
% 21.27/21.46                 '112', '113', '114', '129'])).
% 21.27/21.46  thf('131', plain,
% 21.27/21.46      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 21.27/21.46      inference('split', [status(esa)], ['59'])).
% 21.27/21.46  thf('132', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 21.27/21.46      inference('sat_resolution*', [status(thm)], ['130', '131'])).
% 21.27/21.46  thf('133', plain, (((sk_B) != (k1_xboole_0))),
% 21.27/21.46      inference('simpl_trail', [status(thm)], ['60', '132'])).
% 21.27/21.46  thf('134', plain,
% 21.27/21.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.27/21.46      inference('simplify_reflect-', [status(thm)], ['58', '133'])).
% 21.27/21.46  thf('135', plain,
% 21.27/21.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.27/21.46      inference('simplify_reflect-', [status(thm)], ['58', '133'])).
% 21.27/21.46  thf('136', plain,
% 21.27/21.46      (![X0 : $i, X1 : $i]:
% 21.27/21.46         (((X1) = (X0))
% 21.27/21.46          | ((sk_A) = (k1_relat_1 @ sk_D))
% 21.27/21.46          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.27/21.46      inference('sup+', [status(thm)], ['134', '135'])).
% 21.27/21.46  thf('137', plain,
% 21.27/21.46      (![X0 : $i, X1 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ((X1) = (X0)))),
% 21.27/21.46      inference('simplify', [status(thm)], ['136'])).
% 21.27/21.46  thf('138', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 21.27/21.46      inference('condensation', [status(thm)], ['137'])).
% 21.27/21.46  thf(t91_relat_1, axiom,
% 21.27/21.46    (![A:$i,B:$i]:
% 21.27/21.46     ( ( v1_relat_1 @ B ) =>
% 21.27/21.46       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 21.27/21.46         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 21.27/21.46  thf('139', plain,
% 21.27/21.46      (![X17 : $i, X18 : $i]:
% 21.27/21.46         (~ (r1_tarski @ X17 @ (k1_relat_1 @ X18))
% 21.27/21.46          | ((k1_relat_1 @ (k7_relat_1 @ X18 @ X17)) = (X17))
% 21.27/21.46          | ~ (v1_relat_1 @ X18))),
% 21.27/21.46      inference('cnf', [status(esa)], [t91_relat_1])).
% 21.27/21.46  thf('140', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         (~ (r1_tarski @ X0 @ sk_A)
% 21.27/21.46          | ~ (v1_relat_1 @ sk_D)
% 21.27/21.46          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 21.27/21.46      inference('sup-', [status(thm)], ['138', '139'])).
% 21.27/21.46  thf('141', plain, ((v1_relat_1 @ sk_D)),
% 21.27/21.46      inference('sup-', [status(thm)], ['34', '35'])).
% 21.27/21.46  thf('142', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         (~ (r1_tarski @ X0 @ sk_A)
% 21.27/21.46          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 21.27/21.46      inference('demod', [status(thm)], ['140', '141'])).
% 21.27/21.46  thf('143', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 21.27/21.46      inference('sup-', [status(thm)], ['39', '142'])).
% 21.27/21.46  thf('144', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 21.27/21.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 21.27/21.46      inference('demod', [status(thm)], ['32', '33', '36'])).
% 21.27/21.46  thf('145', plain,
% 21.27/21.46      (![X25 : $i, X26 : $i, X27 : $i]:
% 21.27/21.46         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 21.27/21.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 21.27/21.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 21.27/21.46  thf('146', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         ((k1_relset_1 @ X0 @ sk_B @ (k7_relat_1 @ sk_D @ X0))
% 21.27/21.46           = (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 21.27/21.46      inference('sup-', [status(thm)], ['144', '145'])).
% 21.27/21.46  thf('147', plain,
% 21.27/21.46      (![X33 : $i, X34 : $i, X35 : $i]:
% 21.27/21.46         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 21.27/21.46          | (v1_funct_2 @ X35 @ X33 @ X34)
% 21.27/21.46          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 21.27/21.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 21.27/21.46  thf('148', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 21.27/21.46          | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 21.27/21.46          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 21.27/21.46      inference('sup-', [status(thm)], ['146', '147'])).
% 21.27/21.46  thf('149', plain,
% 21.27/21.46      (![X31 : $i, X32 : $i]:
% 21.27/21.46         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 21.27/21.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 21.27/21.46  thf('150', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 21.27/21.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 21.27/21.46      inference('demod', [status(thm)], ['32', '33', '36'])).
% 21.27/21.46  thf('151', plain,
% 21.27/21.46      (![X36 : $i, X37 : $i, X38 : $i]:
% 21.27/21.46         (~ (zip_tseitin_0 @ X36 @ X37)
% 21.27/21.46          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 21.27/21.46          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 21.27/21.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 21.27/21.46  thf('152', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 21.27/21.46          | ~ (zip_tseitin_0 @ sk_B @ X0))),
% 21.27/21.46      inference('sup-', [status(thm)], ['150', '151'])).
% 21.27/21.46  thf('153', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         (((sk_B) = (k1_xboole_0))
% 21.27/21.46          | (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0))),
% 21.27/21.46      inference('sup-', [status(thm)], ['149', '152'])).
% 21.27/21.46  thf('154', plain, (((sk_B) != (k1_xboole_0))),
% 21.27/21.46      inference('simpl_trail', [status(thm)], ['60', '132'])).
% 21.27/21.46  thf('155', plain,
% 21.27/21.46      (![X0 : $i]: (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)),
% 21.27/21.46      inference('simplify_reflect-', [status(thm)], ['153', '154'])).
% 21.27/21.46  thf('156', plain,
% 21.27/21.46      (![X0 : $i]:
% 21.27/21.46         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 21.27/21.46          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 21.27/21.46      inference('demod', [status(thm)], ['148', '155'])).
% 21.27/21.46  thf('157', plain,
% 21.27/21.46      ((((sk_C) != (sk_C))
% 21.27/21.46        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 21.27/21.46      inference('sup-', [status(thm)], ['143', '156'])).
% 21.27/21.46  thf('158', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 21.27/21.46      inference('simplify', [status(thm)], ['157'])).
% 21.27/21.46  thf('159', plain, ($false), inference('demod', [status(thm)], ['38', '158'])).
% 21.27/21.46  
% 21.27/21.46  % SZS output end Refutation
% 21.27/21.46  
% 21.27/21.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
