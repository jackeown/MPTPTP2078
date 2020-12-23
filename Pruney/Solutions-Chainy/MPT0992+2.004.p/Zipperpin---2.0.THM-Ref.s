%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dJ6IdyTLjy

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:35 EST 2020

% Result     : Theorem 17.55s
% Output     : Refutation 17.55s
% Verified   : 
% Statistics : Number of formulae       :  225 (1962 expanded)
%              Number of leaves         :   42 ( 591 expanded)
%              Depth                    :   27
%              Number of atoms          : 1691 (22382 expanded)
%              Number of equality atoms :  135 (1523 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
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

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X41 @ X42 @ X40 @ X43 ) ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ( ( k2_partfun1 @ X45 @ X46 @ X44 @ X47 )
        = ( k7_relat_1 @ X44 @ X47 ) ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X41 @ X42 @ X40 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X31 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('42',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','52'])).

thf('54',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','51'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','52'])).

thf('59',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('60',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','51'])).

thf('64',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['40','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('69',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('73',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_B
        = ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['66','75'])).

thf('77',plain,(
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

thf('78',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('79',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('83',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('85',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('86',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('90',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('91',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','93'])).

thf('95',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['95'])).

thf('97',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['95'])).

thf('98',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('99',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['95'])).

thf('101',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('104',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','104'])).

thf('106',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('107',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('109',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['95'])).

thf('111',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('114',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('116',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('119',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('120',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ( ( k2_partfun1 @ X45 @ X46 @ X44 @ X47 )
        = ( k7_relat_1 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','52'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['117','124'])).

thf('126',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('127',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('128',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('129',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['95'])).

thf('130',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('131',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('132',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['117','124'])).

thf('133',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('134',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('135',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X33 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('143',plain,(
    ! [X32: $i] :
      ( zip_tseitin_0 @ X32 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('145',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['143','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['141','147'])).

thf('149',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['99','109','114','125','126','127','128','129','130','131','132','133','148'])).

thf('150',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['95'])).

thf('151',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['149','150'])).

thf('152',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['96','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','152'])).

thf('154',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('155',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('157',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['155','156'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('158',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['39','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('164',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ sk_B @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('169',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ~ ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_B
        = ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['66','75'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X1 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['96','151'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(condensation,[status(thm)],['175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 ) ),
    inference(demod,[status(thm)],['170','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['167','177'])).

thf('179',plain,
    ( ( sk_C != sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['162','178'])).

thf('180',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    $false ),
    inference(demod,[status(thm)],['38','180'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dJ6IdyTLjy
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 17.55/17.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.55/17.80  % Solved by: fo/fo7.sh
% 17.55/17.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.55/17.80  % done 14484 iterations in 17.330s
% 17.55/17.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.55/17.80  % SZS output start Refutation
% 17.55/17.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 17.55/17.80  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 17.55/17.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 17.55/17.80  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 17.55/17.80  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 17.55/17.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 17.55/17.80  thf(sk_D_type, type, sk_D: $i).
% 17.55/17.80  thf(sk_C_type, type, sk_C: $i).
% 17.55/17.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 17.55/17.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 17.55/17.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 17.55/17.80  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 17.55/17.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 17.55/17.80  thf(sk_A_type, type, sk_A: $i).
% 17.55/17.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 17.55/17.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.55/17.80  thf(sk_B_type, type, sk_B: $i).
% 17.55/17.80  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 17.55/17.80  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 17.55/17.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 17.55/17.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 17.55/17.80  thf(t38_funct_2, conjecture,
% 17.55/17.80    (![A:$i,B:$i,C:$i,D:$i]:
% 17.55/17.80     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 17.55/17.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.55/17.80       ( ( r1_tarski @ C @ A ) =>
% 17.55/17.80         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 17.55/17.80           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 17.55/17.80             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 17.55/17.80             ( m1_subset_1 @
% 17.55/17.80               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 17.55/17.80               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 17.55/17.80  thf(zf_stmt_0, negated_conjecture,
% 17.55/17.80    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 17.55/17.80        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 17.55/17.80            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.55/17.80          ( ( r1_tarski @ C @ A ) =>
% 17.55/17.80            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 17.55/17.80              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 17.55/17.80                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 17.55/17.80                ( m1_subset_1 @
% 17.55/17.80                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 17.55/17.80                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 17.55/17.80    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 17.55/17.80  thf('0', plain,
% 17.55/17.80      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 17.55/17.80        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 17.55/17.80             sk_B)
% 17.55/17.80        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 17.55/17.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 17.55/17.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.80  thf('1', plain,
% 17.55/17.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.55/17.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.80  thf(dt_k2_partfun1, axiom,
% 17.55/17.80    (![A:$i,B:$i,C:$i,D:$i]:
% 17.55/17.80     ( ( ( v1_funct_1 @ C ) & 
% 17.55/17.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.55/17.80       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 17.55/17.80         ( m1_subset_1 @
% 17.55/17.80           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 17.55/17.80           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 17.55/17.80  thf('2', plain,
% 17.55/17.80      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 17.55/17.80         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 17.55/17.80          | ~ (v1_funct_1 @ X40)
% 17.55/17.80          | (v1_funct_1 @ (k2_partfun1 @ X41 @ X42 @ X40 @ X43)))),
% 17.55/17.80      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 17.55/17.80  thf('3', plain,
% 17.55/17.80      (![X0 : $i]:
% 17.55/17.80         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 17.55/17.80          | ~ (v1_funct_1 @ sk_D))),
% 17.55/17.80      inference('sup-', [status(thm)], ['1', '2'])).
% 17.55/17.80  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 17.55/17.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.80  thf('5', plain,
% 17.55/17.80      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 17.55/17.80      inference('demod', [status(thm)], ['3', '4'])).
% 17.55/17.80  thf('6', plain,
% 17.55/17.80      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 17.55/17.80        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 17.55/17.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 17.55/17.80      inference('demod', [status(thm)], ['0', '5'])).
% 17.55/17.80  thf('7', plain,
% 17.55/17.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.55/17.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.80  thf(redefinition_k2_partfun1, axiom,
% 17.55/17.80    (![A:$i,B:$i,C:$i,D:$i]:
% 17.55/17.80     ( ( ( v1_funct_1 @ C ) & 
% 17.55/17.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.55/17.80       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 17.55/17.80  thf('8', plain,
% 17.55/17.80      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 17.55/17.80         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 17.55/17.80          | ~ (v1_funct_1 @ X44)
% 17.55/17.80          | ((k2_partfun1 @ X45 @ X46 @ X44 @ X47) = (k7_relat_1 @ X44 @ X47)))),
% 17.55/17.80      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 17.55/17.80  thf('9', plain,
% 17.55/17.80      (![X0 : $i]:
% 17.55/17.80         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 17.55/17.80          | ~ (v1_funct_1 @ sk_D))),
% 17.55/17.80      inference('sup-', [status(thm)], ['7', '8'])).
% 17.55/17.80  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 17.55/17.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.80  thf('11', plain,
% 17.55/17.80      (![X0 : $i]:
% 17.55/17.80         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 17.55/17.80      inference('demod', [status(thm)], ['9', '10'])).
% 17.55/17.80  thf('12', plain,
% 17.55/17.80      (![X0 : $i]:
% 17.55/17.80         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 17.55/17.80      inference('demod', [status(thm)], ['9', '10'])).
% 17.55/17.80  thf('13', plain,
% 17.55/17.80      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 17.55/17.80        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 17.55/17.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 17.55/17.80      inference('demod', [status(thm)], ['6', '11', '12'])).
% 17.55/17.80  thf('14', plain,
% 17.55/17.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.55/17.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.80  thf('15', plain,
% 17.55/17.80      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 17.55/17.80         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 17.55/17.80          | ~ (v1_funct_1 @ X40)
% 17.55/17.80          | (m1_subset_1 @ (k2_partfun1 @ X41 @ X42 @ X40 @ X43) @ 
% 17.55/17.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 17.55/17.80      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 17.55/17.80  thf('16', plain,
% 17.55/17.80      (![X0 : $i]:
% 17.55/17.80         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 17.55/17.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 17.55/17.80          | ~ (v1_funct_1 @ sk_D))),
% 17.55/17.80      inference('sup-', [status(thm)], ['14', '15'])).
% 17.55/17.80  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 17.55/17.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.80  thf('18', plain,
% 17.55/17.80      (![X0 : $i]:
% 17.55/17.80         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 17.55/17.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.55/17.80      inference('demod', [status(thm)], ['16', '17'])).
% 17.55/17.80  thf('19', plain,
% 17.55/17.80      (![X0 : $i]:
% 17.55/17.80         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 17.55/17.80      inference('demod', [status(thm)], ['9', '10'])).
% 17.55/17.80  thf('20', plain,
% 17.55/17.80      (![X0 : $i]:
% 17.55/17.80         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 17.55/17.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.55/17.80      inference('demod', [status(thm)], ['18', '19'])).
% 17.55/17.80  thf(cc2_relset_1, axiom,
% 17.55/17.80    (![A:$i,B:$i,C:$i]:
% 17.55/17.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.55/17.80       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 17.55/17.80  thf('21', plain,
% 17.55/17.80      (![X23 : $i, X24 : $i, X25 : $i]:
% 17.55/17.80         ((v5_relat_1 @ X23 @ X25)
% 17.55/17.80          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 17.55/17.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 17.55/17.80  thf('22', plain,
% 17.55/17.80      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 17.55/17.80      inference('sup-', [status(thm)], ['20', '21'])).
% 17.55/17.80  thf(d19_relat_1, axiom,
% 17.55/17.80    (![A:$i,B:$i]:
% 17.55/17.80     ( ( v1_relat_1 @ B ) =>
% 17.55/17.80       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 17.55/17.80  thf('23', plain,
% 17.55/17.80      (![X12 : $i, X13 : $i]:
% 17.55/17.80         (~ (v5_relat_1 @ X12 @ X13)
% 17.55/17.80          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 17.55/17.80          | ~ (v1_relat_1 @ X12))),
% 17.55/17.80      inference('cnf', [status(esa)], [d19_relat_1])).
% 17.55/17.80  thf('24', plain,
% 17.55/17.80      (![X0 : $i]:
% 17.55/17.80         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 17.55/17.80          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 17.55/17.80      inference('sup-', [status(thm)], ['22', '23'])).
% 17.55/17.80  thf('25', plain,
% 17.55/17.80      (![X0 : $i]:
% 17.55/17.80         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 17.55/17.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.55/17.80      inference('demod', [status(thm)], ['18', '19'])).
% 17.55/17.80  thf(cc1_relset_1, axiom,
% 17.55/17.80    (![A:$i,B:$i,C:$i]:
% 17.55/17.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.55/17.80       ( v1_relat_1 @ C ) ))).
% 17.55/17.80  thf('26', plain,
% 17.55/17.80      (![X20 : $i, X21 : $i, X22 : $i]:
% 17.55/17.80         ((v1_relat_1 @ X20)
% 17.55/17.80          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 17.55/17.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 17.55/17.80  thf('27', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 17.55/17.80      inference('sup-', [status(thm)], ['25', '26'])).
% 17.55/17.80  thf('28', plain,
% 17.55/17.80      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 17.55/17.81      inference('demod', [status(thm)], ['24', '27'])).
% 17.55/17.81  thf(t87_relat_1, axiom,
% 17.55/17.81    (![A:$i,B:$i]:
% 17.55/17.81     ( ( v1_relat_1 @ B ) =>
% 17.55/17.81       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 17.55/17.81  thf('29', plain,
% 17.55/17.81      (![X14 : $i, X15 : $i]:
% 17.55/17.81         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X14 @ X15)) @ X15)
% 17.55/17.81          | ~ (v1_relat_1 @ X14))),
% 17.55/17.81      inference('cnf', [status(esa)], [t87_relat_1])).
% 17.55/17.81  thf(t11_relset_1, axiom,
% 17.55/17.81    (![A:$i,B:$i,C:$i]:
% 17.55/17.81     ( ( v1_relat_1 @ C ) =>
% 17.55/17.81       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 17.55/17.81           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 17.55/17.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 17.55/17.81  thf('30', plain,
% 17.55/17.81      (![X29 : $i, X30 : $i, X31 : $i]:
% 17.55/17.81         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 17.55/17.81          | ~ (r1_tarski @ (k2_relat_1 @ X29) @ X31)
% 17.55/17.81          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 17.55/17.81          | ~ (v1_relat_1 @ X29))),
% 17.55/17.81      inference('cnf', [status(esa)], [t11_relset_1])).
% 17.55/17.81  thf('31', plain,
% 17.55/17.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.55/17.81         (~ (v1_relat_1 @ X1)
% 17.55/17.81          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 17.55/17.81          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 17.55/17.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 17.55/17.81          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 17.55/17.81      inference('sup-', [status(thm)], ['29', '30'])).
% 17.55/17.81  thf('32', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 17.55/17.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 17.55/17.81          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 17.55/17.81          | ~ (v1_relat_1 @ sk_D))),
% 17.55/17.81      inference('sup-', [status(thm)], ['28', '31'])).
% 17.55/17.81  thf('33', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 17.55/17.81      inference('sup-', [status(thm)], ['25', '26'])).
% 17.55/17.81  thf('34', plain,
% 17.55/17.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.81  thf('35', plain,
% 17.55/17.81      (![X20 : $i, X21 : $i, X22 : $i]:
% 17.55/17.81         ((v1_relat_1 @ X20)
% 17.55/17.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 17.55/17.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 17.55/17.81  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 17.55/17.81      inference('sup-', [status(thm)], ['34', '35'])).
% 17.55/17.81  thf('37', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 17.55/17.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 17.55/17.81      inference('demod', [status(thm)], ['32', '33', '36'])).
% 17.55/17.81  thf('38', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 17.55/17.81      inference('demod', [status(thm)], ['13', '37'])).
% 17.55/17.81  thf('39', plain, ((r1_tarski @ sk_C @ sk_A)),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.81  thf(d1_funct_2, axiom,
% 17.55/17.81    (![A:$i,B:$i,C:$i]:
% 17.55/17.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.55/17.81       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 17.55/17.81           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 17.55/17.81             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 17.55/17.81         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 17.55/17.81           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 17.55/17.81             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 17.55/17.81  thf(zf_stmt_1, axiom,
% 17.55/17.81    (![B:$i,A:$i]:
% 17.55/17.81     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 17.55/17.81       ( zip_tseitin_0 @ B @ A ) ))).
% 17.55/17.81  thf('40', plain,
% 17.55/17.81      (![X32 : $i, X33 : $i]:
% 17.55/17.81         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 17.55/17.81  thf(t88_relat_1, axiom,
% 17.55/17.81    (![A:$i,B:$i]:
% 17.55/17.81     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 17.55/17.81  thf('41', plain,
% 17.55/17.81      (![X16 : $i, X17 : $i]:
% 17.55/17.81         ((r1_tarski @ (k7_relat_1 @ X16 @ X17) @ X16) | ~ (v1_relat_1 @ X16))),
% 17.55/17.81      inference('cnf', [status(esa)], [t88_relat_1])).
% 17.55/17.81  thf(t3_xboole_1, axiom,
% 17.55/17.81    (![A:$i]:
% 17.55/17.81     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 17.55/17.81  thf('42', plain,
% 17.55/17.81      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 17.55/17.81      inference('cnf', [status(esa)], [t3_xboole_1])).
% 17.55/17.81  thf('43', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         (~ (v1_relat_1 @ k1_xboole_0)
% 17.55/17.81          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 17.55/17.81      inference('sup-', [status(thm)], ['41', '42'])).
% 17.55/17.81  thf(t113_zfmisc_1, axiom,
% 17.55/17.81    (![A:$i,B:$i]:
% 17.55/17.81     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 17.55/17.81       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 17.55/17.81  thf('44', plain,
% 17.55/17.81      (![X5 : $i, X6 : $i]:
% 17.55/17.81         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 17.55/17.81      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 17.55/17.81  thf('45', plain,
% 17.55/17.81      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 17.55/17.81      inference('simplify', [status(thm)], ['44'])).
% 17.55/17.81  thf(d10_xboole_0, axiom,
% 17.55/17.81    (![A:$i,B:$i]:
% 17.55/17.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 17.55/17.81  thf('46', plain,
% 17.55/17.81      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 17.55/17.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 17.55/17.81  thf('47', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 17.55/17.81      inference('simplify', [status(thm)], ['46'])).
% 17.55/17.81  thf(t3_subset, axiom,
% 17.55/17.81    (![A:$i,B:$i]:
% 17.55/17.81     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 17.55/17.81  thf('48', plain,
% 17.55/17.81      (![X7 : $i, X9 : $i]:
% 17.55/17.81         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 17.55/17.81      inference('cnf', [status(esa)], [t3_subset])).
% 17.55/17.81  thf('49', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.55/17.81      inference('sup-', [status(thm)], ['47', '48'])).
% 17.55/17.81  thf('50', plain,
% 17.55/17.81      (![X20 : $i, X21 : $i, X22 : $i]:
% 17.55/17.81         ((v1_relat_1 @ X20)
% 17.55/17.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 17.55/17.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 17.55/17.81  thf('51', plain,
% 17.55/17.81      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 17.55/17.81      inference('sup-', [status(thm)], ['49', '50'])).
% 17.55/17.81  thf('52', plain, ((v1_relat_1 @ k1_xboole_0)),
% 17.55/17.81      inference('sup+', [status(thm)], ['45', '51'])).
% 17.55/17.81  thf('53', plain,
% 17.55/17.81      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 17.55/17.81      inference('demod', [status(thm)], ['43', '52'])).
% 17.55/17.81  thf('54', plain,
% 17.55/17.81      (![X14 : $i, X15 : $i]:
% 17.55/17.81         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X14 @ X15)) @ X15)
% 17.55/17.81          | ~ (v1_relat_1 @ X14))),
% 17.55/17.81      inference('cnf', [status(esa)], [t87_relat_1])).
% 17.55/17.81  thf('55', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         ((r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 17.55/17.81          | ~ (v1_relat_1 @ k1_xboole_0))),
% 17.55/17.81      inference('sup+', [status(thm)], ['53', '54'])).
% 17.55/17.81  thf('56', plain, ((v1_relat_1 @ k1_xboole_0)),
% 17.55/17.81      inference('sup+', [status(thm)], ['45', '51'])).
% 17.55/17.81  thf('57', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 17.55/17.81      inference('demod', [status(thm)], ['55', '56'])).
% 17.55/17.81  thf('58', plain,
% 17.55/17.81      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 17.55/17.81      inference('demod', [status(thm)], ['43', '52'])).
% 17.55/17.81  thf('59', plain,
% 17.55/17.81      (![X14 : $i, X15 : $i]:
% 17.55/17.81         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X14 @ X15)) @ X15)
% 17.55/17.81          | ~ (v1_relat_1 @ X14))),
% 17.55/17.81      inference('cnf', [status(esa)], [t87_relat_1])).
% 17.55/17.81  thf('60', plain,
% 17.55/17.81      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 17.55/17.81      inference('cnf', [status(esa)], [t3_xboole_1])).
% 17.55/17.81  thf('61', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         (~ (v1_relat_1 @ X0)
% 17.55/17.81          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 17.55/17.81      inference('sup-', [status(thm)], ['59', '60'])).
% 17.55/17.81  thf('62', plain,
% 17.55/17.81      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 17.55/17.81        | ~ (v1_relat_1 @ k1_xboole_0))),
% 17.55/17.81      inference('sup+', [status(thm)], ['58', '61'])).
% 17.55/17.81  thf('63', plain, ((v1_relat_1 @ k1_xboole_0)),
% 17.55/17.81      inference('sup+', [status(thm)], ['45', '51'])).
% 17.55/17.81  thf('64', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 17.55/17.81      inference('demod', [status(thm)], ['62', '63'])).
% 17.55/17.81  thf('65', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 17.55/17.81      inference('demod', [status(thm)], ['57', '64'])).
% 17.55/17.81  thf('66', plain,
% 17.55/17.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.55/17.81         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 17.55/17.81      inference('sup+', [status(thm)], ['40', '65'])).
% 17.55/17.81  thf('67', plain,
% 17.55/17.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.81  thf('68', plain,
% 17.55/17.81      (![X23 : $i, X24 : $i, X25 : $i]:
% 17.55/17.81         ((v5_relat_1 @ X23 @ X25)
% 17.55/17.81          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 17.55/17.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 17.55/17.81  thf('69', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 17.55/17.81      inference('sup-', [status(thm)], ['67', '68'])).
% 17.55/17.81  thf('70', plain,
% 17.55/17.81      (![X12 : $i, X13 : $i]:
% 17.55/17.81         (~ (v5_relat_1 @ X12 @ X13)
% 17.55/17.81          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 17.55/17.81          | ~ (v1_relat_1 @ X12))),
% 17.55/17.81      inference('cnf', [status(esa)], [d19_relat_1])).
% 17.55/17.81  thf('71', plain,
% 17.55/17.81      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 17.55/17.81      inference('sup-', [status(thm)], ['69', '70'])).
% 17.55/17.81  thf('72', plain, ((v1_relat_1 @ sk_D)),
% 17.55/17.81      inference('sup-', [status(thm)], ['34', '35'])).
% 17.55/17.81  thf('73', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 17.55/17.81      inference('demod', [status(thm)], ['71', '72'])).
% 17.55/17.81  thf('74', plain,
% 17.55/17.81      (![X0 : $i, X2 : $i]:
% 17.55/17.81         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 17.55/17.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 17.55/17.81  thf('75', plain,
% 17.55/17.81      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 17.55/17.81        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 17.55/17.81      inference('sup-', [status(thm)], ['73', '74'])).
% 17.55/17.81  thf('76', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         ((zip_tseitin_0 @ sk_B @ X0) | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 17.55/17.81      inference('sup-', [status(thm)], ['66', '75'])).
% 17.55/17.81  thf('77', plain,
% 17.55/17.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.81  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 17.55/17.81  thf(zf_stmt_3, axiom,
% 17.55/17.81    (![C:$i,B:$i,A:$i]:
% 17.55/17.81     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 17.55/17.81       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 17.55/17.81  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 17.55/17.81  thf(zf_stmt_5, axiom,
% 17.55/17.81    (![A:$i,B:$i,C:$i]:
% 17.55/17.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.55/17.81       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 17.55/17.81         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 17.55/17.81           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 17.55/17.81             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 17.55/17.81  thf('78', plain,
% 17.55/17.81      (![X37 : $i, X38 : $i, X39 : $i]:
% 17.55/17.81         (~ (zip_tseitin_0 @ X37 @ X38)
% 17.55/17.81          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 17.55/17.81          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 17.55/17.81  thf('79', plain,
% 17.55/17.81      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 17.55/17.81      inference('sup-', [status(thm)], ['77', '78'])).
% 17.55/17.81  thf('80', plain,
% 17.55/17.81      ((((sk_B) = (k2_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 17.55/17.81      inference('sup-', [status(thm)], ['76', '79'])).
% 17.55/17.81  thf('81', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.81  thf('82', plain,
% 17.55/17.81      (![X34 : $i, X35 : $i, X36 : $i]:
% 17.55/17.81         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 17.55/17.81          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 17.55/17.81          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 17.55/17.81  thf('83', plain,
% 17.55/17.81      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 17.55/17.81        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 17.55/17.81      inference('sup-', [status(thm)], ['81', '82'])).
% 17.55/17.81  thf('84', plain,
% 17.55/17.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.81  thf(redefinition_k1_relset_1, axiom,
% 17.55/17.81    (![A:$i,B:$i,C:$i]:
% 17.55/17.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.55/17.81       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 17.55/17.81  thf('85', plain,
% 17.55/17.81      (![X26 : $i, X27 : $i, X28 : $i]:
% 17.55/17.81         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 17.55/17.81          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 17.55/17.81      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 17.55/17.81  thf('86', plain,
% 17.55/17.81      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 17.55/17.81      inference('sup-', [status(thm)], ['84', '85'])).
% 17.55/17.81  thf('87', plain,
% 17.55/17.81      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 17.55/17.81      inference('demod', [status(thm)], ['83', '86'])).
% 17.55/17.81  thf('88', plain,
% 17.55/17.81      ((((sk_B) = (k2_relat_1 @ sk_D)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 17.55/17.81      inference('sup-', [status(thm)], ['80', '87'])).
% 17.55/17.81  thf('89', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 17.55/17.81      inference('demod', [status(thm)], ['71', '72'])).
% 17.55/17.81  thf('90', plain,
% 17.55/17.81      (![X32 : $i, X33 : $i]:
% 17.55/17.81         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 17.55/17.81  thf('91', plain,
% 17.55/17.81      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 17.55/17.81      inference('cnf', [status(esa)], [t3_xboole_1])).
% 17.55/17.81  thf('92', plain,
% 17.55/17.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.55/17.81         (~ (r1_tarski @ X1 @ X0)
% 17.55/17.81          | (zip_tseitin_0 @ X0 @ X2)
% 17.55/17.81          | ((X1) = (k1_xboole_0)))),
% 17.55/17.81      inference('sup-', [status(thm)], ['90', '91'])).
% 17.55/17.81  thf('93', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B @ X0))),
% 17.55/17.81      inference('sup-', [status(thm)], ['89', '92'])).
% 17.55/17.81  thf('94', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         (((sk_B) = (k1_xboole_0))
% 17.55/17.81          | ((sk_A) = (k1_relat_1 @ sk_D))
% 17.55/17.81          | (zip_tseitin_0 @ sk_B @ X0))),
% 17.55/17.81      inference('sup+', [status(thm)], ['88', '93'])).
% 17.55/17.81  thf('95', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.81  thf('96', plain,
% 17.55/17.81      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 17.55/17.81      inference('split', [status(esa)], ['95'])).
% 17.55/17.81  thf('97', plain,
% 17.55/17.81      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('split', [status(esa)], ['95'])).
% 17.55/17.81  thf('98', plain,
% 17.55/17.81      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 17.55/17.81        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 17.55/17.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 17.55/17.81      inference('demod', [status(thm)], ['0', '5'])).
% 17.55/17.81  thf('99', plain,
% 17.55/17.81      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 17.55/17.81            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 17.55/17.81         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 17.55/17.81              sk_B)))
% 17.55/17.81         <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('sup-', [status(thm)], ['97', '98'])).
% 17.55/17.81  thf('100', plain,
% 17.55/17.81      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('split', [status(esa)], ['95'])).
% 17.55/17.81  thf('101', plain,
% 17.55/17.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.81  thf('102', plain,
% 17.55/17.81      (((m1_subset_1 @ sk_D @ 
% 17.55/17.81         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 17.55/17.81         <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('sup+', [status(thm)], ['100', '101'])).
% 17.55/17.81  thf('103', plain,
% 17.55/17.81      (![X5 : $i, X6 : $i]:
% 17.55/17.81         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 17.55/17.81      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 17.55/17.81  thf('104', plain,
% 17.55/17.81      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 17.55/17.81      inference('simplify', [status(thm)], ['103'])).
% 17.55/17.81  thf('105', plain,
% 17.55/17.81      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 17.55/17.81         <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('demod', [status(thm)], ['102', '104'])).
% 17.55/17.81  thf('106', plain,
% 17.55/17.81      (![X7 : $i, X8 : $i]:
% 17.55/17.81         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 17.55/17.81      inference('cnf', [status(esa)], [t3_subset])).
% 17.55/17.81  thf('107', plain,
% 17.55/17.81      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('sup-', [status(thm)], ['105', '106'])).
% 17.55/17.81  thf('108', plain,
% 17.55/17.81      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 17.55/17.81      inference('cnf', [status(esa)], [t3_xboole_1])).
% 17.55/17.81  thf('109', plain,
% 17.55/17.81      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('sup-', [status(thm)], ['107', '108'])).
% 17.55/17.81  thf('110', plain,
% 17.55/17.81      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('split', [status(esa)], ['95'])).
% 17.55/17.81  thf('111', plain, ((r1_tarski @ sk_C @ sk_A)),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.81  thf('112', plain,
% 17.55/17.81      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('sup+', [status(thm)], ['110', '111'])).
% 17.55/17.81  thf('113', plain,
% 17.55/17.81      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 17.55/17.81      inference('cnf', [status(esa)], [t3_xboole_1])).
% 17.55/17.81  thf('114', plain,
% 17.55/17.81      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('sup-', [status(thm)], ['112', '113'])).
% 17.55/17.81  thf('115', plain,
% 17.55/17.81      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('sup-', [status(thm)], ['107', '108'])).
% 17.55/17.81  thf('116', plain, ((v1_funct_1 @ sk_D)),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.81  thf('117', plain,
% 17.55/17.81      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('sup+', [status(thm)], ['115', '116'])).
% 17.55/17.81  thf('118', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 17.55/17.81      inference('demod', [status(thm)], ['57', '64'])).
% 17.55/17.81  thf('119', plain,
% 17.55/17.81      (![X7 : $i, X9 : $i]:
% 17.55/17.81         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 17.55/17.81      inference('cnf', [status(esa)], [t3_subset])).
% 17.55/17.81  thf('120', plain,
% 17.55/17.81      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 17.55/17.81      inference('sup-', [status(thm)], ['118', '119'])).
% 17.55/17.81  thf('121', plain,
% 17.55/17.81      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 17.55/17.81         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 17.55/17.81          | ~ (v1_funct_1 @ X44)
% 17.55/17.81          | ((k2_partfun1 @ X45 @ X46 @ X44 @ X47) = (k7_relat_1 @ X44 @ X47)))),
% 17.55/17.81      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 17.55/17.81  thf('122', plain,
% 17.55/17.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.55/17.81         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 17.55/17.81            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 17.55/17.81          | ~ (v1_funct_1 @ k1_xboole_0))),
% 17.55/17.81      inference('sup-', [status(thm)], ['120', '121'])).
% 17.55/17.81  thf('123', plain,
% 17.55/17.81      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 17.55/17.81      inference('demod', [status(thm)], ['43', '52'])).
% 17.55/17.81  thf('124', plain,
% 17.55/17.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.55/17.81         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 17.55/17.81          | ~ (v1_funct_1 @ k1_xboole_0))),
% 17.55/17.81      inference('demod', [status(thm)], ['122', '123'])).
% 17.55/17.81  thf('125', plain,
% 17.55/17.81      ((![X0 : $i, X1 : $i, X2 : $i]:
% 17.55/17.81          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 17.55/17.81         <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('sup-', [status(thm)], ['117', '124'])).
% 17.55/17.81  thf('126', plain,
% 17.55/17.81      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('sup-', [status(thm)], ['112', '113'])).
% 17.55/17.81  thf('127', plain,
% 17.55/17.81      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 17.55/17.81      inference('simplify', [status(thm)], ['103'])).
% 17.55/17.81  thf('128', plain,
% 17.55/17.81      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 17.55/17.81      inference('sup-', [status(thm)], ['118', '119'])).
% 17.55/17.81  thf('129', plain,
% 17.55/17.81      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('split', [status(esa)], ['95'])).
% 17.55/17.81  thf('130', plain,
% 17.55/17.81      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('sup-', [status(thm)], ['107', '108'])).
% 17.55/17.81  thf('131', plain,
% 17.55/17.81      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('sup-', [status(thm)], ['112', '113'])).
% 17.55/17.81  thf('132', plain,
% 17.55/17.81      ((![X0 : $i, X1 : $i, X2 : $i]:
% 17.55/17.81          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 17.55/17.81         <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('sup-', [status(thm)], ['117', '124'])).
% 17.55/17.81  thf('133', plain,
% 17.55/17.81      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 17.55/17.81      inference('sup-', [status(thm)], ['112', '113'])).
% 17.55/17.81  thf('134', plain,
% 17.55/17.81      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 17.55/17.81      inference('sup-', [status(thm)], ['118', '119'])).
% 17.55/17.81  thf('135', plain,
% 17.55/17.81      (![X26 : $i, X27 : $i, X28 : $i]:
% 17.55/17.81         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 17.55/17.81          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 17.55/17.81      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 17.55/17.81  thf('136', plain,
% 17.55/17.81      (![X0 : $i, X1 : $i]:
% 17.55/17.81         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 17.55/17.81      inference('sup-', [status(thm)], ['134', '135'])).
% 17.55/17.81  thf('137', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 17.55/17.81      inference('demod', [status(thm)], ['62', '63'])).
% 17.55/17.81  thf('138', plain,
% 17.55/17.81      (![X0 : $i, X1 : $i]:
% 17.55/17.81         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 17.55/17.81      inference('demod', [status(thm)], ['136', '137'])).
% 17.55/17.81  thf('139', plain,
% 17.55/17.81      (![X34 : $i, X35 : $i, X36 : $i]:
% 17.55/17.81         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 17.55/17.81          | (v1_funct_2 @ X36 @ X34 @ X35)
% 17.55/17.81          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 17.55/17.81  thf('140', plain,
% 17.55/17.81      (![X0 : $i, X1 : $i]:
% 17.55/17.81         (((X1) != (k1_xboole_0))
% 17.55/17.81          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 17.55/17.81          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 17.55/17.81      inference('sup-', [status(thm)], ['138', '139'])).
% 17.55/17.81  thf('141', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 17.55/17.81          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 17.55/17.81      inference('simplify', [status(thm)], ['140'])).
% 17.55/17.81  thf('142', plain,
% 17.55/17.81      (![X32 : $i, X33 : $i]:
% 17.55/17.81         ((zip_tseitin_0 @ X32 @ X33) | ((X33) != (k1_xboole_0)))),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 17.55/17.81  thf('143', plain, (![X32 : $i]: (zip_tseitin_0 @ X32 @ k1_xboole_0)),
% 17.55/17.81      inference('simplify', [status(thm)], ['142'])).
% 17.55/17.81  thf('144', plain,
% 17.55/17.81      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 17.55/17.81      inference('sup-', [status(thm)], ['118', '119'])).
% 17.55/17.81  thf('145', plain,
% 17.55/17.81      (![X37 : $i, X38 : $i, X39 : $i]:
% 17.55/17.81         (~ (zip_tseitin_0 @ X37 @ X38)
% 17.55/17.81          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 17.55/17.81          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 17.55/17.81  thf('146', plain,
% 17.55/17.81      (![X0 : $i, X1 : $i]:
% 17.55/17.81         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 17.55/17.81      inference('sup-', [status(thm)], ['144', '145'])).
% 17.55/17.81  thf('147', plain,
% 17.55/17.81      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 17.55/17.81      inference('sup-', [status(thm)], ['143', '146'])).
% 17.55/17.81  thf('148', plain,
% 17.55/17.81      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 17.55/17.81      inference('demod', [status(thm)], ['141', '147'])).
% 17.55/17.81  thf('149', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 17.55/17.81      inference('demod', [status(thm)],
% 17.55/17.81                ['99', '109', '114', '125', '126', '127', '128', '129', '130', 
% 17.55/17.81                 '131', '132', '133', '148'])).
% 17.55/17.81  thf('150', plain,
% 17.55/17.81      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 17.55/17.81      inference('split', [status(esa)], ['95'])).
% 17.55/17.81  thf('151', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 17.55/17.81      inference('sat_resolution*', [status(thm)], ['149', '150'])).
% 17.55/17.81  thf('152', plain, (((sk_B) != (k1_xboole_0))),
% 17.55/17.81      inference('simpl_trail', [status(thm)], ['96', '151'])).
% 17.55/17.81  thf('153', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ sk_B @ X0))),
% 17.55/17.81      inference('simplify_reflect-', [status(thm)], ['94', '152'])).
% 17.55/17.81  thf('154', plain,
% 17.55/17.81      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 17.55/17.81      inference('sup-', [status(thm)], ['77', '78'])).
% 17.55/17.81  thf('155', plain,
% 17.55/17.81      ((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 17.55/17.81      inference('sup-', [status(thm)], ['153', '154'])).
% 17.55/17.81  thf('156', plain,
% 17.55/17.81      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 17.55/17.81      inference('demod', [status(thm)], ['83', '86'])).
% 17.55/17.81  thf('157', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 17.55/17.81      inference('clc', [status(thm)], ['155', '156'])).
% 17.55/17.81  thf(t91_relat_1, axiom,
% 17.55/17.81    (![A:$i,B:$i]:
% 17.55/17.81     ( ( v1_relat_1 @ B ) =>
% 17.55/17.81       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 17.55/17.81         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 17.55/17.81  thf('158', plain,
% 17.55/17.81      (![X18 : $i, X19 : $i]:
% 17.55/17.81         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 17.55/17.81          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 17.55/17.81          | ~ (v1_relat_1 @ X19))),
% 17.55/17.81      inference('cnf', [status(esa)], [t91_relat_1])).
% 17.55/17.81  thf('159', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         (~ (r1_tarski @ X0 @ sk_A)
% 17.55/17.81          | ~ (v1_relat_1 @ sk_D)
% 17.55/17.81          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 17.55/17.81      inference('sup-', [status(thm)], ['157', '158'])).
% 17.55/17.81  thf('160', plain, ((v1_relat_1 @ sk_D)),
% 17.55/17.81      inference('sup-', [status(thm)], ['34', '35'])).
% 17.55/17.81  thf('161', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         (~ (r1_tarski @ X0 @ sk_A)
% 17.55/17.81          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 17.55/17.81      inference('demod', [status(thm)], ['159', '160'])).
% 17.55/17.81  thf('162', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 17.55/17.81      inference('sup-', [status(thm)], ['39', '161'])).
% 17.55/17.81  thf('163', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 17.55/17.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 17.55/17.81      inference('demod', [status(thm)], ['32', '33', '36'])).
% 17.55/17.81  thf('164', plain,
% 17.55/17.81      (![X26 : $i, X27 : $i, X28 : $i]:
% 17.55/17.81         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 17.55/17.81          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 17.55/17.81      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 17.55/17.81  thf('165', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         ((k1_relset_1 @ X0 @ sk_B @ (k7_relat_1 @ sk_D @ X0))
% 17.55/17.81           = (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 17.55/17.81      inference('sup-', [status(thm)], ['163', '164'])).
% 17.55/17.81  thf('166', plain,
% 17.55/17.81      (![X34 : $i, X35 : $i, X36 : $i]:
% 17.55/17.81         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 17.55/17.81          | (v1_funct_2 @ X36 @ X34 @ X35)
% 17.55/17.81          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 17.55/17.81  thf('167', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 17.55/17.81          | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 17.55/17.81          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 17.55/17.81      inference('sup-', [status(thm)], ['165', '166'])).
% 17.55/17.81  thf('168', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 17.55/17.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 17.55/17.81      inference('demod', [status(thm)], ['32', '33', '36'])).
% 17.55/17.81  thf('169', plain,
% 17.55/17.81      (![X37 : $i, X38 : $i, X39 : $i]:
% 17.55/17.81         (~ (zip_tseitin_0 @ X37 @ X38)
% 17.55/17.81          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 17.55/17.81          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 17.55/17.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 17.55/17.81  thf('170', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 17.55/17.81          | ~ (zip_tseitin_0 @ sk_B @ X0))),
% 17.55/17.81      inference('sup-', [status(thm)], ['168', '169'])).
% 17.55/17.81  thf('171', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         ((zip_tseitin_0 @ sk_B @ X0) | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 17.55/17.81      inference('sup-', [status(thm)], ['66', '75'])).
% 17.55/17.81  thf('172', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B @ X0))),
% 17.55/17.81      inference('sup-', [status(thm)], ['89', '92'])).
% 17.55/17.81  thf('173', plain,
% 17.55/17.81      (![X0 : $i, X1 : $i]:
% 17.55/17.81         (((sk_B) = (k1_xboole_0))
% 17.55/17.81          | (zip_tseitin_0 @ sk_B @ X1)
% 17.55/17.81          | (zip_tseitin_0 @ sk_B @ X0))),
% 17.55/17.81      inference('sup+', [status(thm)], ['171', '172'])).
% 17.55/17.81  thf('174', plain, (((sk_B) != (k1_xboole_0))),
% 17.55/17.81      inference('simpl_trail', [status(thm)], ['96', '151'])).
% 17.55/17.81  thf('175', plain,
% 17.55/17.81      (![X0 : $i, X1 : $i]:
% 17.55/17.81         ((zip_tseitin_0 @ sk_B @ X1) | (zip_tseitin_0 @ sk_B @ X0))),
% 17.55/17.81      inference('simplify_reflect-', [status(thm)], ['173', '174'])).
% 17.55/17.81  thf('176', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 17.55/17.81      inference('condensation', [status(thm)], ['175'])).
% 17.55/17.81  thf('177', plain,
% 17.55/17.81      (![X0 : $i]: (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)),
% 17.55/17.81      inference('demod', [status(thm)], ['170', '176'])).
% 17.55/17.81  thf('178', plain,
% 17.55/17.81      (![X0 : $i]:
% 17.55/17.81         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 17.55/17.81          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 17.55/17.81      inference('demod', [status(thm)], ['167', '177'])).
% 17.55/17.81  thf('179', plain,
% 17.55/17.81      ((((sk_C) != (sk_C))
% 17.55/17.81        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 17.55/17.81      inference('sup-', [status(thm)], ['162', '178'])).
% 17.55/17.81  thf('180', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 17.55/17.81      inference('simplify', [status(thm)], ['179'])).
% 17.55/17.81  thf('181', plain, ($false), inference('demod', [status(thm)], ['38', '180'])).
% 17.55/17.81  
% 17.55/17.81  % SZS output end Refutation
% 17.55/17.81  
% 17.66/17.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
