%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IMUyCAwfUC

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:39 EST 2020

% Result     : Theorem 16.82s
% Output     : Refutation 16.82s
% Verified   : 
% Statistics : Number of formulae       :  244 (1977 expanded)
%              Number of leaves         :   42 ( 595 expanded)
%              Depth                    :   25
%              Number of atoms          : 1821 (22504 expanded)
%              Number of equality atoms :  145 (1540 expanded)
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

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('90',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( r1_tarski @ sk_D @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('97',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('99',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('101',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('103',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( v5_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','105'])).

thf('107',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['88','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('114',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['115'])).

thf('117',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['115'])).

thf('118',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('119',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['115'])).

thf('121',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('124',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('126',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('128',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['115'])).

thf('130',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('133',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('135',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('138',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('139',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ( ( k2_partfun1 @ X45 @ X46 @ X44 @ X47 )
        = ( k7_relat_1 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','52'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','143'])).

thf('145',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('146',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('147',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('148',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['115'])).

thf('149',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('150',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('151',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','143'])).

thf('152',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('153',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('154',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X33 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('162',plain,(
    ! [X32: $i] :
      ( zip_tseitin_0 @ X32 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('164',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['162','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['160','166'])).

thf('168',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['119','128','133','144','145','146','147','148','149','150','151','152','167'])).

thf('169',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['115'])).

thf('170',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['168','169'])).

thf('171',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['116','170'])).

thf('172',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['114','171'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('173',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['39','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('179',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ sk_B @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('184',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ~ ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_B
        = ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['66','75'])).

thf('187',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('188',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('189',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['187','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X1 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['186','191'])).

thf('193',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['116','170'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(condensation,[status(thm)],['194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 ) ),
    inference(demod,[status(thm)],['185','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['182','196'])).

thf('198',plain,
    ( ( sk_C != sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['177','197'])).

thf('199',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,(
    $false ),
    inference(demod,[status(thm)],['38','199'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IMUyCAwfUC
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:18:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 16.82/17.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 16.82/17.04  % Solved by: fo/fo7.sh
% 16.82/17.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 16.82/17.04  % done 13377 iterations in 16.574s
% 16.82/17.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 16.82/17.04  % SZS output start Refutation
% 16.82/17.04  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 16.82/17.04  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 16.82/17.04  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 16.82/17.04  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 16.82/17.04  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 16.82/17.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 16.82/17.04  thf(sk_D_type, type, sk_D: $i).
% 16.82/17.04  thf(sk_C_type, type, sk_C: $i).
% 16.82/17.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 16.82/17.04  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 16.82/17.04  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 16.82/17.04  thf(sk_A_type, type, sk_A: $i).
% 16.82/17.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 16.82/17.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 16.82/17.04  thf(sk_B_type, type, sk_B: $i).
% 16.82/17.04  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 16.82/17.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 16.82/17.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 16.82/17.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 16.82/17.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 16.82/17.04  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 16.82/17.04  thf(t38_funct_2, conjecture,
% 16.82/17.04    (![A:$i,B:$i,C:$i,D:$i]:
% 16.82/17.04     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 16.82/17.04         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 16.82/17.04       ( ( r1_tarski @ C @ A ) =>
% 16.82/17.04         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 16.82/17.04           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 16.82/17.04             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 16.82/17.04             ( m1_subset_1 @
% 16.82/17.04               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 16.82/17.04               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 16.82/17.04  thf(zf_stmt_0, negated_conjecture,
% 16.82/17.04    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 16.82/17.04        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 16.82/17.04            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 16.82/17.04          ( ( r1_tarski @ C @ A ) =>
% 16.82/17.04            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 16.82/17.04              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 16.82/17.04                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 16.82/17.04                ( m1_subset_1 @
% 16.82/17.04                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 16.82/17.04                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 16.82/17.04    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 16.82/17.04  thf('0', plain,
% 16.82/17.04      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 16.82/17.04        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 16.82/17.04             sk_B)
% 16.82/17.04        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 16.82/17.04             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 16.82/17.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.04  thf('1', plain,
% 16.82/17.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 16.82/17.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.04  thf(dt_k2_partfun1, axiom,
% 16.82/17.04    (![A:$i,B:$i,C:$i,D:$i]:
% 16.82/17.04     ( ( ( v1_funct_1 @ C ) & 
% 16.82/17.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 16.82/17.04       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 16.82/17.04         ( m1_subset_1 @
% 16.82/17.04           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 16.82/17.04           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 16.82/17.04  thf('2', plain,
% 16.82/17.04      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 16.82/17.04         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 16.82/17.04          | ~ (v1_funct_1 @ X40)
% 16.82/17.04          | (v1_funct_1 @ (k2_partfun1 @ X41 @ X42 @ X40 @ X43)))),
% 16.82/17.04      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 16.82/17.04  thf('3', plain,
% 16.82/17.04      (![X0 : $i]:
% 16.82/17.04         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 16.82/17.04          | ~ (v1_funct_1 @ sk_D))),
% 16.82/17.04      inference('sup-', [status(thm)], ['1', '2'])).
% 16.82/17.04  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 16.82/17.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.04  thf('5', plain,
% 16.82/17.04      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 16.82/17.04      inference('demod', [status(thm)], ['3', '4'])).
% 16.82/17.04  thf('6', plain,
% 16.82/17.04      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 16.82/17.04        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 16.82/17.04             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 16.82/17.04      inference('demod', [status(thm)], ['0', '5'])).
% 16.82/17.04  thf('7', plain,
% 16.82/17.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 16.82/17.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.04  thf(redefinition_k2_partfun1, axiom,
% 16.82/17.04    (![A:$i,B:$i,C:$i,D:$i]:
% 16.82/17.04     ( ( ( v1_funct_1 @ C ) & 
% 16.82/17.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 16.82/17.04       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 16.82/17.04  thf('8', plain,
% 16.82/17.04      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 16.82/17.04         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 16.82/17.04          | ~ (v1_funct_1 @ X44)
% 16.82/17.04          | ((k2_partfun1 @ X45 @ X46 @ X44 @ X47) = (k7_relat_1 @ X44 @ X47)))),
% 16.82/17.04      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 16.82/17.05  thf('9', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 16.82/17.05          | ~ (v1_funct_1 @ sk_D))),
% 16.82/17.05      inference('sup-', [status(thm)], ['7', '8'])).
% 16.82/17.05  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.05  thf('11', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 16.82/17.05      inference('demod', [status(thm)], ['9', '10'])).
% 16.82/17.05  thf('12', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 16.82/17.05      inference('demod', [status(thm)], ['9', '10'])).
% 16.82/17.05  thf('13', plain,
% 16.82/17.05      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 16.82/17.05        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 16.82/17.05             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 16.82/17.05      inference('demod', [status(thm)], ['6', '11', '12'])).
% 16.82/17.05  thf('14', plain,
% 16.82/17.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.05  thf('15', plain,
% 16.82/17.05      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 16.82/17.05         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 16.82/17.05          | ~ (v1_funct_1 @ X40)
% 16.82/17.05          | (m1_subset_1 @ (k2_partfun1 @ X41 @ X42 @ X40 @ X43) @ 
% 16.82/17.05             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 16.82/17.05      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 16.82/17.05  thf('16', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 16.82/17.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 16.82/17.05          | ~ (v1_funct_1 @ sk_D))),
% 16.82/17.05      inference('sup-', [status(thm)], ['14', '15'])).
% 16.82/17.05  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.05  thf('18', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 16.82/17.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 16.82/17.05      inference('demod', [status(thm)], ['16', '17'])).
% 16.82/17.05  thf('19', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 16.82/17.05      inference('demod', [status(thm)], ['9', '10'])).
% 16.82/17.05  thf('20', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 16.82/17.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 16.82/17.05      inference('demod', [status(thm)], ['18', '19'])).
% 16.82/17.05  thf(cc2_relset_1, axiom,
% 16.82/17.05    (![A:$i,B:$i,C:$i]:
% 16.82/17.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.82/17.05       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 16.82/17.05  thf('21', plain,
% 16.82/17.05      (![X23 : $i, X24 : $i, X25 : $i]:
% 16.82/17.05         ((v5_relat_1 @ X23 @ X25)
% 16.82/17.05          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 16.82/17.05      inference('cnf', [status(esa)], [cc2_relset_1])).
% 16.82/17.05  thf('22', plain,
% 16.82/17.05      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 16.82/17.05      inference('sup-', [status(thm)], ['20', '21'])).
% 16.82/17.05  thf(d19_relat_1, axiom,
% 16.82/17.05    (![A:$i,B:$i]:
% 16.82/17.05     ( ( v1_relat_1 @ B ) =>
% 16.82/17.05       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 16.82/17.05  thf('23', plain,
% 16.82/17.05      (![X10 : $i, X11 : $i]:
% 16.82/17.05         (~ (v5_relat_1 @ X10 @ X11)
% 16.82/17.05          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 16.82/17.05          | ~ (v1_relat_1 @ X10))),
% 16.82/17.05      inference('cnf', [status(esa)], [d19_relat_1])).
% 16.82/17.05  thf('24', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 16.82/17.05          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 16.82/17.05      inference('sup-', [status(thm)], ['22', '23'])).
% 16.82/17.05  thf('25', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 16.82/17.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 16.82/17.05      inference('demod', [status(thm)], ['18', '19'])).
% 16.82/17.05  thf(cc1_relset_1, axiom,
% 16.82/17.05    (![A:$i,B:$i,C:$i]:
% 16.82/17.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.82/17.05       ( v1_relat_1 @ C ) ))).
% 16.82/17.05  thf('26', plain,
% 16.82/17.05      (![X20 : $i, X21 : $i, X22 : $i]:
% 16.82/17.05         ((v1_relat_1 @ X20)
% 16.82/17.05          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 16.82/17.05      inference('cnf', [status(esa)], [cc1_relset_1])).
% 16.82/17.05  thf('27', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['25', '26'])).
% 16.82/17.05  thf('28', plain,
% 16.82/17.05      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 16.82/17.05      inference('demod', [status(thm)], ['24', '27'])).
% 16.82/17.05  thf(t87_relat_1, axiom,
% 16.82/17.05    (![A:$i,B:$i]:
% 16.82/17.05     ( ( v1_relat_1 @ B ) =>
% 16.82/17.05       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 16.82/17.05  thf('29', plain,
% 16.82/17.05      (![X14 : $i, X15 : $i]:
% 16.82/17.05         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X14 @ X15)) @ X15)
% 16.82/17.05          | ~ (v1_relat_1 @ X14))),
% 16.82/17.05      inference('cnf', [status(esa)], [t87_relat_1])).
% 16.82/17.05  thf(t11_relset_1, axiom,
% 16.82/17.05    (![A:$i,B:$i,C:$i]:
% 16.82/17.05     ( ( v1_relat_1 @ C ) =>
% 16.82/17.05       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 16.82/17.05           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 16.82/17.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 16.82/17.05  thf('30', plain,
% 16.82/17.05      (![X29 : $i, X30 : $i, X31 : $i]:
% 16.82/17.05         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 16.82/17.05          | ~ (r1_tarski @ (k2_relat_1 @ X29) @ X31)
% 16.82/17.05          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 16.82/17.05          | ~ (v1_relat_1 @ X29))),
% 16.82/17.05      inference('cnf', [status(esa)], [t11_relset_1])).
% 16.82/17.05  thf('31', plain,
% 16.82/17.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.82/17.05         (~ (v1_relat_1 @ X1)
% 16.82/17.05          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 16.82/17.05          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 16.82/17.05             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 16.82/17.05          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 16.82/17.05      inference('sup-', [status(thm)], ['29', '30'])).
% 16.82/17.05  thf('32', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 16.82/17.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 16.82/17.05          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 16.82/17.05          | ~ (v1_relat_1 @ sk_D))),
% 16.82/17.05      inference('sup-', [status(thm)], ['28', '31'])).
% 16.82/17.05  thf('33', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['25', '26'])).
% 16.82/17.05  thf('34', plain,
% 16.82/17.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.05  thf('35', plain,
% 16.82/17.05      (![X20 : $i, X21 : $i, X22 : $i]:
% 16.82/17.05         ((v1_relat_1 @ X20)
% 16.82/17.05          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 16.82/17.05      inference('cnf', [status(esa)], [cc1_relset_1])).
% 16.82/17.05  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 16.82/17.05      inference('sup-', [status(thm)], ['34', '35'])).
% 16.82/17.05  thf('37', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 16.82/17.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 16.82/17.05      inference('demod', [status(thm)], ['32', '33', '36'])).
% 16.82/17.05  thf('38', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 16.82/17.05      inference('demod', [status(thm)], ['13', '37'])).
% 16.82/17.05  thf('39', plain, ((r1_tarski @ sk_C @ sk_A)),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.05  thf(d1_funct_2, axiom,
% 16.82/17.05    (![A:$i,B:$i,C:$i]:
% 16.82/17.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.82/17.05       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 16.82/17.05           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 16.82/17.05             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 16.82/17.05         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 16.82/17.05           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 16.82/17.05             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 16.82/17.05  thf(zf_stmt_1, axiom,
% 16.82/17.05    (![B:$i,A:$i]:
% 16.82/17.05     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 16.82/17.05       ( zip_tseitin_0 @ B @ A ) ))).
% 16.82/17.05  thf('40', plain,
% 16.82/17.05      (![X32 : $i, X33 : $i]:
% 16.82/17.05         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_1])).
% 16.82/17.05  thf(t88_relat_1, axiom,
% 16.82/17.05    (![A:$i,B:$i]:
% 16.82/17.05     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 16.82/17.05  thf('41', plain,
% 16.82/17.05      (![X16 : $i, X17 : $i]:
% 16.82/17.05         ((r1_tarski @ (k7_relat_1 @ X16 @ X17) @ X16) | ~ (v1_relat_1 @ X16))),
% 16.82/17.05      inference('cnf', [status(esa)], [t88_relat_1])).
% 16.82/17.05  thf(t3_xboole_1, axiom,
% 16.82/17.05    (![A:$i]:
% 16.82/17.05     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 16.82/17.05  thf('42', plain,
% 16.82/17.05      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 16.82/17.05      inference('cnf', [status(esa)], [t3_xboole_1])).
% 16.82/17.05  thf('43', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (~ (v1_relat_1 @ k1_xboole_0)
% 16.82/17.05          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 16.82/17.05      inference('sup-', [status(thm)], ['41', '42'])).
% 16.82/17.05  thf(t113_zfmisc_1, axiom,
% 16.82/17.05    (![A:$i,B:$i]:
% 16.82/17.05     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 16.82/17.05       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 16.82/17.05  thf('44', plain,
% 16.82/17.05      (![X5 : $i, X6 : $i]:
% 16.82/17.05         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 16.82/17.05      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 16.82/17.05  thf('45', plain,
% 16.82/17.05      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 16.82/17.05      inference('simplify', [status(thm)], ['44'])).
% 16.82/17.05  thf(d10_xboole_0, axiom,
% 16.82/17.05    (![A:$i,B:$i]:
% 16.82/17.05     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 16.82/17.05  thf('46', plain,
% 16.82/17.05      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 16.82/17.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 16.82/17.05  thf('47', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 16.82/17.05      inference('simplify', [status(thm)], ['46'])).
% 16.82/17.05  thf(t3_subset, axiom,
% 16.82/17.05    (![A:$i,B:$i]:
% 16.82/17.05     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 16.82/17.05  thf('48', plain,
% 16.82/17.05      (![X7 : $i, X9 : $i]:
% 16.82/17.05         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 16.82/17.05      inference('cnf', [status(esa)], [t3_subset])).
% 16.82/17.05  thf('49', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['47', '48'])).
% 16.82/17.05  thf('50', plain,
% 16.82/17.05      (![X20 : $i, X21 : $i, X22 : $i]:
% 16.82/17.05         ((v1_relat_1 @ X20)
% 16.82/17.05          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 16.82/17.05      inference('cnf', [status(esa)], [cc1_relset_1])).
% 16.82/17.05  thf('51', plain,
% 16.82/17.05      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['49', '50'])).
% 16.82/17.05  thf('52', plain, ((v1_relat_1 @ k1_xboole_0)),
% 16.82/17.05      inference('sup+', [status(thm)], ['45', '51'])).
% 16.82/17.05  thf('53', plain,
% 16.82/17.05      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 16.82/17.05      inference('demod', [status(thm)], ['43', '52'])).
% 16.82/17.05  thf('54', plain,
% 16.82/17.05      (![X14 : $i, X15 : $i]:
% 16.82/17.05         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X14 @ X15)) @ X15)
% 16.82/17.05          | ~ (v1_relat_1 @ X14))),
% 16.82/17.05      inference('cnf', [status(esa)], [t87_relat_1])).
% 16.82/17.05  thf('55', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         ((r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 16.82/17.05          | ~ (v1_relat_1 @ k1_xboole_0))),
% 16.82/17.05      inference('sup+', [status(thm)], ['53', '54'])).
% 16.82/17.05  thf('56', plain, ((v1_relat_1 @ k1_xboole_0)),
% 16.82/17.05      inference('sup+', [status(thm)], ['45', '51'])).
% 16.82/17.05  thf('57', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 16.82/17.05      inference('demod', [status(thm)], ['55', '56'])).
% 16.82/17.05  thf('58', plain,
% 16.82/17.05      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 16.82/17.05      inference('demod', [status(thm)], ['43', '52'])).
% 16.82/17.05  thf('59', plain,
% 16.82/17.05      (![X14 : $i, X15 : $i]:
% 16.82/17.05         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X14 @ X15)) @ X15)
% 16.82/17.05          | ~ (v1_relat_1 @ X14))),
% 16.82/17.05      inference('cnf', [status(esa)], [t87_relat_1])).
% 16.82/17.05  thf('60', plain,
% 16.82/17.05      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 16.82/17.05      inference('cnf', [status(esa)], [t3_xboole_1])).
% 16.82/17.05  thf('61', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (~ (v1_relat_1 @ X0)
% 16.82/17.05          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 16.82/17.05      inference('sup-', [status(thm)], ['59', '60'])).
% 16.82/17.05  thf('62', plain,
% 16.82/17.05      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 16.82/17.05        | ~ (v1_relat_1 @ k1_xboole_0))),
% 16.82/17.05      inference('sup+', [status(thm)], ['58', '61'])).
% 16.82/17.05  thf('63', plain, ((v1_relat_1 @ k1_xboole_0)),
% 16.82/17.05      inference('sup+', [status(thm)], ['45', '51'])).
% 16.82/17.05  thf('64', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.82/17.05      inference('demod', [status(thm)], ['62', '63'])).
% 16.82/17.05  thf('65', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 16.82/17.05      inference('demod', [status(thm)], ['57', '64'])).
% 16.82/17.05  thf('66', plain,
% 16.82/17.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.82/17.05         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 16.82/17.05      inference('sup+', [status(thm)], ['40', '65'])).
% 16.82/17.05  thf('67', plain,
% 16.82/17.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.05  thf('68', plain,
% 16.82/17.05      (![X23 : $i, X24 : $i, X25 : $i]:
% 16.82/17.05         ((v5_relat_1 @ X23 @ X25)
% 16.82/17.05          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 16.82/17.05      inference('cnf', [status(esa)], [cc2_relset_1])).
% 16.82/17.05  thf('69', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 16.82/17.05      inference('sup-', [status(thm)], ['67', '68'])).
% 16.82/17.05  thf('70', plain,
% 16.82/17.05      (![X10 : $i, X11 : $i]:
% 16.82/17.05         (~ (v5_relat_1 @ X10 @ X11)
% 16.82/17.05          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 16.82/17.05          | ~ (v1_relat_1 @ X10))),
% 16.82/17.05      inference('cnf', [status(esa)], [d19_relat_1])).
% 16.82/17.05  thf('71', plain,
% 16.82/17.05      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 16.82/17.05      inference('sup-', [status(thm)], ['69', '70'])).
% 16.82/17.05  thf('72', plain, ((v1_relat_1 @ sk_D)),
% 16.82/17.05      inference('sup-', [status(thm)], ['34', '35'])).
% 16.82/17.05  thf('73', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 16.82/17.05      inference('demod', [status(thm)], ['71', '72'])).
% 16.82/17.05  thf('74', plain,
% 16.82/17.05      (![X0 : $i, X2 : $i]:
% 16.82/17.05         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 16.82/17.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 16.82/17.05  thf('75', plain,
% 16.82/17.05      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 16.82/17.05        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 16.82/17.05      inference('sup-', [status(thm)], ['73', '74'])).
% 16.82/17.05  thf('76', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         ((zip_tseitin_0 @ sk_B @ X0) | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 16.82/17.05      inference('sup-', [status(thm)], ['66', '75'])).
% 16.82/17.05  thf('77', plain,
% 16.82/17.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.05  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 16.82/17.05  thf(zf_stmt_3, axiom,
% 16.82/17.05    (![C:$i,B:$i,A:$i]:
% 16.82/17.05     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 16.82/17.05       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 16.82/17.05  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 16.82/17.05  thf(zf_stmt_5, axiom,
% 16.82/17.05    (![A:$i,B:$i,C:$i]:
% 16.82/17.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.82/17.05       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 16.82/17.05         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 16.82/17.05           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 16.82/17.05             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 16.82/17.05  thf('78', plain,
% 16.82/17.05      (![X37 : $i, X38 : $i, X39 : $i]:
% 16.82/17.05         (~ (zip_tseitin_0 @ X37 @ X38)
% 16.82/17.05          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 16.82/17.05          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 16.82/17.05  thf('79', plain,
% 16.82/17.05      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 16.82/17.05      inference('sup-', [status(thm)], ['77', '78'])).
% 16.82/17.05  thf('80', plain,
% 16.82/17.05      ((((sk_B) = (k2_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 16.82/17.05      inference('sup-', [status(thm)], ['76', '79'])).
% 16.82/17.05  thf('81', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.05  thf('82', plain,
% 16.82/17.05      (![X34 : $i, X35 : $i, X36 : $i]:
% 16.82/17.05         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 16.82/17.05          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 16.82/17.05          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_3])).
% 16.82/17.05  thf('83', plain,
% 16.82/17.05      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 16.82/17.05        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 16.82/17.05      inference('sup-', [status(thm)], ['81', '82'])).
% 16.82/17.05  thf('84', plain,
% 16.82/17.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.05  thf(redefinition_k1_relset_1, axiom,
% 16.82/17.05    (![A:$i,B:$i,C:$i]:
% 16.82/17.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.82/17.05       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 16.82/17.05  thf('85', plain,
% 16.82/17.05      (![X26 : $i, X27 : $i, X28 : $i]:
% 16.82/17.05         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 16.82/17.05          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 16.82/17.05      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 16.82/17.05  thf('86', plain,
% 16.82/17.05      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 16.82/17.05      inference('sup-', [status(thm)], ['84', '85'])).
% 16.82/17.05  thf('87', plain,
% 16.82/17.05      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 16.82/17.05      inference('demod', [status(thm)], ['83', '86'])).
% 16.82/17.05  thf('88', plain,
% 16.82/17.05      ((((sk_B) = (k2_relat_1 @ sk_D)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 16.82/17.05      inference('sup-', [status(thm)], ['80', '87'])).
% 16.82/17.05  thf('89', plain,
% 16.82/17.05      (![X32 : $i, X33 : $i]:
% 16.82/17.05         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_1])).
% 16.82/17.05  thf('90', plain,
% 16.82/17.05      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 16.82/17.05      inference('simplify', [status(thm)], ['44'])).
% 16.82/17.05  thf('91', plain,
% 16.82/17.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.82/17.05         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 16.82/17.05      inference('sup+', [status(thm)], ['89', '90'])).
% 16.82/17.05  thf('92', plain,
% 16.82/17.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.05  thf('93', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 16.82/17.05          | (zip_tseitin_0 @ sk_B @ X0))),
% 16.82/17.05      inference('sup+', [status(thm)], ['91', '92'])).
% 16.82/17.05  thf('94', plain,
% 16.82/17.05      (![X7 : $i, X8 : $i]:
% 16.82/17.05         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 16.82/17.05      inference('cnf', [status(esa)], [t3_subset])).
% 16.82/17.05  thf('95', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         ((zip_tseitin_0 @ sk_B @ X0) | (r1_tarski @ sk_D @ k1_xboole_0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['93', '94'])).
% 16.82/17.05  thf('96', plain,
% 16.82/17.05      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 16.82/17.05      inference('sup-', [status(thm)], ['77', '78'])).
% 16.82/17.05  thf('97', plain,
% 16.82/17.05      (((r1_tarski @ sk_D @ k1_xboole_0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 16.82/17.05      inference('sup-', [status(thm)], ['95', '96'])).
% 16.82/17.05  thf('98', plain,
% 16.82/17.05      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 16.82/17.05      inference('demod', [status(thm)], ['83', '86'])).
% 16.82/17.05  thf('99', plain,
% 16.82/17.05      (((r1_tarski @ sk_D @ k1_xboole_0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 16.82/17.05      inference('sup-', [status(thm)], ['97', '98'])).
% 16.82/17.05  thf('100', plain,
% 16.82/17.05      (![X7 : $i, X9 : $i]:
% 16.82/17.05         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 16.82/17.05      inference('cnf', [status(esa)], [t3_subset])).
% 16.82/17.05  thf('101', plain,
% 16.82/17.05      ((((sk_A) = (k1_relat_1 @ sk_D))
% 16.82/17.05        | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 16.82/17.05      inference('sup-', [status(thm)], ['99', '100'])).
% 16.82/17.05  thf('102', plain,
% 16.82/17.05      (![X5 : $i, X6 : $i]:
% 16.82/17.05         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 16.82/17.05      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 16.82/17.05  thf('103', plain,
% 16.82/17.05      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 16.82/17.05      inference('simplify', [status(thm)], ['102'])).
% 16.82/17.05  thf('104', plain,
% 16.82/17.05      (![X23 : $i, X24 : $i, X25 : $i]:
% 16.82/17.05         ((v5_relat_1 @ X23 @ X25)
% 16.82/17.05          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 16.82/17.05      inference('cnf', [status(esa)], [cc2_relset_1])).
% 16.82/17.05  thf('105', plain,
% 16.82/17.05      (![X0 : $i, X1 : $i]:
% 16.82/17.05         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 16.82/17.05          | (v5_relat_1 @ X1 @ X0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['103', '104'])).
% 16.82/17.05  thf('106', plain,
% 16.82/17.05      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | (v5_relat_1 @ sk_D @ X0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['101', '105'])).
% 16.82/17.05  thf('107', plain,
% 16.82/17.05      (![X10 : $i, X11 : $i]:
% 16.82/17.05         (~ (v5_relat_1 @ X10 @ X11)
% 16.82/17.05          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 16.82/17.05          | ~ (v1_relat_1 @ X10))),
% 16.82/17.05      inference('cnf', [status(esa)], [d19_relat_1])).
% 16.82/17.05  thf('108', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (((sk_A) = (k1_relat_1 @ sk_D))
% 16.82/17.05          | ~ (v1_relat_1 @ sk_D)
% 16.82/17.05          | (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['106', '107'])).
% 16.82/17.05  thf('109', plain, ((v1_relat_1 @ sk_D)),
% 16.82/17.05      inference('sup-', [status(thm)], ['34', '35'])).
% 16.82/17.05  thf('110', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (((sk_A) = (k1_relat_1 @ sk_D))
% 16.82/17.05          | (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 16.82/17.05      inference('demod', [status(thm)], ['108', '109'])).
% 16.82/17.05  thf('111', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         ((r1_tarski @ sk_B @ X0)
% 16.82/17.05          | ((sk_A) = (k1_relat_1 @ sk_D))
% 16.82/17.05          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 16.82/17.05      inference('sup+', [status(thm)], ['88', '110'])).
% 16.82/17.05  thf('112', plain,
% 16.82/17.05      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | (r1_tarski @ sk_B @ X0))),
% 16.82/17.05      inference('simplify', [status(thm)], ['111'])).
% 16.82/17.05  thf('113', plain,
% 16.82/17.05      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 16.82/17.05      inference('cnf', [status(esa)], [t3_xboole_1])).
% 16.82/17.05  thf('114', plain,
% 16.82/17.05      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((sk_B) = (k1_xboole_0)))),
% 16.82/17.05      inference('sup-', [status(thm)], ['112', '113'])).
% 16.82/17.05  thf('115', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.05  thf('116', plain,
% 16.82/17.05      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 16.82/17.05      inference('split', [status(esa)], ['115'])).
% 16.82/17.05  thf('117', plain,
% 16.82/17.05      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('split', [status(esa)], ['115'])).
% 16.82/17.05  thf('118', plain,
% 16.82/17.05      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 16.82/17.05        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 16.82/17.05             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 16.82/17.05      inference('demod', [status(thm)], ['0', '5'])).
% 16.82/17.05  thf('119', plain,
% 16.82/17.05      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 16.82/17.05            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 16.82/17.05         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 16.82/17.05              sk_B)))
% 16.82/17.05         <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('sup-', [status(thm)], ['117', '118'])).
% 16.82/17.05  thf('120', plain,
% 16.82/17.05      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('split', [status(esa)], ['115'])).
% 16.82/17.05  thf('121', plain,
% 16.82/17.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.05  thf('122', plain,
% 16.82/17.05      (((m1_subset_1 @ sk_D @ 
% 16.82/17.05         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 16.82/17.05         <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('sup+', [status(thm)], ['120', '121'])).
% 16.82/17.05  thf('123', plain,
% 16.82/17.05      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 16.82/17.05      inference('simplify', [status(thm)], ['102'])).
% 16.82/17.05  thf('124', plain,
% 16.82/17.05      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 16.82/17.05         <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('demod', [status(thm)], ['122', '123'])).
% 16.82/17.05  thf('125', plain,
% 16.82/17.05      (![X7 : $i, X8 : $i]:
% 16.82/17.05         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 16.82/17.05      inference('cnf', [status(esa)], [t3_subset])).
% 16.82/17.05  thf('126', plain,
% 16.82/17.05      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('sup-', [status(thm)], ['124', '125'])).
% 16.82/17.05  thf('127', plain,
% 16.82/17.05      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 16.82/17.05      inference('cnf', [status(esa)], [t3_xboole_1])).
% 16.82/17.05  thf('128', plain,
% 16.82/17.05      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('sup-', [status(thm)], ['126', '127'])).
% 16.82/17.05  thf('129', plain,
% 16.82/17.05      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('split', [status(esa)], ['115'])).
% 16.82/17.05  thf('130', plain, ((r1_tarski @ sk_C @ sk_A)),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.05  thf('131', plain,
% 16.82/17.05      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('sup+', [status(thm)], ['129', '130'])).
% 16.82/17.05  thf('132', plain,
% 16.82/17.05      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 16.82/17.05      inference('cnf', [status(esa)], [t3_xboole_1])).
% 16.82/17.05  thf('133', plain,
% 16.82/17.05      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('sup-', [status(thm)], ['131', '132'])).
% 16.82/17.05  thf('134', plain,
% 16.82/17.05      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('sup-', [status(thm)], ['126', '127'])).
% 16.82/17.05  thf('135', plain, ((v1_funct_1 @ sk_D)),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.82/17.05  thf('136', plain,
% 16.82/17.05      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('sup+', [status(thm)], ['134', '135'])).
% 16.82/17.05  thf('137', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 16.82/17.05      inference('demod', [status(thm)], ['57', '64'])).
% 16.82/17.05  thf('138', plain,
% 16.82/17.05      (![X7 : $i, X9 : $i]:
% 16.82/17.05         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 16.82/17.05      inference('cnf', [status(esa)], [t3_subset])).
% 16.82/17.05  thf('139', plain,
% 16.82/17.05      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['137', '138'])).
% 16.82/17.05  thf('140', plain,
% 16.82/17.05      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 16.82/17.05         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 16.82/17.05          | ~ (v1_funct_1 @ X44)
% 16.82/17.05          | ((k2_partfun1 @ X45 @ X46 @ X44 @ X47) = (k7_relat_1 @ X44 @ X47)))),
% 16.82/17.05      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 16.82/17.05  thf('141', plain,
% 16.82/17.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.82/17.05         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 16.82/17.05            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 16.82/17.05          | ~ (v1_funct_1 @ k1_xboole_0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['139', '140'])).
% 16.82/17.05  thf('142', plain,
% 16.82/17.05      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 16.82/17.05      inference('demod', [status(thm)], ['43', '52'])).
% 16.82/17.05  thf('143', plain,
% 16.82/17.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.82/17.05         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 16.82/17.05          | ~ (v1_funct_1 @ k1_xboole_0))),
% 16.82/17.05      inference('demod', [status(thm)], ['141', '142'])).
% 16.82/17.05  thf('144', plain,
% 16.82/17.05      ((![X0 : $i, X1 : $i, X2 : $i]:
% 16.82/17.05          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 16.82/17.05         <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('sup-', [status(thm)], ['136', '143'])).
% 16.82/17.05  thf('145', plain,
% 16.82/17.05      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('sup-', [status(thm)], ['131', '132'])).
% 16.82/17.05  thf('146', plain,
% 16.82/17.05      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 16.82/17.05      inference('simplify', [status(thm)], ['102'])).
% 16.82/17.05  thf('147', plain,
% 16.82/17.05      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['137', '138'])).
% 16.82/17.05  thf('148', plain,
% 16.82/17.05      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('split', [status(esa)], ['115'])).
% 16.82/17.05  thf('149', plain,
% 16.82/17.05      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('sup-', [status(thm)], ['126', '127'])).
% 16.82/17.05  thf('150', plain,
% 16.82/17.05      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('sup-', [status(thm)], ['131', '132'])).
% 16.82/17.05  thf('151', plain,
% 16.82/17.05      ((![X0 : $i, X1 : $i, X2 : $i]:
% 16.82/17.05          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 16.82/17.05         <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('sup-', [status(thm)], ['136', '143'])).
% 16.82/17.05  thf('152', plain,
% 16.82/17.05      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 16.82/17.05      inference('sup-', [status(thm)], ['131', '132'])).
% 16.82/17.05  thf('153', plain,
% 16.82/17.05      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['137', '138'])).
% 16.82/17.05  thf('154', plain,
% 16.82/17.05      (![X26 : $i, X27 : $i, X28 : $i]:
% 16.82/17.05         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 16.82/17.05          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 16.82/17.05      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 16.82/17.05  thf('155', plain,
% 16.82/17.05      (![X0 : $i, X1 : $i]:
% 16.82/17.05         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['153', '154'])).
% 16.82/17.05  thf('156', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.82/17.05      inference('demod', [status(thm)], ['62', '63'])).
% 16.82/17.05  thf('157', plain,
% 16.82/17.05      (![X0 : $i, X1 : $i]:
% 16.82/17.05         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 16.82/17.05      inference('demod', [status(thm)], ['155', '156'])).
% 16.82/17.05  thf('158', plain,
% 16.82/17.05      (![X34 : $i, X35 : $i, X36 : $i]:
% 16.82/17.05         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 16.82/17.05          | (v1_funct_2 @ X36 @ X34 @ X35)
% 16.82/17.05          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_3])).
% 16.82/17.05  thf('159', plain,
% 16.82/17.05      (![X0 : $i, X1 : $i]:
% 16.82/17.05         (((X1) != (k1_xboole_0))
% 16.82/17.05          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 16.82/17.05          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['157', '158'])).
% 16.82/17.05  thf('160', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 16.82/17.05          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 16.82/17.05      inference('simplify', [status(thm)], ['159'])).
% 16.82/17.05  thf('161', plain,
% 16.82/17.05      (![X32 : $i, X33 : $i]:
% 16.82/17.05         ((zip_tseitin_0 @ X32 @ X33) | ((X33) != (k1_xboole_0)))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_1])).
% 16.82/17.05  thf('162', plain, (![X32 : $i]: (zip_tseitin_0 @ X32 @ k1_xboole_0)),
% 16.82/17.05      inference('simplify', [status(thm)], ['161'])).
% 16.82/17.05  thf('163', plain,
% 16.82/17.05      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['137', '138'])).
% 16.82/17.05  thf('164', plain,
% 16.82/17.05      (![X37 : $i, X38 : $i, X39 : $i]:
% 16.82/17.05         (~ (zip_tseitin_0 @ X37 @ X38)
% 16.82/17.05          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 16.82/17.05          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 16.82/17.05  thf('165', plain,
% 16.82/17.05      (![X0 : $i, X1 : $i]:
% 16.82/17.05         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 16.82/17.05      inference('sup-', [status(thm)], ['163', '164'])).
% 16.82/17.05  thf('166', plain,
% 16.82/17.05      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 16.82/17.05      inference('sup-', [status(thm)], ['162', '165'])).
% 16.82/17.05  thf('167', plain,
% 16.82/17.05      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 16.82/17.05      inference('demod', [status(thm)], ['160', '166'])).
% 16.82/17.05  thf('168', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 16.82/17.05      inference('demod', [status(thm)],
% 16.82/17.05                ['119', '128', '133', '144', '145', '146', '147', '148', 
% 16.82/17.05                 '149', '150', '151', '152', '167'])).
% 16.82/17.05  thf('169', plain,
% 16.82/17.05      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 16.82/17.05      inference('split', [status(esa)], ['115'])).
% 16.82/17.05  thf('170', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 16.82/17.05      inference('sat_resolution*', [status(thm)], ['168', '169'])).
% 16.82/17.05  thf('171', plain, (((sk_B) != (k1_xboole_0))),
% 16.82/17.05      inference('simpl_trail', [status(thm)], ['116', '170'])).
% 16.82/17.05  thf('172', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 16.82/17.05      inference('simplify_reflect-', [status(thm)], ['114', '171'])).
% 16.82/17.05  thf(t91_relat_1, axiom,
% 16.82/17.05    (![A:$i,B:$i]:
% 16.82/17.05     ( ( v1_relat_1 @ B ) =>
% 16.82/17.05       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 16.82/17.05         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 16.82/17.05  thf('173', plain,
% 16.82/17.05      (![X18 : $i, X19 : $i]:
% 16.82/17.05         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 16.82/17.05          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 16.82/17.05          | ~ (v1_relat_1 @ X19))),
% 16.82/17.05      inference('cnf', [status(esa)], [t91_relat_1])).
% 16.82/17.05  thf('174', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (~ (r1_tarski @ X0 @ sk_A)
% 16.82/17.05          | ~ (v1_relat_1 @ sk_D)
% 16.82/17.05          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 16.82/17.05      inference('sup-', [status(thm)], ['172', '173'])).
% 16.82/17.05  thf('175', plain, ((v1_relat_1 @ sk_D)),
% 16.82/17.05      inference('sup-', [status(thm)], ['34', '35'])).
% 16.82/17.05  thf('176', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (~ (r1_tarski @ X0 @ sk_A)
% 16.82/17.05          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 16.82/17.05      inference('demod', [status(thm)], ['174', '175'])).
% 16.82/17.05  thf('177', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 16.82/17.05      inference('sup-', [status(thm)], ['39', '176'])).
% 16.82/17.05  thf('178', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 16.82/17.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 16.82/17.05      inference('demod', [status(thm)], ['32', '33', '36'])).
% 16.82/17.05  thf('179', plain,
% 16.82/17.05      (![X26 : $i, X27 : $i, X28 : $i]:
% 16.82/17.05         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 16.82/17.05          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 16.82/17.05      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 16.82/17.05  thf('180', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         ((k1_relset_1 @ X0 @ sk_B @ (k7_relat_1 @ sk_D @ X0))
% 16.82/17.05           = (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 16.82/17.05      inference('sup-', [status(thm)], ['178', '179'])).
% 16.82/17.05  thf('181', plain,
% 16.82/17.05      (![X34 : $i, X35 : $i, X36 : $i]:
% 16.82/17.05         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 16.82/17.05          | (v1_funct_2 @ X36 @ X34 @ X35)
% 16.82/17.05          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_3])).
% 16.82/17.05  thf('182', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 16.82/17.05          | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 16.82/17.05          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 16.82/17.05      inference('sup-', [status(thm)], ['180', '181'])).
% 16.82/17.05  thf('183', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 16.82/17.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 16.82/17.05      inference('demod', [status(thm)], ['32', '33', '36'])).
% 16.82/17.05  thf('184', plain,
% 16.82/17.05      (![X37 : $i, X38 : $i, X39 : $i]:
% 16.82/17.05         (~ (zip_tseitin_0 @ X37 @ X38)
% 16.82/17.05          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 16.82/17.05          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 16.82/17.05  thf('185', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 16.82/17.05          | ~ (zip_tseitin_0 @ sk_B @ X0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['183', '184'])).
% 16.82/17.05  thf('186', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         ((zip_tseitin_0 @ sk_B @ X0) | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 16.82/17.05      inference('sup-', [status(thm)], ['66', '75'])).
% 16.82/17.05  thf('187', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 16.82/17.05      inference('demod', [status(thm)], ['71', '72'])).
% 16.82/17.05  thf('188', plain,
% 16.82/17.05      (![X32 : $i, X33 : $i]:
% 16.82/17.05         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 16.82/17.05      inference('cnf', [status(esa)], [zf_stmt_1])).
% 16.82/17.05  thf('189', plain,
% 16.82/17.05      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 16.82/17.05      inference('cnf', [status(esa)], [t3_xboole_1])).
% 16.82/17.05  thf('190', plain,
% 16.82/17.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.82/17.05         (~ (r1_tarski @ X1 @ X0)
% 16.82/17.05          | (zip_tseitin_0 @ X0 @ X2)
% 16.82/17.05          | ((X1) = (k1_xboole_0)))),
% 16.82/17.05      inference('sup-', [status(thm)], ['188', '189'])).
% 16.82/17.05  thf('191', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B @ X0))),
% 16.82/17.05      inference('sup-', [status(thm)], ['187', '190'])).
% 16.82/17.05  thf('192', plain,
% 16.82/17.05      (![X0 : $i, X1 : $i]:
% 16.82/17.05         (((sk_B) = (k1_xboole_0))
% 16.82/17.05          | (zip_tseitin_0 @ sk_B @ X1)
% 16.82/17.05          | (zip_tseitin_0 @ sk_B @ X0))),
% 16.82/17.05      inference('sup+', [status(thm)], ['186', '191'])).
% 16.82/17.05  thf('193', plain, (((sk_B) != (k1_xboole_0))),
% 16.82/17.05      inference('simpl_trail', [status(thm)], ['116', '170'])).
% 16.82/17.05  thf('194', plain,
% 16.82/17.05      (![X0 : $i, X1 : $i]:
% 16.82/17.05         ((zip_tseitin_0 @ sk_B @ X1) | (zip_tseitin_0 @ sk_B @ X0))),
% 16.82/17.05      inference('simplify_reflect-', [status(thm)], ['192', '193'])).
% 16.82/17.05  thf('195', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 16.82/17.05      inference('condensation', [status(thm)], ['194'])).
% 16.82/17.05  thf('196', plain,
% 16.82/17.05      (![X0 : $i]: (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)),
% 16.82/17.05      inference('demod', [status(thm)], ['185', '195'])).
% 16.82/17.05  thf('197', plain,
% 16.82/17.05      (![X0 : $i]:
% 16.82/17.05         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 16.82/17.05          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 16.82/17.05      inference('demod', [status(thm)], ['182', '196'])).
% 16.82/17.05  thf('198', plain,
% 16.82/17.05      ((((sk_C) != (sk_C))
% 16.82/17.05        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 16.82/17.05      inference('sup-', [status(thm)], ['177', '197'])).
% 16.82/17.05  thf('199', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 16.82/17.05      inference('simplify', [status(thm)], ['198'])).
% 16.82/17.05  thf('200', plain, ($false), inference('demod', [status(thm)], ['38', '199'])).
% 16.82/17.05  
% 16.82/17.05  % SZS output end Refutation
% 16.82/17.05  
% 16.82/17.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
