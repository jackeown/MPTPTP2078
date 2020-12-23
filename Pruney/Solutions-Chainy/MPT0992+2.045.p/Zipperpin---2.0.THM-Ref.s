%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WnhrwgM1Zy

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:41 EST 2020

% Result     : Theorem 15.98s
% Output     : Refutation 15.98s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 899 expanded)
%              Number of leaves         :   42 ( 277 expanded)
%              Depth                    :   22
%              Number of atoms          : 1532 (14926 expanded)
%              Number of equality atoms :  119 ( 865 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X42 @ X43 @ X41 @ X44 ) ) ) ),
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
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ( ( k2_partfun1 @ X46 @ X47 @ X45 @ X48 )
        = ( k7_relat_1 @ X45 @ X48 ) ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X42 @ X43 @ X41 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X32 )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
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

thf('46',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('53',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('54',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('64',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('65',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('70',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('75',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('77',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('80',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('82',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('85',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ( ( k2_partfun1 @ X46 @ X47 @ X45 @ X48 )
        = ( k7_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('87',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X17 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('91',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('92',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['86','93'])).

thf('95',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','94'])).

thf('96',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('97',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('98',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('99',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('100',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('101',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('102',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','94'])).

thf('103',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('104',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('105',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','92'])).

thf('108',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['90','91'])).

thf('111',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('113',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','113'])).

thf('115',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('119',plain,(
    ! [X33: $i] :
      ( zip_tseitin_0 @ X33 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('121',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['117','123'])).

thf('125',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['65','75','80','95','96','97','98','99','100','101','102','103','124'])).

thf('126',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('127',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['125','126'])).

thf('128',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['62','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['60','128'])).

thf('130',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('131',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('133',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['131','132'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('134',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['39','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('140',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ sk_B @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('145',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('146',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ~ ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['62','127'])).

thf('150',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['143','150'])).

thf('152',plain,
    ( ( sk_C != sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['138','151'])).

thf('153',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    $false ),
    inference(demod,[status(thm)],['38','153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WnhrwgM1Zy
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 15.98/16.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 15.98/16.23  % Solved by: fo/fo7.sh
% 15.98/16.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.98/16.23  % done 10304 iterations in 15.760s
% 15.98/16.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 15.98/16.23  % SZS output start Refutation
% 15.98/16.23  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 15.98/16.23  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 15.98/16.23  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 15.98/16.23  thf(sk_C_type, type, sk_C: $i).
% 15.98/16.23  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 15.98/16.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.98/16.23  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 15.98/16.23  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 15.98/16.23  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 15.98/16.23  thf(sk_A_type, type, sk_A: $i).
% 15.98/16.23  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 15.98/16.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.98/16.23  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 15.98/16.23  thf(sk_B_type, type, sk_B: $i).
% 15.98/16.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.98/16.23  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 15.98/16.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.98/16.23  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 15.98/16.23  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 15.98/16.23  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 15.98/16.23  thf(sk_D_type, type, sk_D: $i).
% 15.98/16.23  thf(t38_funct_2, conjecture,
% 15.98/16.23    (![A:$i,B:$i,C:$i,D:$i]:
% 15.98/16.23     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 15.98/16.23         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.98/16.23       ( ( r1_tarski @ C @ A ) =>
% 15.98/16.23         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 15.98/16.23           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 15.98/16.23             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 15.98/16.23             ( m1_subset_1 @
% 15.98/16.23               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 15.98/16.23               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 15.98/16.23  thf(zf_stmt_0, negated_conjecture,
% 15.98/16.23    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 15.98/16.23        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 15.98/16.23            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.98/16.23          ( ( r1_tarski @ C @ A ) =>
% 15.98/16.23            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 15.98/16.23              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 15.98/16.23                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 15.98/16.23                ( m1_subset_1 @
% 15.98/16.23                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 15.98/16.23                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 15.98/16.23    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 15.98/16.23  thf('0', plain,
% 15.98/16.23      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 15.98/16.23        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 15.98/16.23             sk_B)
% 15.98/16.23        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 15.98/16.23             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf('1', plain,
% 15.98/16.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf(dt_k2_partfun1, axiom,
% 15.98/16.23    (![A:$i,B:$i,C:$i,D:$i]:
% 15.98/16.23     ( ( ( v1_funct_1 @ C ) & 
% 15.98/16.23         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.98/16.23       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 15.98/16.23         ( m1_subset_1 @
% 15.98/16.23           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 15.98/16.23           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 15.98/16.23  thf('2', plain,
% 15.98/16.23      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 15.98/16.23         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 15.98/16.23          | ~ (v1_funct_1 @ X41)
% 15.98/16.23          | (v1_funct_1 @ (k2_partfun1 @ X42 @ X43 @ X41 @ X44)))),
% 15.98/16.23      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 15.98/16.23  thf('3', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 15.98/16.23          | ~ (v1_funct_1 @ sk_D))),
% 15.98/16.23      inference('sup-', [status(thm)], ['1', '2'])).
% 15.98/16.23  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf('5', plain,
% 15.98/16.23      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 15.98/16.23      inference('demod', [status(thm)], ['3', '4'])).
% 15.98/16.23  thf('6', plain,
% 15.98/16.23      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 15.98/16.23        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 15.98/16.23             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 15.98/16.23      inference('demod', [status(thm)], ['0', '5'])).
% 15.98/16.23  thf('7', plain,
% 15.98/16.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf(redefinition_k2_partfun1, axiom,
% 15.98/16.23    (![A:$i,B:$i,C:$i,D:$i]:
% 15.98/16.23     ( ( ( v1_funct_1 @ C ) & 
% 15.98/16.23         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.98/16.23       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 15.98/16.23  thf('8', plain,
% 15.98/16.23      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 15.98/16.23         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 15.98/16.23          | ~ (v1_funct_1 @ X45)
% 15.98/16.23          | ((k2_partfun1 @ X46 @ X47 @ X45 @ X48) = (k7_relat_1 @ X45 @ X48)))),
% 15.98/16.23      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 15.98/16.23  thf('9', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 15.98/16.23          | ~ (v1_funct_1 @ sk_D))),
% 15.98/16.23      inference('sup-', [status(thm)], ['7', '8'])).
% 15.98/16.23  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf('11', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 15.98/16.23      inference('demod', [status(thm)], ['9', '10'])).
% 15.98/16.23  thf('12', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 15.98/16.23      inference('demod', [status(thm)], ['9', '10'])).
% 15.98/16.23  thf('13', plain,
% 15.98/16.23      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 15.98/16.23        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 15.98/16.23             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 15.98/16.23      inference('demod', [status(thm)], ['6', '11', '12'])).
% 15.98/16.23  thf('14', plain,
% 15.98/16.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf('15', plain,
% 15.98/16.23      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 15.98/16.23         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 15.98/16.23          | ~ (v1_funct_1 @ X41)
% 15.98/16.23          | (m1_subset_1 @ (k2_partfun1 @ X42 @ X43 @ X41 @ X44) @ 
% 15.98/16.23             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 15.98/16.23      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 15.98/16.23  thf('16', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 15.98/16.23           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 15.98/16.23          | ~ (v1_funct_1 @ sk_D))),
% 15.98/16.23      inference('sup-', [status(thm)], ['14', '15'])).
% 15.98/16.23  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf('18', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 15.98/16.23          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.98/16.23      inference('demod', [status(thm)], ['16', '17'])).
% 15.98/16.23  thf('19', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 15.98/16.23      inference('demod', [status(thm)], ['9', '10'])).
% 15.98/16.23  thf('20', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.98/16.23          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.98/16.23      inference('demod', [status(thm)], ['18', '19'])).
% 15.98/16.23  thf(cc2_relset_1, axiom,
% 15.98/16.23    (![A:$i,B:$i,C:$i]:
% 15.98/16.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.98/16.23       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 15.98/16.23  thf('21', plain,
% 15.98/16.23      (![X24 : $i, X25 : $i, X26 : $i]:
% 15.98/16.23         ((v5_relat_1 @ X24 @ X26)
% 15.98/16.23          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 15.98/16.23      inference('cnf', [status(esa)], [cc2_relset_1])).
% 15.98/16.23  thf('22', plain,
% 15.98/16.23      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 15.98/16.23      inference('sup-', [status(thm)], ['20', '21'])).
% 15.98/16.23  thf(d19_relat_1, axiom,
% 15.98/16.23    (![A:$i,B:$i]:
% 15.98/16.23     ( ( v1_relat_1 @ B ) =>
% 15.98/16.23       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 15.98/16.23  thf('23', plain,
% 15.98/16.23      (![X11 : $i, X12 : $i]:
% 15.98/16.23         (~ (v5_relat_1 @ X11 @ X12)
% 15.98/16.23          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 15.98/16.23          | ~ (v1_relat_1 @ X11))),
% 15.98/16.23      inference('cnf', [status(esa)], [d19_relat_1])).
% 15.98/16.23  thf('24', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 15.98/16.23          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 15.98/16.23      inference('sup-', [status(thm)], ['22', '23'])).
% 15.98/16.23  thf('25', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.98/16.23          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.98/16.23      inference('demod', [status(thm)], ['18', '19'])).
% 15.98/16.23  thf(cc1_relset_1, axiom,
% 15.98/16.23    (![A:$i,B:$i,C:$i]:
% 15.98/16.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.98/16.23       ( v1_relat_1 @ C ) ))).
% 15.98/16.23  thf('26', plain,
% 15.98/16.23      (![X21 : $i, X22 : $i, X23 : $i]:
% 15.98/16.23         ((v1_relat_1 @ X21)
% 15.98/16.23          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 15.98/16.23      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.98/16.23  thf('27', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 15.98/16.23      inference('sup-', [status(thm)], ['25', '26'])).
% 15.98/16.23  thf('28', plain,
% 15.98/16.23      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 15.98/16.23      inference('demod', [status(thm)], ['24', '27'])).
% 15.98/16.23  thf(t87_relat_1, axiom,
% 15.98/16.23    (![A:$i,B:$i]:
% 15.98/16.23     ( ( v1_relat_1 @ B ) =>
% 15.98/16.23       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 15.98/16.23  thf('29', plain,
% 15.98/16.23      (![X15 : $i, X16 : $i]:
% 15.98/16.23         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X15 @ X16)) @ X16)
% 15.98/16.23          | ~ (v1_relat_1 @ X15))),
% 15.98/16.23      inference('cnf', [status(esa)], [t87_relat_1])).
% 15.98/16.23  thf(t11_relset_1, axiom,
% 15.98/16.23    (![A:$i,B:$i,C:$i]:
% 15.98/16.23     ( ( v1_relat_1 @ C ) =>
% 15.98/16.23       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 15.98/16.23           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 15.98/16.23         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 15.98/16.23  thf('30', plain,
% 15.98/16.23      (![X30 : $i, X31 : $i, X32 : $i]:
% 15.98/16.23         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 15.98/16.23          | ~ (r1_tarski @ (k2_relat_1 @ X30) @ X32)
% 15.98/16.23          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 15.98/16.23          | ~ (v1_relat_1 @ X30))),
% 15.98/16.23      inference('cnf', [status(esa)], [t11_relset_1])).
% 15.98/16.23  thf('31', plain,
% 15.98/16.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.98/16.23         (~ (v1_relat_1 @ X1)
% 15.98/16.23          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 15.98/16.23          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 15.98/16.23             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 15.98/16.23          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 15.98/16.23      inference('sup-', [status(thm)], ['29', '30'])).
% 15.98/16.23  thf('32', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.98/16.23           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 15.98/16.23          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 15.98/16.23          | ~ (v1_relat_1 @ sk_D))),
% 15.98/16.23      inference('sup-', [status(thm)], ['28', '31'])).
% 15.98/16.23  thf('33', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 15.98/16.23      inference('sup-', [status(thm)], ['25', '26'])).
% 15.98/16.23  thf('34', plain,
% 15.98/16.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf('35', plain,
% 15.98/16.23      (![X21 : $i, X22 : $i, X23 : $i]:
% 15.98/16.23         ((v1_relat_1 @ X21)
% 15.98/16.23          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 15.98/16.23      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.98/16.23  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 15.98/16.23      inference('sup-', [status(thm)], ['34', '35'])).
% 15.98/16.23  thf('37', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.98/16.23          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 15.98/16.23      inference('demod', [status(thm)], ['32', '33', '36'])).
% 15.98/16.23  thf('38', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 15.98/16.23      inference('demod', [status(thm)], ['13', '37'])).
% 15.98/16.23  thf('39', plain, ((r1_tarski @ sk_C @ sk_A)),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf(d1_funct_2, axiom,
% 15.98/16.23    (![A:$i,B:$i,C:$i]:
% 15.98/16.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.98/16.23       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.98/16.23           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 15.98/16.23             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 15.98/16.23         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.98/16.23           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 15.98/16.23             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 15.98/16.23  thf(zf_stmt_1, axiom,
% 15.98/16.23    (![B:$i,A:$i]:
% 15.98/16.23     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.98/16.23       ( zip_tseitin_0 @ B @ A ) ))).
% 15.98/16.23  thf('40', plain,
% 15.98/16.23      (![X33 : $i, X34 : $i]:
% 15.98/16.23         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.98/16.23  thf(t4_subset_1, axiom,
% 15.98/16.23    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 15.98/16.23  thf('41', plain,
% 15.98/16.23      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 15.98/16.23      inference('cnf', [status(esa)], [t4_subset_1])).
% 15.98/16.23  thf('42', plain,
% 15.98/16.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.98/16.23         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (zip_tseitin_0 @ X0 @ X2))),
% 15.98/16.23      inference('sup+', [status(thm)], ['40', '41'])).
% 15.98/16.23  thf(t3_subset, axiom,
% 15.98/16.23    (![A:$i,B:$i]:
% 15.98/16.23     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 15.98/16.23  thf('43', plain,
% 15.98/16.23      (![X5 : $i, X6 : $i]:
% 15.98/16.23         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 15.98/16.23      inference('cnf', [status(esa)], [t3_subset])).
% 15.98/16.23  thf('44', plain,
% 15.98/16.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.98/16.23         ((zip_tseitin_0 @ X1 @ X2) | (r1_tarski @ X1 @ X0))),
% 15.98/16.23      inference('sup-', [status(thm)], ['42', '43'])).
% 15.98/16.23  thf('45', plain,
% 15.98/16.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 15.98/16.23  thf(zf_stmt_3, axiom,
% 15.98/16.23    (![C:$i,B:$i,A:$i]:
% 15.98/16.23     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 15.98/16.23       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 15.98/16.23  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 15.98/16.23  thf(zf_stmt_5, axiom,
% 15.98/16.23    (![A:$i,B:$i,C:$i]:
% 15.98/16.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.98/16.23       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 15.98/16.23         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.98/16.23           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 15.98/16.23             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 15.98/16.23  thf('46', plain,
% 15.98/16.23      (![X38 : $i, X39 : $i, X40 : $i]:
% 15.98/16.23         (~ (zip_tseitin_0 @ X38 @ X39)
% 15.98/16.23          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 15.98/16.23          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.98/16.23  thf('47', plain,
% 15.98/16.23      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 15.98/16.23      inference('sup-', [status(thm)], ['45', '46'])).
% 15.98/16.23  thf('48', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 15.98/16.23      inference('sup-', [status(thm)], ['44', '47'])).
% 15.98/16.23  thf('49', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf('50', plain,
% 15.98/16.23      (![X35 : $i, X36 : $i, X37 : $i]:
% 15.98/16.23         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 15.98/16.23          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 15.98/16.23          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.98/16.23  thf('51', plain,
% 15.98/16.23      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 15.98/16.23        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 15.98/16.23      inference('sup-', [status(thm)], ['49', '50'])).
% 15.98/16.23  thf('52', plain,
% 15.98/16.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf(redefinition_k1_relset_1, axiom,
% 15.98/16.23    (![A:$i,B:$i,C:$i]:
% 15.98/16.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.98/16.23       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 15.98/16.23  thf('53', plain,
% 15.98/16.23      (![X27 : $i, X28 : $i, X29 : $i]:
% 15.98/16.23         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 15.98/16.23          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 15.98/16.23      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.98/16.23  thf('54', plain,
% 15.98/16.23      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 15.98/16.23      inference('sup-', [status(thm)], ['52', '53'])).
% 15.98/16.23  thf('55', plain,
% 15.98/16.23      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.98/16.23      inference('demod', [status(thm)], ['51', '54'])).
% 15.98/16.23  thf('56', plain,
% 15.98/16.23      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.98/16.23      inference('sup-', [status(thm)], ['48', '55'])).
% 15.98/16.23  thf('57', plain,
% 15.98/16.23      (![X33 : $i, X34 : $i]:
% 15.98/16.23         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.98/16.23  thf(t3_xboole_1, axiom,
% 15.98/16.23    (![A:$i]:
% 15.98/16.23     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 15.98/16.23  thf('58', plain,
% 15.98/16.23      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 15.98/16.23      inference('cnf', [status(esa)], [t3_xboole_1])).
% 15.98/16.23  thf('59', plain,
% 15.98/16.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.98/16.23         (~ (r1_tarski @ X1 @ X0)
% 15.98/16.23          | (zip_tseitin_0 @ X0 @ X2)
% 15.98/16.23          | ((X1) = (k1_xboole_0)))),
% 15.98/16.23      inference('sup-', [status(thm)], ['57', '58'])).
% 15.98/16.23  thf('60', plain,
% 15.98/16.23      (![X0 : $i, X1 : $i]:
% 15.98/16.23         (((sk_A) = (k1_relat_1 @ sk_D))
% 15.98/16.23          | ((sk_B) = (k1_xboole_0))
% 15.98/16.23          | (zip_tseitin_0 @ X0 @ X1))),
% 15.98/16.23      inference('sup-', [status(thm)], ['56', '59'])).
% 15.98/16.23  thf('61', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf('62', plain,
% 15.98/16.23      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.98/16.23      inference('split', [status(esa)], ['61'])).
% 15.98/16.23  thf('63', plain,
% 15.98/16.23      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('split', [status(esa)], ['61'])).
% 15.98/16.23  thf('64', plain,
% 15.98/16.23      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 15.98/16.23        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 15.98/16.23             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 15.98/16.23      inference('demod', [status(thm)], ['0', '5'])).
% 15.98/16.23  thf('65', plain,
% 15.98/16.23      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 15.98/16.23            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 15.98/16.23         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 15.98/16.23              sk_B)))
% 15.98/16.23         <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('sup-', [status(thm)], ['63', '64'])).
% 15.98/16.23  thf('66', plain,
% 15.98/16.23      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('split', [status(esa)], ['61'])).
% 15.98/16.23  thf('67', plain,
% 15.98/16.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf('68', plain,
% 15.98/16.23      (((m1_subset_1 @ sk_D @ 
% 15.98/16.23         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 15.98/16.23         <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('sup+', [status(thm)], ['66', '67'])).
% 15.98/16.23  thf(t113_zfmisc_1, axiom,
% 15.98/16.23    (![A:$i,B:$i]:
% 15.98/16.23     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 15.98/16.23       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 15.98/16.23  thf('69', plain,
% 15.98/16.23      (![X2 : $i, X3 : $i]:
% 15.98/16.23         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 15.98/16.23      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 15.98/16.23  thf('70', plain,
% 15.98/16.23      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 15.98/16.23      inference('simplify', [status(thm)], ['69'])).
% 15.98/16.23  thf('71', plain,
% 15.98/16.23      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 15.98/16.23         <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('demod', [status(thm)], ['68', '70'])).
% 15.98/16.23  thf('72', plain,
% 15.98/16.23      (![X5 : $i, X6 : $i]:
% 15.98/16.23         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 15.98/16.23      inference('cnf', [status(esa)], [t3_subset])).
% 15.98/16.23  thf('73', plain,
% 15.98/16.23      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('sup-', [status(thm)], ['71', '72'])).
% 15.98/16.23  thf('74', plain,
% 15.98/16.23      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 15.98/16.23      inference('cnf', [status(esa)], [t3_xboole_1])).
% 15.98/16.23  thf('75', plain,
% 15.98/16.23      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('sup-', [status(thm)], ['73', '74'])).
% 15.98/16.23  thf('76', plain,
% 15.98/16.23      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('split', [status(esa)], ['61'])).
% 15.98/16.23  thf('77', plain, ((r1_tarski @ sk_C @ sk_A)),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf('78', plain,
% 15.98/16.23      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('sup+', [status(thm)], ['76', '77'])).
% 15.98/16.23  thf('79', plain,
% 15.98/16.23      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 15.98/16.23      inference('cnf', [status(esa)], [t3_xboole_1])).
% 15.98/16.23  thf('80', plain,
% 15.98/16.23      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('sup-', [status(thm)], ['78', '79'])).
% 15.98/16.23  thf('81', plain,
% 15.98/16.23      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('sup-', [status(thm)], ['73', '74'])).
% 15.98/16.23  thf('82', plain, ((v1_funct_1 @ sk_D)),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.98/16.23  thf('83', plain,
% 15.98/16.23      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('sup+', [status(thm)], ['81', '82'])).
% 15.98/16.23  thf('84', plain,
% 15.98/16.23      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 15.98/16.23      inference('cnf', [status(esa)], [t4_subset_1])).
% 15.98/16.23  thf('85', plain,
% 15.98/16.23      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 15.98/16.23         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 15.98/16.23          | ~ (v1_funct_1 @ X45)
% 15.98/16.23          | ((k2_partfun1 @ X46 @ X47 @ X45 @ X48) = (k7_relat_1 @ X45 @ X48)))),
% 15.98/16.23      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 15.98/16.23  thf('86', plain,
% 15.98/16.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.98/16.23         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 15.98/16.23            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 15.98/16.23          | ~ (v1_funct_1 @ k1_xboole_0))),
% 15.98/16.23      inference('sup-', [status(thm)], ['84', '85'])).
% 15.98/16.23  thf(t88_relat_1, axiom,
% 15.98/16.23    (![A:$i,B:$i]:
% 15.98/16.23     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 15.98/16.23  thf('87', plain,
% 15.98/16.23      (![X17 : $i, X18 : $i]:
% 15.98/16.23         ((r1_tarski @ (k7_relat_1 @ X17 @ X18) @ X17) | ~ (v1_relat_1 @ X17))),
% 15.98/16.23      inference('cnf', [status(esa)], [t88_relat_1])).
% 15.98/16.23  thf('88', plain,
% 15.98/16.23      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 15.98/16.23      inference('cnf', [status(esa)], [t3_xboole_1])).
% 15.98/16.23  thf('89', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         (~ (v1_relat_1 @ k1_xboole_0)
% 15.98/16.23          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 15.98/16.23      inference('sup-', [status(thm)], ['87', '88'])).
% 15.98/16.23  thf('90', plain,
% 15.98/16.23      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 15.98/16.23      inference('cnf', [status(esa)], [t4_subset_1])).
% 15.98/16.23  thf('91', plain,
% 15.98/16.23      (![X21 : $i, X22 : $i, X23 : $i]:
% 15.98/16.23         ((v1_relat_1 @ X21)
% 15.98/16.23          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 15.98/16.23      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.98/16.23  thf('92', plain, ((v1_relat_1 @ k1_xboole_0)),
% 15.98/16.23      inference('sup-', [status(thm)], ['90', '91'])).
% 15.98/16.23  thf('93', plain,
% 15.98/16.23      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.98/16.23      inference('demod', [status(thm)], ['89', '92'])).
% 15.98/16.23  thf('94', plain,
% 15.98/16.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.98/16.23         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 15.98/16.23          | ~ (v1_funct_1 @ k1_xboole_0))),
% 15.98/16.23      inference('demod', [status(thm)], ['86', '93'])).
% 15.98/16.23  thf('95', plain,
% 15.98/16.23      ((![X0 : $i, X1 : $i, X2 : $i]:
% 15.98/16.23          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 15.98/16.23         <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('sup-', [status(thm)], ['83', '94'])).
% 15.98/16.23  thf('96', plain,
% 15.98/16.23      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('sup-', [status(thm)], ['78', '79'])).
% 15.98/16.23  thf('97', plain,
% 15.98/16.23      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 15.98/16.23      inference('simplify', [status(thm)], ['69'])).
% 15.98/16.23  thf('98', plain,
% 15.98/16.23      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 15.98/16.23      inference('cnf', [status(esa)], [t4_subset_1])).
% 15.98/16.23  thf('99', plain,
% 15.98/16.23      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('split', [status(esa)], ['61'])).
% 15.98/16.23  thf('100', plain,
% 15.98/16.23      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('sup-', [status(thm)], ['73', '74'])).
% 15.98/16.23  thf('101', plain,
% 15.98/16.23      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('sup-', [status(thm)], ['78', '79'])).
% 15.98/16.23  thf('102', plain,
% 15.98/16.23      ((![X0 : $i, X1 : $i, X2 : $i]:
% 15.98/16.23          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 15.98/16.23         <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('sup-', [status(thm)], ['83', '94'])).
% 15.98/16.23  thf('103', plain,
% 15.98/16.23      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.98/16.23      inference('sup-', [status(thm)], ['78', '79'])).
% 15.98/16.23  thf('104', plain,
% 15.98/16.23      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 15.98/16.23      inference('cnf', [status(esa)], [t4_subset_1])).
% 15.98/16.23  thf('105', plain,
% 15.98/16.23      (![X27 : $i, X28 : $i, X29 : $i]:
% 15.98/16.23         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 15.98/16.23          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 15.98/16.23      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.98/16.23  thf('106', plain,
% 15.98/16.23      (![X0 : $i, X1 : $i]:
% 15.98/16.23         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 15.98/16.23      inference('sup-', [status(thm)], ['104', '105'])).
% 15.98/16.23  thf('107', plain,
% 15.98/16.23      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.98/16.23      inference('demod', [status(thm)], ['89', '92'])).
% 15.98/16.23  thf('108', plain,
% 15.98/16.23      (![X15 : $i, X16 : $i]:
% 15.98/16.23         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X15 @ X16)) @ X16)
% 15.98/16.23          | ~ (v1_relat_1 @ X15))),
% 15.98/16.23      inference('cnf', [status(esa)], [t87_relat_1])).
% 15.98/16.23  thf('109', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         ((r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 15.98/16.23          | ~ (v1_relat_1 @ k1_xboole_0))),
% 15.98/16.23      inference('sup+', [status(thm)], ['107', '108'])).
% 15.98/16.23  thf('110', plain, ((v1_relat_1 @ k1_xboole_0)),
% 15.98/16.23      inference('sup-', [status(thm)], ['90', '91'])).
% 15.98/16.23  thf('111', plain,
% 15.98/16.23      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 15.98/16.23      inference('demod', [status(thm)], ['109', '110'])).
% 15.98/16.23  thf('112', plain,
% 15.98/16.23      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 15.98/16.23      inference('cnf', [status(esa)], [t3_xboole_1])).
% 15.98/16.23  thf('113', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 15.98/16.23      inference('sup-', [status(thm)], ['111', '112'])).
% 15.98/16.23  thf('114', plain,
% 15.98/16.23      (![X0 : $i, X1 : $i]:
% 15.98/16.23         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 15.98/16.23      inference('demod', [status(thm)], ['106', '113'])).
% 15.98/16.23  thf('115', plain,
% 15.98/16.23      (![X35 : $i, X36 : $i, X37 : $i]:
% 15.98/16.23         (((X35) != (k1_relset_1 @ X35 @ X36 @ X37))
% 15.98/16.23          | (v1_funct_2 @ X37 @ X35 @ X36)
% 15.98/16.23          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.98/16.23  thf('116', plain,
% 15.98/16.23      (![X0 : $i, X1 : $i]:
% 15.98/16.23         (((X1) != (k1_xboole_0))
% 15.98/16.23          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 15.98/16.23          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 15.98/16.23      inference('sup-', [status(thm)], ['114', '115'])).
% 15.98/16.23  thf('117', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 15.98/16.23          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 15.98/16.23      inference('simplify', [status(thm)], ['116'])).
% 15.98/16.23  thf('118', plain,
% 15.98/16.23      (![X33 : $i, X34 : $i]:
% 15.98/16.23         ((zip_tseitin_0 @ X33 @ X34) | ((X34) != (k1_xboole_0)))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.98/16.23  thf('119', plain, (![X33 : $i]: (zip_tseitin_0 @ X33 @ k1_xboole_0)),
% 15.98/16.23      inference('simplify', [status(thm)], ['118'])).
% 15.98/16.23  thf('120', plain,
% 15.98/16.23      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 15.98/16.23      inference('cnf', [status(esa)], [t4_subset_1])).
% 15.98/16.23  thf('121', plain,
% 15.98/16.23      (![X38 : $i, X39 : $i, X40 : $i]:
% 15.98/16.23         (~ (zip_tseitin_0 @ X38 @ X39)
% 15.98/16.23          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 15.98/16.23          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.98/16.23  thf('122', plain,
% 15.98/16.23      (![X0 : $i, X1 : $i]:
% 15.98/16.23         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 15.98/16.23      inference('sup-', [status(thm)], ['120', '121'])).
% 15.98/16.23  thf('123', plain,
% 15.98/16.23      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 15.98/16.23      inference('sup-', [status(thm)], ['119', '122'])).
% 15.98/16.23  thf('124', plain,
% 15.98/16.23      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 15.98/16.23      inference('demod', [status(thm)], ['117', '123'])).
% 15.98/16.23  thf('125', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 15.98/16.23      inference('demod', [status(thm)],
% 15.98/16.23                ['65', '75', '80', '95', '96', '97', '98', '99', '100', '101', 
% 15.98/16.23                 '102', '103', '124'])).
% 15.98/16.23  thf('126', plain,
% 15.98/16.23      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 15.98/16.23      inference('split', [status(esa)], ['61'])).
% 15.98/16.23  thf('127', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 15.98/16.23      inference('sat_resolution*', [status(thm)], ['125', '126'])).
% 15.98/16.23  thf('128', plain, (((sk_B) != (k1_xboole_0))),
% 15.98/16.23      inference('simpl_trail', [status(thm)], ['62', '127'])).
% 15.98/16.23  thf('129', plain,
% 15.98/16.23      (![X0 : $i, X1 : $i]:
% 15.98/16.23         (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X0 @ X1))),
% 15.98/16.23      inference('simplify_reflect-', [status(thm)], ['60', '128'])).
% 15.98/16.23  thf('130', plain,
% 15.98/16.23      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 15.98/16.23      inference('sup-', [status(thm)], ['45', '46'])).
% 15.98/16.23  thf('131', plain,
% 15.98/16.23      ((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 15.98/16.23      inference('sup-', [status(thm)], ['129', '130'])).
% 15.98/16.23  thf('132', plain,
% 15.98/16.23      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.98/16.23      inference('demod', [status(thm)], ['51', '54'])).
% 15.98/16.23  thf('133', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 15.98/16.23      inference('clc', [status(thm)], ['131', '132'])).
% 15.98/16.23  thf(t91_relat_1, axiom,
% 15.98/16.23    (![A:$i,B:$i]:
% 15.98/16.23     ( ( v1_relat_1 @ B ) =>
% 15.98/16.23       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 15.98/16.23         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 15.98/16.23  thf('134', plain,
% 15.98/16.23      (![X19 : $i, X20 : $i]:
% 15.98/16.23         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 15.98/16.23          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 15.98/16.23          | ~ (v1_relat_1 @ X20))),
% 15.98/16.23      inference('cnf', [status(esa)], [t91_relat_1])).
% 15.98/16.23  thf('135', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         (~ (r1_tarski @ X0 @ sk_A)
% 15.98/16.23          | ~ (v1_relat_1 @ sk_D)
% 15.98/16.23          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 15.98/16.23      inference('sup-', [status(thm)], ['133', '134'])).
% 15.98/16.23  thf('136', plain, ((v1_relat_1 @ sk_D)),
% 15.98/16.23      inference('sup-', [status(thm)], ['34', '35'])).
% 15.98/16.23  thf('137', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         (~ (r1_tarski @ X0 @ sk_A)
% 15.98/16.23          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 15.98/16.23      inference('demod', [status(thm)], ['135', '136'])).
% 15.98/16.23  thf('138', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 15.98/16.23      inference('sup-', [status(thm)], ['39', '137'])).
% 15.98/16.23  thf('139', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.98/16.23          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 15.98/16.23      inference('demod', [status(thm)], ['32', '33', '36'])).
% 15.98/16.23  thf('140', plain,
% 15.98/16.23      (![X27 : $i, X28 : $i, X29 : $i]:
% 15.98/16.23         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 15.98/16.23          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 15.98/16.23      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.98/16.23  thf('141', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         ((k1_relset_1 @ X0 @ sk_B @ (k7_relat_1 @ sk_D @ X0))
% 15.98/16.23           = (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 15.98/16.23      inference('sup-', [status(thm)], ['139', '140'])).
% 15.98/16.23  thf('142', plain,
% 15.98/16.23      (![X35 : $i, X36 : $i, X37 : $i]:
% 15.98/16.23         (((X35) != (k1_relset_1 @ X35 @ X36 @ X37))
% 15.98/16.23          | (v1_funct_2 @ X37 @ X35 @ X36)
% 15.98/16.23          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.98/16.23  thf('143', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 15.98/16.23          | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 15.98/16.23          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 15.98/16.23      inference('sup-', [status(thm)], ['141', '142'])).
% 15.98/16.23  thf('144', plain,
% 15.98/16.23      (![X33 : $i, X34 : $i]:
% 15.98/16.23         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.98/16.23  thf('145', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.98/16.23          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 15.98/16.23      inference('demod', [status(thm)], ['32', '33', '36'])).
% 15.98/16.23  thf('146', plain,
% 15.98/16.23      (![X38 : $i, X39 : $i, X40 : $i]:
% 15.98/16.23         (~ (zip_tseitin_0 @ X38 @ X39)
% 15.98/16.23          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 15.98/16.23          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 15.98/16.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.98/16.23  thf('147', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 15.98/16.23          | ~ (zip_tseitin_0 @ sk_B @ X0))),
% 15.98/16.23      inference('sup-', [status(thm)], ['145', '146'])).
% 15.98/16.23  thf('148', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         (((sk_B) = (k1_xboole_0))
% 15.98/16.23          | (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0))),
% 15.98/16.23      inference('sup-', [status(thm)], ['144', '147'])).
% 15.98/16.23  thf('149', plain, (((sk_B) != (k1_xboole_0))),
% 15.98/16.23      inference('simpl_trail', [status(thm)], ['62', '127'])).
% 15.98/16.23  thf('150', plain,
% 15.98/16.23      (![X0 : $i]: (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)),
% 15.98/16.23      inference('simplify_reflect-', [status(thm)], ['148', '149'])).
% 15.98/16.23  thf('151', plain,
% 15.98/16.23      (![X0 : $i]:
% 15.98/16.23         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 15.98/16.23          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 15.98/16.23      inference('demod', [status(thm)], ['143', '150'])).
% 15.98/16.23  thf('152', plain,
% 15.98/16.23      ((((sk_C) != (sk_C))
% 15.98/16.23        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 15.98/16.23      inference('sup-', [status(thm)], ['138', '151'])).
% 15.98/16.23  thf('153', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 15.98/16.23      inference('simplify', [status(thm)], ['152'])).
% 15.98/16.23  thf('154', plain, ($false), inference('demod', [status(thm)], ['38', '153'])).
% 15.98/16.23  
% 15.98/16.23  % SZS output end Refutation
% 15.98/16.23  
% 15.98/16.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
