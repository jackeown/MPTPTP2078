%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D5awTqLxQF

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:05 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 385 expanded)
%              Number of leaves         :   23 ( 120 expanded)
%              Depth                    :   17
%              Number of atoms          :  703 (4886 expanded)
%              Number of equality atoms :   67 ( 408 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(t142_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X22 = X19 )
      | ~ ( r1_partfun1 @ X22 @ X19 )
      | ~ ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_partfun1 @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A_1 )
      | ~ ( v1_partfun1 @ sk_D @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A_1 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A_1 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('18',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('19',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['17','22'])).

thf('24',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('25',plain,(
    ~ ( r2_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('31',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','21'])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('37',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','37'])).

thf('39',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('45',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','21'])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','49'])).

thf('51',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('53',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 )
      | ( X12 != X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('54',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    r2_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','55'])).

thf('57',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('58',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('59',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['50','59'])).

thf('61',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('62',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['23','62'])).

thf('64',plain,(
    v1_partfun1 @ sk_D @ sk_A_1 ),
    inference(clc,[status(thm)],['10','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['4','64','65'])).

thf('67',plain,
    ( ( sk_C = sk_D )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ~ ( v1_partfun1 @ sk_C @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','66'])).

thf('68',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ( v1_partfun1 @ sk_C @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_C @ sk_A_1 ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['23','62'])).

thf('76',plain,(
    v1_partfun1 @ sk_C @ sk_A_1 ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    sk_C = sk_D ),
    inference(demod,[status(thm)],['67','68','76','77'])).

thf('79',plain,(
    r2_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['52','54'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','78','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D5awTqLxQF
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 288 iterations in 0.121s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.57  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.38/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.38/0.57  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.38/0.57  thf(t142_funct_2, conjecture,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57       ( ![D:$i]:
% 0.38/0.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57           ( ( r1_partfun1 @ C @ D ) =>
% 0.38/0.57             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.38/0.57               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57          ( ![D:$i]:
% 0.38/0.57            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.57                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57              ( ( r1_partfun1 @ C @ D ) =>
% 0.38/0.57                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.38/0.57                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.38/0.57  thf('0', plain, (~ (r2_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_D)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t148_partfun1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57       ( ![D:$i]:
% 0.38/0.57         ( ( ( v1_funct_1 @ D ) & 
% 0.38/0.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.38/0.57               ( r1_partfun1 @ C @ D ) ) =>
% 0.38/0.57             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.57         (~ (v1_funct_1 @ X19)
% 0.38/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.38/0.57          | ((X22) = (X19))
% 0.38/0.57          | ~ (r1_partfun1 @ X22 @ X19)
% 0.38/0.57          | ~ (v1_partfun1 @ X19 @ X20)
% 0.38/0.57          | ~ (v1_partfun1 @ X22 @ X20)
% 0.38/0.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.38/0.57          | ~ (v1_funct_1 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 0.38/0.57          | ~ (v1_partfun1 @ X0 @ sk_A_1)
% 0.38/0.57          | ~ (v1_partfun1 @ sk_D @ sk_A_1)
% 0.38/0.57          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.38/0.57          | ((X0) = (sk_D))
% 0.38/0.57          | ~ (v1_funct_1 @ sk_D))),
% 0.38/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(cc5_funct_2, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.38/0.57       ( ![C:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.38/0.57             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.38/0.57          | (v1_partfun1 @ X16 @ X17)
% 0.38/0.57          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.38/0.57          | ~ (v1_funct_1 @ X16)
% 0.38/0.57          | (v1_xboole_0 @ X18))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (((v1_xboole_0 @ sk_B)
% 0.38/0.57        | ~ (v1_funct_1 @ sk_D)
% 0.38/0.57        | ~ (v1_funct_2 @ sk_D @ sk_A_1 @ sk_B)
% 0.38/0.57        | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.57  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('10', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.38/0.57      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.38/0.57  thf(l13_xboole_0, axiom,
% 0.38/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf('14', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A_1) = (k1_xboole_0)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.38/0.57      inference('split', [status(esa)], ['14'])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      ((![X0 : $i]:
% 0.38/0.57          (((X0) != (k1_xboole_0))
% 0.38/0.57           | ~ (v1_xboole_0 @ X0)
% 0.38/0.57           | ~ (v1_xboole_0 @ sk_B)))
% 0.38/0.57         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['13', '15'])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.38/0.57         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['16'])).
% 0.38/0.57  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.38/0.57  thf('18', plain, ((v1_xboole_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.38/0.57  thf('19', plain, ((v1_xboole_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.57  thf('21', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.57      inference('demod', [status(thm)], ['18', '21'])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      ((~ (v1_xboole_0 @ sk_B)) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.38/0.57      inference('simplify_reflect+', [status(thm)], ['17', '22'])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('split', [status(esa)], ['14'])).
% 0.38/0.57  thf('25', plain, (~ (r2_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_D)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D))
% 0.38/0.57         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('split', [status(esa)], ['14'])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (((m1_subset_1 @ sk_C @ 
% 0.38/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.38/0.57         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.38/0.57  thf(cc1_subset_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      (![X7 : $i, X8 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.38/0.57          | (v1_xboole_0 @ X7)
% 0.38/0.57          | ~ (v1_xboole_0 @ X8))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 0.38/0.57         | (v1_xboole_0 @ sk_C))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.57  thf(t113_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i]:
% 0.38/0.57         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.38/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.57  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.57      inference('demod', [status(thm)], ['18', '21'])).
% 0.38/0.57  thf('35', plain, (((v1_xboole_0 @ sk_C)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('demod', [status(thm)], ['31', '33', '34'])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ sk_D))
% 0.38/0.57         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('demod', [status(thm)], ['26', '37'])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('split', [status(esa)], ['14'])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (((m1_subset_1 @ sk_D @ 
% 0.38/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.38/0.57         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['39', '40'])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.38/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.38/0.57         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (![X7 : $i, X8 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.38/0.57          | (v1_xboole_0 @ X7)
% 0.38/0.57          | ~ (v1_xboole_0 @ X8))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_D)))
% 0.38/0.57         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.57  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.57      inference('demod', [status(thm)], ['18', '21'])).
% 0.38/0.57  thf('47', plain, (((v1_xboole_0 @ sk_D)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.38/0.57  thf('48', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.57  thf('50', plain,
% 0.38/0.57      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0))
% 0.38/0.57         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('demod', [status(thm)], ['38', '49'])).
% 0.38/0.57  thf('51', plain,
% 0.38/0.57      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('split', [status(esa)], ['14'])).
% 0.38/0.57  thf('52', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_r2_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.38/0.57  thf('53', plain,
% 0.38/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.38/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.38/0.57          | (r2_relset_1 @ X13 @ X14 @ X12 @ X15)
% 0.38/0.57          | ((X12) != (X15)))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.38/0.57  thf('54', plain,
% 0.38/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.57         ((r2_relset_1 @ X13 @ X14 @ X15 @ X15)
% 0.38/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['53'])).
% 0.38/0.57  thf('55', plain, ((r2_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_C)),
% 0.38/0.57      inference('sup-', [status(thm)], ['52', '54'])).
% 0.38/0.57  thf('56', plain,
% 0.38/0.57      (((r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C))
% 0.38/0.57         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['51', '55'])).
% 0.38/0.57  thf('57', plain,
% 0.38/0.57      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.57  thf('58', plain,
% 0.38/0.57      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.57  thf('59', plain,
% 0.38/0.57      (((r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0))
% 0.38/0.57         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.38/0.57      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.38/0.57  thf('60', plain, (~ (((sk_A_1) = (k1_xboole_0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['50', '59'])).
% 0.38/0.57  thf('61', plain,
% 0.38/0.57      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A_1) = (k1_xboole_0)))),
% 0.38/0.57      inference('split', [status(esa)], ['14'])).
% 0.38/0.57  thf('62', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['60', '61'])).
% 0.38/0.57  thf('63', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['23', '62'])).
% 0.38/0.57  thf('64', plain, ((v1_partfun1 @ sk_D @ sk_A_1)),
% 0.38/0.57      inference('clc', [status(thm)], ['10', '63'])).
% 0.38/0.57  thf('65', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('66', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 0.38/0.57          | ~ (v1_partfun1 @ X0 @ sk_A_1)
% 0.38/0.57          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.38/0.57          | ((X0) = (sk_D)))),
% 0.38/0.57      inference('demod', [status(thm)], ['4', '64', '65'])).
% 0.38/0.57  thf('67', plain,
% 0.38/0.57      ((((sk_C) = (sk_D))
% 0.38/0.57        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.38/0.57        | ~ (v1_partfun1 @ sk_C @ sk_A_1)
% 0.38/0.57        | ~ (v1_funct_1 @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['1', '66'])).
% 0.38/0.57  thf('68', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('69', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('70', plain,
% 0.38/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.38/0.57          | (v1_partfun1 @ X16 @ X17)
% 0.38/0.57          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.38/0.57          | ~ (v1_funct_1 @ X16)
% 0.38/0.57          | (v1_xboole_0 @ X18))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.38/0.57  thf('71', plain,
% 0.38/0.57      (((v1_xboole_0 @ sk_B)
% 0.38/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.57        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 0.38/0.57        | (v1_partfun1 @ sk_C @ sk_A_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['69', '70'])).
% 0.38/0.57  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('73', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('74', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_C @ sk_A_1))),
% 0.38/0.57      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.38/0.57  thf('75', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['23', '62'])).
% 0.38/0.57  thf('76', plain, ((v1_partfun1 @ sk_C @ sk_A_1)),
% 0.38/0.57      inference('clc', [status(thm)], ['74', '75'])).
% 0.38/0.57  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('78', plain, (((sk_C) = (sk_D))),
% 0.38/0.57      inference('demod', [status(thm)], ['67', '68', '76', '77'])).
% 0.38/0.57  thf('79', plain, ((r2_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_C)),
% 0.38/0.57      inference('sup-', [status(thm)], ['52', '54'])).
% 0.38/0.57  thf('80', plain, ($false),
% 0.38/0.57      inference('demod', [status(thm)], ['0', '78', '79'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
