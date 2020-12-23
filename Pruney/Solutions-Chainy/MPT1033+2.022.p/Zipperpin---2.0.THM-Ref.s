%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xBGp1UeQS2

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:07 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  105 (1122 expanded)
%              Number of leaves         :   20 ( 307 expanded)
%              Depth                    :   20
%              Number of atoms          :  742 (22767 expanded)
%              Number of equality atoms :   59 (1267 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( v1_partfun1 @ X8 @ X9 )
      | ~ ( v1_funct_2 @ X8 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( X14 = X11 )
      | ~ ( r1_partfun1 @ X14 @ X11 )
      | ~ ( v1_partfun1 @ X11 @ X12 )
      | ~ ( v1_partfun1 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( v1_partfun1 @ X8 @ X9 )
      | ~ ( v1_funct_2 @ X8 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = sk_D ) ),
    inference(clc,[status(thm)],['20','26'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('29',plain,
    ( ( sk_C = sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C = sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_C = sk_D )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_relset_1 @ X4 @ X5 @ X6 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['36'])).

thf('38',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['3','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = sk_D ) ),
    inference(clc,[status(thm)],['20','26'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('45',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,
    ( ( sk_C = sk_D )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['3','41'])).

thf('51',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['36'])).

thf('56',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('58',plain,(
    r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C ),
    inference(simpl_trail,[status(thm)],['56','57'])).

thf('59',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','58'])).

thf('60',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['42','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = sk_D ) ),
    inference(clc,[status(thm)],['20','26'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('67',plain,
    ( ( sk_C = sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['3','41'])).

thf('69',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C ),
    inference(simpl_trail,[status(thm)],['56','57'])).

thf('71',plain,(
    sk_D = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['36'])).

thf('77',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('79',plain,(
    r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_D ),
    inference(simpl_trail,[status(thm)],['77','78'])).

thf('80',plain,(
    sk_D = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('81',plain,(
    sk_D = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('82',plain,(
    r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['72','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xBGp1UeQS2
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 111 iterations in 0.038s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.19/0.48  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(t142_funct_2, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48       ( ![D:$i]:
% 0.19/0.48         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.48             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48           ( ( r1_partfun1 @ C @ D ) =>
% 0.19/0.48             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.19/0.48               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.48        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.48            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48          ( ![D:$i]:
% 0.19/0.48            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.48                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48              ( ( r1_partfun1 @ C @ D ) =>
% 0.19/0.48                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.19/0.48                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.19/0.48  thf('0', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('2', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D))
% 0.19/0.48         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(cc5_funct_2, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.48       ( ![C:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.19/0.48             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.19/0.48          | (v1_partfun1 @ X8 @ X9)
% 0.19/0.48          | ~ (v1_funct_2 @ X8 @ X9 @ X10)
% 0.19/0.48          | ~ (v1_funct_1 @ X8)
% 0.19/0.48          | (v1_xboole_0 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B)
% 0.19/0.48        | ~ (v1_funct_1 @ sk_D)
% 0.19/0.48        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.19/0.48        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.48  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('10', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t148_partfun1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48       ( ![D:$i]:
% 0.19/0.48         ( ( ( v1_funct_1 @ D ) & 
% 0.19/0.48             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.19/0.48               ( r1_partfun1 @ C @ D ) ) =>
% 0.19/0.48             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.48         (~ (v1_funct_1 @ X11)
% 0.19/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.19/0.48          | ((X14) = (X11))
% 0.19/0.48          | ~ (r1_partfun1 @ X14 @ X11)
% 0.19/0.48          | ~ (v1_partfun1 @ X11 @ X12)
% 0.19/0.48          | ~ (v1_partfun1 @ X14 @ X12)
% 0.19/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.19/0.48          | ~ (v1_funct_1 @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v1_funct_1 @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.19/0.48          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.19/0.48          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.19/0.48          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.19/0.48          | ((X0) = (sk_D))
% 0.19/0.48          | ~ (v1_funct_1 @ sk_D))),
% 0.19/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.48  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v1_funct_1 @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.19/0.48          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.19/0.48          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.19/0.48          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.19/0.48          | ((X0) = (sk_D)))),
% 0.19/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ sk_B)
% 0.19/0.48          | ((X0) = (sk_D))
% 0.19/0.48          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.19/0.48          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.19/0.48          | ~ (v1_funct_1 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '15'])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      ((~ (v1_funct_1 @ sk_C)
% 0.19/0.48        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.19/0.48        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.19/0.48        | ((sk_C) = (sk_D))
% 0.19/0.48        | (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['4', '16'])).
% 0.19/0.48  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('19', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      ((~ (v1_partfun1 @ sk_C @ sk_A)
% 0.19/0.48        | ((sk_C) = (sk_D))
% 0.19/0.48        | (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.19/0.48          | (v1_partfun1 @ X8 @ X9)
% 0.19/0.48          | ~ (v1_funct_2 @ X8 @ X9 @ X10)
% 0.19/0.48          | ~ (v1_funct_1 @ X8)
% 0.19/0.48          | (v1_xboole_0 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B)
% 0.19/0.48        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.48        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.19/0.48        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.48  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('25', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('26', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.19/0.48  thf('27', plain, (((v1_xboole_0 @ sk_B) | ((sk_C) = (sk_D)))),
% 0.19/0.48      inference('clc', [status(thm)], ['20', '26'])).
% 0.19/0.48  thf(l13_xboole_0, axiom,
% 0.19/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.48  thf('29', plain, ((((sk_C) = (sk_D)) | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (sk_D))))
% 0.19/0.48         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.48  thf('32', plain, ((((sk_C) = (sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.19/0.48  thf('33', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C))
% 0.19/0.48         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(reflexivity_r2_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.48         ((r2_relset_1 @ X4 @ X5 @ X6 @ X6)
% 0.19/0.48          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.19/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.19/0.48      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.19/0.48      inference('condensation', [status(thm)], ['36'])).
% 0.19/0.48  thf('38', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.19/0.48      inference('sup-', [status(thm)], ['35', '37'])).
% 0.19/0.48  thf('39', plain, ((((sk_B) = (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['34', '38'])).
% 0.19/0.48  thf('40', plain, ((((sk_A) = (k1_xboole_0))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('41', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('42', plain, (~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D)),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['3', '41'])).
% 0.19/0.48  thf('43', plain, (((v1_xboole_0 @ sk_B) | ((sk_C) = (sk_D)))),
% 0.19/0.48      inference('clc', [status(thm)], ['20', '26'])).
% 0.19/0.48  thf('44', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(cc4_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_xboole_0 @ A ) =>
% 0.19/0.48       ( ![C:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.48           ( v1_xboole_0 @ C ) ) ) ))).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ X1)
% 0.19/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 0.19/0.48          | (v1_xboole_0 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.19/0.48  thf('46', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.48  thf('47', plain, ((((sk_C) = (sk_D)) | (v1_xboole_0 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['43', '46'])).
% 0.19/0.48  thf('48', plain,
% 0.19/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.48  thf('49', plain, ((((sk_C) = (sk_D)) | ((sk_C) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.48  thf('50', plain, (~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D)),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['3', '41'])).
% 0.19/0.48  thf('51', plain,
% 0.19/0.48      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C)
% 0.19/0.48        | ((sk_C) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.48  thf('52', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('53', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('54', plain,
% 0.19/0.48      (((m1_subset_1 @ sk_C @ 
% 0.19/0.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.19/0.48         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['52', '53'])).
% 0.19/0.48  thf('55', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.19/0.48      inference('condensation', [status(thm)], ['36'])).
% 0.19/0.48  thf('56', plain,
% 0.19/0.48      (((r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C))
% 0.19/0.48         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['54', '55'])).
% 0.19/0.48  thf('57', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('58', plain, ((r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C)),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['56', '57'])).
% 0.19/0.48  thf('59', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['51', '58'])).
% 0.19/0.48  thf('60', plain, (~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ sk_D)),
% 0.19/0.48      inference('demod', [status(thm)], ['42', '59'])).
% 0.19/0.48  thf('61', plain, (((v1_xboole_0 @ sk_B) | ((sk_C) = (sk_D)))),
% 0.19/0.48      inference('clc', [status(thm)], ['20', '26'])).
% 0.19/0.48  thf('62', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('63', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ X1)
% 0.19/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 0.19/0.48          | (v1_xboole_0 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.19/0.48  thf('64', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['62', '63'])).
% 0.19/0.48  thf('65', plain, ((((sk_C) = (sk_D)) | (v1_xboole_0 @ sk_D))),
% 0.19/0.48      inference('sup-', [status(thm)], ['61', '64'])).
% 0.19/0.48  thf('66', plain,
% 0.19/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.48  thf('67', plain, ((((sk_C) = (sk_D)) | ((sk_D) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['65', '66'])).
% 0.19/0.48  thf('68', plain, (~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D)),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['3', '41'])).
% 0.19/0.48  thf('69', plain,
% 0.19/0.48      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C)
% 0.19/0.48        | ((sk_D) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['67', '68'])).
% 0.19/0.48  thf('70', plain, ((r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C)),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['56', '57'])).
% 0.19/0.48  thf('71', plain, (((sk_D) = (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['69', '70'])).
% 0.19/0.48  thf('72', plain,
% 0.19/0.48      (~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('demod', [status(thm)], ['60', '71'])).
% 0.19/0.48  thf('73', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('74', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('75', plain,
% 0.19/0.48      (((m1_subset_1 @ sk_D @ 
% 0.19/0.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.19/0.48         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['73', '74'])).
% 0.19/0.48  thf('76', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.19/0.48      inference('condensation', [status(thm)], ['36'])).
% 0.19/0.48  thf('77', plain,
% 0.19/0.48      (((r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_D))
% 0.19/0.48         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['75', '76'])).
% 0.19/0.48  thf('78', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('79', plain, ((r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_D)),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['77', '78'])).
% 0.19/0.48  thf('80', plain, (((sk_D) = (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['69', '70'])).
% 0.19/0.48  thf('81', plain, (((sk_D) = (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['69', '70'])).
% 0.19/0.48  thf('82', plain,
% 0.19/0.48      ((r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.19/0.48  thf('83', plain, ($false), inference('demod', [status(thm)], ['72', '82'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.34/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
