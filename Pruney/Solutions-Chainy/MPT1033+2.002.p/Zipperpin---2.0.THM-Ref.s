%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SjSSPBHWTH

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:04 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 232 expanded)
%              Number of leaves         :   23 (  73 expanded)
%              Depth                    :   18
%              Number of atoms          :  675 (3320 expanded)
%              Number of equality atoms :   56 ( 246 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X29 = X26 )
      | ~ ( r1_partfun1 @ X29 @ X26 )
      | ~ ( v1_partfun1 @ X26 @ X27 )
      | ~ ( v1_partfun1 @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
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
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['17','18'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('25',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('31',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','31'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('34',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('38',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('46',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('50',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','50'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','51'])).

thf('53',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('54',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['19','54'])).

thf('56',plain,(
    v1_partfun1 @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['10','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['4','56','57'])).

thf('59',plain,
    ( ( sk_C = sk_D )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','58'])).

thf('60',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['19','54'])).

thf('68',plain,(
    v1_partfun1 @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_C = sk_D ),
    inference(demod,[status(thm)],['59','60','68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['21'])).

thf('73',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SjSSPBHWTH
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.70  % Solved by: fo/fo7.sh
% 0.47/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.70  % done 402 iterations in 0.244s
% 0.47/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.70  % SZS output start Refutation
% 0.47/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.70  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.70  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.47/0.70  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.47/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.70  thf(t142_funct_2, conjecture,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.70       ( ![D:$i]:
% 0.47/0.70         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.70             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.70           ( ( r1_partfun1 @ C @ D ) =>
% 0.47/0.70             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.70               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.70        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.70            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.70          ( ![D:$i]:
% 0.47/0.70            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.70                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.70              ( ( r1_partfun1 @ C @ D ) =>
% 0.47/0.70                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.70                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.47/0.70    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.47/0.70  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('1', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('2', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(t148_partfun1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.70       ( ![D:$i]:
% 0.47/0.70         ( ( ( v1_funct_1 @ D ) & 
% 0.47/0.70             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.70           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.47/0.70               ( r1_partfun1 @ C @ D ) ) =>
% 0.47/0.70             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.47/0.70  thf('3', plain,
% 0.47/0.70      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.47/0.70         (~ (v1_funct_1 @ X26)
% 0.47/0.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.47/0.70          | ((X29) = (X26))
% 0.47/0.70          | ~ (r1_partfun1 @ X29 @ X26)
% 0.47/0.70          | ~ (v1_partfun1 @ X26 @ X27)
% 0.47/0.70          | ~ (v1_partfun1 @ X29 @ X27)
% 0.47/0.70          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.47/0.70          | ~ (v1_funct_1 @ X29))),
% 0.47/0.70      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.47/0.70  thf('4', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_funct_1 @ X0)
% 0.47/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.47/0.70          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.47/0.70          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.47/0.70          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.47/0.70          | ((X0) = (sk_D))
% 0.47/0.70          | ~ (v1_funct_1 @ sk_D))),
% 0.47/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.70  thf('5', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(cc5_funct_2, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.70       ( ![C:$i]:
% 0.47/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.70           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.47/0.70             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.47/0.70  thf('6', plain,
% 0.47/0.70      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.47/0.70          | (v1_partfun1 @ X23 @ X24)
% 0.47/0.70          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.47/0.70          | ~ (v1_funct_1 @ X23)
% 0.47/0.70          | (v1_xboole_0 @ X25))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.47/0.70  thf('7', plain,
% 0.47/0.70      (((v1_xboole_0 @ sk_B_1)
% 0.47/0.70        | ~ (v1_funct_1 @ sk_D)
% 0.47/0.70        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_1)
% 0.47/0.70        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.47/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.70  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('10', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.47/0.70      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.47/0.70  thf(l13_xboole_0, axiom,
% 0.47/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.70  thf('11', plain,
% 0.47/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.70  thf('12', plain,
% 0.47/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.70  thf('13', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.70  thf('14', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('15', plain,
% 0.47/0.70      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.47/0.70      inference('split', [status(esa)], ['14'])).
% 0.47/0.70  thf('16', plain,
% 0.47/0.70      ((![X0 : $i]:
% 0.47/0.70          (((X0) != (k1_xboole_0))
% 0.47/0.70           | ~ (v1_xboole_0 @ X0)
% 0.47/0.70           | ~ (v1_xboole_0 @ sk_B_1)))
% 0.47/0.70         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['13', '15'])).
% 0.47/0.70  thf('17', plain,
% 0.47/0.70      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.47/0.70         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.47/0.70      inference('simplify', [status(thm)], ['16'])).
% 0.47/0.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.70  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.70  thf('19', plain,
% 0.47/0.70      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.47/0.70      inference('simplify_reflect+', [status(thm)], ['17', '18'])).
% 0.47/0.70  thf(t4_subset_1, axiom,
% 0.47/0.70    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.47/0.70  thf('20', plain,
% 0.47/0.70      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.47/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.47/0.70  thf(reflexivity_r2_relset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.70     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.70       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.47/0.70  thf('21', plain,
% 0.47/0.70      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.70         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 0.47/0.70          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.47/0.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.47/0.70      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.47/0.70  thf('22', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.47/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.47/0.70      inference('condensation', [status(thm)], ['21'])).
% 0.47/0.70  thf('23', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('sup-', [status(thm)], ['20', '22'])).
% 0.47/0.70  thf('24', plain,
% 0.47/0.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('split', [status(esa)], ['14'])).
% 0.47/0.70  thf('25', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('26', plain,
% 0.47/0.70      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_D))
% 0.47/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.70  thf('27', plain,
% 0.47/0.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('split', [status(esa)], ['14'])).
% 0.47/0.70  thf('28', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('29', plain,
% 0.47/0.70      (((m1_subset_1 @ sk_C @ 
% 0.47/0.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.47/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('sup+', [status(thm)], ['27', '28'])).
% 0.47/0.70  thf(t113_zfmisc_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.70       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.70  thf('30', plain,
% 0.47/0.70      (![X2 : $i, X3 : $i]:
% 0.47/0.70         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.70  thf('31', plain,
% 0.47/0.70      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['30'])).
% 0.47/0.70  thf('32', plain,
% 0.47/0.70      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.47/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('demod', [status(thm)], ['29', '31'])).
% 0.47/0.70  thf(cc1_subset_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_xboole_0 @ A ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.47/0.70  thf('33', plain,
% 0.47/0.70      (![X6 : $i, X7 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.47/0.70          | (v1_xboole_0 @ X6)
% 0.47/0.70          | ~ (v1_xboole_0 @ X7))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.47/0.70  thf('34', plain,
% 0.47/0.70      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C)))
% 0.47/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.70  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.70  thf('36', plain, (((v1_xboole_0 @ sk_C)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('demod', [status(thm)], ['34', '35'])).
% 0.47/0.70  thf('37', plain,
% 0.47/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.70  thf('38', plain,
% 0.47/0.70      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['36', '37'])).
% 0.47/0.70  thf('39', plain,
% 0.47/0.70      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ sk_D))
% 0.47/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('demod', [status(thm)], ['26', '38'])).
% 0.47/0.70  thf('40', plain,
% 0.47/0.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('split', [status(esa)], ['14'])).
% 0.47/0.70  thf('41', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('42', plain,
% 0.47/0.70      (((m1_subset_1 @ sk_D @ 
% 0.47/0.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.47/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('sup+', [status(thm)], ['40', '41'])).
% 0.47/0.70  thf('43', plain,
% 0.47/0.70      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['30'])).
% 0.47/0.70  thf('44', plain,
% 0.47/0.70      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.47/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('demod', [status(thm)], ['42', '43'])).
% 0.47/0.70  thf('45', plain,
% 0.47/0.70      (![X6 : $i, X7 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.47/0.70          | (v1_xboole_0 @ X6)
% 0.47/0.70          | ~ (v1_xboole_0 @ X7))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.47/0.70  thf('46', plain,
% 0.47/0.70      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_D)))
% 0.47/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['44', '45'])).
% 0.47/0.70  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.70  thf('48', plain, (((v1_xboole_0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('demod', [status(thm)], ['46', '47'])).
% 0.47/0.70  thf('49', plain,
% 0.47/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.70  thf('50', plain,
% 0.47/0.70      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.47/0.70  thf('51', plain,
% 0.47/0.70      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.47/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.70      inference('demod', [status(thm)], ['39', '50'])).
% 0.47/0.70  thf('52', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['23', '51'])).
% 0.47/0.70  thf('53', plain,
% 0.47/0.70      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.47/0.70      inference('split', [status(esa)], ['14'])).
% 0.47/0.70  thf('54', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.47/0.70      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 0.47/0.70  thf('55', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.47/0.70      inference('simpl_trail', [status(thm)], ['19', '54'])).
% 0.47/0.70  thf('56', plain, ((v1_partfun1 @ sk_D @ sk_A)),
% 0.47/0.70      inference('clc', [status(thm)], ['10', '55'])).
% 0.47/0.70  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('58', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_funct_1 @ X0)
% 0.47/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.47/0.70          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.47/0.70          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.47/0.70          | ((X0) = (sk_D)))),
% 0.47/0.70      inference('demod', [status(thm)], ['4', '56', '57'])).
% 0.47/0.70  thf('59', plain,
% 0.47/0.70      ((((sk_C) = (sk_D))
% 0.47/0.70        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.47/0.70        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.47/0.70        | ~ (v1_funct_1 @ sk_C))),
% 0.47/0.70      inference('sup-', [status(thm)], ['1', '58'])).
% 0.47/0.70  thf('60', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('61', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('62', plain,
% 0.47/0.70      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.47/0.70          | (v1_partfun1 @ X23 @ X24)
% 0.47/0.70          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.47/0.70          | ~ (v1_funct_1 @ X23)
% 0.47/0.70          | (v1_xboole_0 @ X25))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.47/0.70  thf('63', plain,
% 0.47/0.70      (((v1_xboole_0 @ sk_B_1)
% 0.47/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.70        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.47/0.70        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.47/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.47/0.70  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('65', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('66', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.47/0.70      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.47/0.70  thf('67', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.47/0.70      inference('simpl_trail', [status(thm)], ['19', '54'])).
% 0.47/0.70  thf('68', plain, ((v1_partfun1 @ sk_C @ sk_A)),
% 0.47/0.70      inference('clc', [status(thm)], ['66', '67'])).
% 0.47/0.70  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('70', plain, (((sk_C) = (sk_D))),
% 0.47/0.70      inference('demod', [status(thm)], ['59', '60', '68', '69'])).
% 0.47/0.70  thf('71', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('72', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.47/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.47/0.70      inference('condensation', [status(thm)], ['21'])).
% 0.47/0.70  thf('73', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C)),
% 0.47/0.70      inference('sup-', [status(thm)], ['71', '72'])).
% 0.47/0.70  thf('74', plain, ($false),
% 0.47/0.70      inference('demod', [status(thm)], ['0', '70', '73'])).
% 0.47/0.70  
% 0.47/0.70  % SZS output end Refutation
% 0.47/0.70  
% 0.47/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
