%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cfAvAqC4yY

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:05 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 231 expanded)
%              Number of leaves         :   23 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  726 (3121 expanded)
%              Number of equality atoms :   68 ( 233 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

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

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( v1_partfun1 @ X10 @ X11 )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A_1 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A_1 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X16 = X13 )
      | ~ ( r1_partfun1 @ X16 @ X13 )
      | ~ ( v1_partfun1 @ X13 @ X14 )
      | ~ ( v1_partfun1 @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A_1 )
      | ~ ( v1_partfun1 @ sk_D @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A_1 )
      | ~ ( v1_partfun1 @ sk_D @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_partfun1 @ sk_C @ sk_A_1 )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_partfun1 @ sk_C @ sk_A_1 )
    | ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( v1_partfun1 @ X10 @ X11 )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ( v1_partfun1 @ sk_C @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_C @ sk_A_1 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('32',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('33',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['31','36'])).

thf('38',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('39',plain,(
    ~ ( r2_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('45',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('47',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['32','35'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','51'])).

thf('53',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('59',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['32','35'])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('63',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','63'])).

thf('65',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('67',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_relset_1 @ X6 @ X7 @ X8 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['67'])).

thf('69',plain,(
    r2_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','69'])).

thf('71',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('72',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('73',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['64','73'])).

thf('75',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('76',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['37','76'])).

thf('78',plain,(
    sk_C = sk_D ),
    inference(clc,[status(thm)],['24','77'])).

thf('79',plain,(
    r2_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['66','68'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','78','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cfAvAqC4yY
% 0.12/0.37  % Computer   : n002.cluster.edu
% 0.12/0.37  % Model      : x86_64 x86_64
% 0.12/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.37  % Memory     : 8042.1875MB
% 0.12/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.37  % CPULimit   : 60
% 0.12/0.37  % DateTime   : Tue Dec  1 15:48:52 EST 2020
% 0.12/0.37  % CPUTime    : 
% 0.12/0.37  % Running portfolio for 600 s
% 0.12/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.37  % Number of cores: 8
% 0.23/0.37  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 273 iterations in 0.132s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.61  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.37/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.61  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.61  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.37/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.61  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.37/0.61  thf(t142_funct_2, conjecture,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61       ( ![D:$i]:
% 0.37/0.61         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.61             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61           ( ( r1_partfun1 @ C @ D ) =>
% 0.37/0.61             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.37/0.61               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.61        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.61            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61          ( ![D:$i]:
% 0.37/0.61            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.61                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61              ( ( r1_partfun1 @ C @ D ) =>
% 0.37/0.61                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.37/0.61                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.37/0.61  thf('0', plain, (~ (r2_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_D)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(cc5_funct_2, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.37/0.61       ( ![C:$i]:
% 0.37/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.37/0.61             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.37/0.61          | (v1_partfun1 @ X10 @ X11)
% 0.37/0.61          | ~ (v1_funct_2 @ X10 @ X11 @ X12)
% 0.37/0.61          | ~ (v1_funct_1 @ X10)
% 0.37/0.61          | (v1_xboole_0 @ X12))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      (((v1_xboole_0 @ sk_B)
% 0.37/0.61        | ~ (v1_funct_1 @ sk_D)
% 0.37/0.61        | ~ (v1_funct_2 @ sk_D @ sk_A_1 @ sk_B)
% 0.37/0.61        | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.61  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A_1 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('7', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.37/0.61      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.37/0.61  thf('8', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t148_partfun1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61       ( ![D:$i]:
% 0.37/0.61         ( ( ( v1_funct_1 @ D ) & 
% 0.37/0.61             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.37/0.61               ( r1_partfun1 @ C @ D ) ) =>
% 0.37/0.61             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.61         (~ (v1_funct_1 @ X13)
% 0.37/0.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.37/0.61          | ((X16) = (X13))
% 0.37/0.61          | ~ (r1_partfun1 @ X16 @ X13)
% 0.37/0.61          | ~ (v1_partfun1 @ X13 @ X14)
% 0.37/0.61          | ~ (v1_partfun1 @ X16 @ X14)
% 0.37/0.61          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.37/0.61          | ~ (v1_funct_1 @ X16))),
% 0.37/0.61      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (v1_funct_1 @ X0)
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 0.37/0.61          | ~ (v1_partfun1 @ X0 @ sk_A_1)
% 0.37/0.61          | ~ (v1_partfun1 @ sk_D @ sk_A_1)
% 0.37/0.61          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.37/0.61          | ((X0) = (sk_D))
% 0.37/0.61          | ~ (v1_funct_1 @ sk_D))),
% 0.37/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.61  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (v1_funct_1 @ X0)
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 0.37/0.61          | ~ (v1_partfun1 @ X0 @ sk_A_1)
% 0.37/0.61          | ~ (v1_partfun1 @ sk_D @ sk_A_1)
% 0.37/0.61          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.37/0.61          | ((X0) = (sk_D)))),
% 0.37/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ sk_B)
% 0.37/0.61          | ((X0) = (sk_D))
% 0.37/0.61          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.37/0.61          | ~ (v1_partfun1 @ X0 @ sk_A_1)
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 0.37/0.61          | ~ (v1_funct_1 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['7', '12'])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.61        | ~ (v1_partfun1 @ sk_C @ sk_A_1)
% 0.37/0.61        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.37/0.61        | ((sk_C) = (sk_D))
% 0.37/0.61        | (v1_xboole_0 @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '13'])).
% 0.37/0.61  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('16', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      ((~ (v1_partfun1 @ sk_C @ sk_A_1)
% 0.37/0.61        | ((sk_C) = (sk_D))
% 0.37/0.61        | (v1_xboole_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('19', plain,
% 0.37/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.37/0.61          | (v1_partfun1 @ X10 @ X11)
% 0.37/0.61          | ~ (v1_funct_2 @ X10 @ X11 @ X12)
% 0.37/0.61          | ~ (v1_funct_1 @ X10)
% 0.37/0.61          | (v1_xboole_0 @ X12))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.37/0.61  thf('20', plain,
% 0.37/0.61      (((v1_xboole_0 @ sk_B)
% 0.37/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.61        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 0.37/0.61        | (v1_partfun1 @ sk_C @ sk_A_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.61  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('23', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_C @ sk_A_1))),
% 0.37/0.61      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.37/0.61  thf('24', plain, (((v1_xboole_0 @ sk_B) | ((sk_C) = (sk_D)))),
% 0.37/0.61      inference('clc', [status(thm)], ['17', '23'])).
% 0.37/0.61  thf(l13_xboole_0, axiom,
% 0.37/0.61    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.61  thf('25', plain,
% 0.37/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.61  thf('27', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['25', '26'])).
% 0.37/0.61  thf('28', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A_1) = (k1_xboole_0)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.37/0.61      inference('split', [status(esa)], ['28'])).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      ((![X0 : $i]:
% 0.37/0.61          (((X0) != (k1_xboole_0))
% 0.37/0.61           | ~ (v1_xboole_0 @ X0)
% 0.37/0.61           | ~ (v1_xboole_0 @ sk_B)))
% 0.37/0.61         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['27', '29'])).
% 0.37/0.61  thf('31', plain,
% 0.37/0.61      (((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.37/0.61         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.37/0.61      inference('simplify', [status(thm)], ['30'])).
% 0.37/0.61  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.37/0.61  thf('32', plain, ((v1_xboole_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.37/0.61  thf('33', plain, ((v1_xboole_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.37/0.61  thf('34', plain,
% 0.37/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.61  thf('35', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.61  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.61      inference('demod', [status(thm)], ['32', '35'])).
% 0.37/0.61  thf('37', plain,
% 0.37/0.61      ((~ (v1_xboole_0 @ sk_B)) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.37/0.61      inference('simplify_reflect+', [status(thm)], ['31', '36'])).
% 0.37/0.61  thf('38', plain,
% 0.37/0.61      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('split', [status(esa)], ['28'])).
% 0.37/0.61  thf('39', plain, (~ (r2_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_D)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('40', plain,
% 0.37/0.61      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D))
% 0.37/0.61         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.61  thf('41', plain,
% 0.37/0.61      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('split', [status(esa)], ['28'])).
% 0.37/0.61  thf('42', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('43', plain,
% 0.37/0.61      (((m1_subset_1 @ sk_C @ 
% 0.37/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.37/0.61         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('sup+', [status(thm)], ['41', '42'])).
% 0.37/0.61  thf(cc1_subset_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_xboole_0 @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.37/0.61  thf('44', plain,
% 0.37/0.61      (![X4 : $i, X5 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.37/0.61          | (v1_xboole_0 @ X4)
% 0.37/0.61          | ~ (v1_xboole_0 @ X5))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.37/0.61  thf('45', plain,
% 0.37/0.61      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 0.37/0.61         | (v1_xboole_0 @ sk_C))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.61  thf(t113_zfmisc_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.37/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.61  thf('46', plain,
% 0.37/0.61      (![X2 : $i, X3 : $i]:
% 0.37/0.61         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.37/0.61  thf('47', plain,
% 0.37/0.61      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.37/0.61      inference('simplify', [status(thm)], ['46'])).
% 0.37/0.61  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.61      inference('demod', [status(thm)], ['32', '35'])).
% 0.37/0.61  thf('49', plain, (((v1_xboole_0 @ sk_C)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('demod', [status(thm)], ['45', '47', '48'])).
% 0.37/0.61  thf('50', plain,
% 0.37/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.61  thf('51', plain,
% 0.37/0.61      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.61  thf('52', plain,
% 0.37/0.61      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ sk_D))
% 0.37/0.61         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('demod', [status(thm)], ['40', '51'])).
% 0.37/0.61  thf('53', plain,
% 0.37/0.61      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('split', [status(esa)], ['28'])).
% 0.37/0.61  thf('54', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('55', plain,
% 0.37/0.61      (((m1_subset_1 @ sk_D @ 
% 0.37/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.37/0.61         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('sup+', [status(thm)], ['53', '54'])).
% 0.37/0.61  thf('56', plain,
% 0.37/0.61      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.37/0.61      inference('simplify', [status(thm)], ['46'])).
% 0.37/0.61  thf('57', plain,
% 0.37/0.61      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.37/0.61         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('demod', [status(thm)], ['55', '56'])).
% 0.37/0.61  thf('58', plain,
% 0.37/0.61      (![X4 : $i, X5 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.37/0.61          | (v1_xboole_0 @ X4)
% 0.37/0.61          | ~ (v1_xboole_0 @ X5))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.37/0.61  thf('59', plain,
% 0.37/0.61      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_D)))
% 0.37/0.61         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.61  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.61      inference('demod', [status(thm)], ['32', '35'])).
% 0.37/0.61  thf('61', plain, (((v1_xboole_0 @ sk_D)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('demod', [status(thm)], ['59', '60'])).
% 0.37/0.61  thf('62', plain,
% 0.37/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.61  thf('63', plain,
% 0.37/0.61      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.61  thf('64', plain,
% 0.37/0.61      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0))
% 0.37/0.61         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('demod', [status(thm)], ['52', '63'])).
% 0.37/0.61  thf('65', plain,
% 0.37/0.61      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('split', [status(esa)], ['28'])).
% 0.37/0.61  thf('66', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(reflexivity_r2_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.37/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.37/0.61  thf('67', plain,
% 0.37/0.61      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.61         ((r2_relset_1 @ X6 @ X7 @ X8 @ X8)
% 0.37/0.61          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.37/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.37/0.61      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.37/0.61  thf('68', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.37/0.61      inference('condensation', [status(thm)], ['67'])).
% 0.37/0.61  thf('69', plain, ((r2_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_C)),
% 0.37/0.61      inference('sup-', [status(thm)], ['66', '68'])).
% 0.37/0.61  thf('70', plain,
% 0.37/0.61      (((r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C))
% 0.37/0.61         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('sup+', [status(thm)], ['65', '69'])).
% 0.37/0.61  thf('71', plain,
% 0.37/0.61      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.61  thf('72', plain,
% 0.37/0.61      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.61  thf('73', plain,
% 0.37/0.61      (((r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0))
% 0.37/0.61         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.37/0.61      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.37/0.61  thf('74', plain, (~ (((sk_A_1) = (k1_xboole_0)))),
% 0.37/0.61      inference('demod', [status(thm)], ['64', '73'])).
% 0.37/0.61  thf('75', plain,
% 0.37/0.61      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A_1) = (k1_xboole_0)))),
% 0.37/0.61      inference('split', [status(esa)], ['28'])).
% 0.37/0.61  thf('76', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.37/0.61      inference('sat_resolution*', [status(thm)], ['74', '75'])).
% 0.37/0.61  thf('77', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.61      inference('simpl_trail', [status(thm)], ['37', '76'])).
% 0.37/0.61  thf('78', plain, (((sk_C) = (sk_D))),
% 0.37/0.61      inference('clc', [status(thm)], ['24', '77'])).
% 0.37/0.61  thf('79', plain, ((r2_relset_1 @ sk_A_1 @ sk_B @ sk_C @ sk_C)),
% 0.37/0.61      inference('sup-', [status(thm)], ['66', '68'])).
% 0.37/0.61  thf('80', plain, ($false),
% 0.37/0.61      inference('demod', [status(thm)], ['0', '78', '79'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
