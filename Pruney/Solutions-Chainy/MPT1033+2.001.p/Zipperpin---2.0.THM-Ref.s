%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3oF5BeAKTr

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:04 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 225 expanded)
%              Number of leaves         :   22 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  906 (3549 expanded)
%              Number of equality atoms :   74 ( 268 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( v1_partfun1 @ X11 @ X12 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( X17 = X14 )
      | ~ ( r1_partfun1 @ X17 @ X14 )
      | ~ ( v1_partfun1 @ X14 @ X15 )
      | ~ ( v1_partfun1 @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
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
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
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
    ( ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( v1_partfun1 @ X11 @ X12 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
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
    | ( sk_A = k1_xboole_0 ) ),
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('35',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

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

thf('43',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( X17 = X14 )
      | ~ ( r1_partfun1 @ X17 @ X14 )
      | ~ ( v1_partfun1 @ X14 @ X15 )
      | ~ ( v1_partfun1 @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_partfun1 @ X2 @ k1_xboole_0 )
      | ~ ( v1_partfun1 @ X1 @ k1_xboole_0 )
      | ~ ( r1_partfun1 @ X2 @ X1 )
      | ( X2 = X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('56',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_partfun1 @ X2 @ k1_xboole_0 )
      | ~ ( v1_partfun1 @ X1 @ k1_xboole_0 )
      | ~ ( r1_partfun1 @ X2 @ X1 )
      | ( X2 = X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( v1_funct_1 @ sk_D )
        | ( X0 = sk_D )
        | ~ ( r1_partfun1 @ X0 @ sk_D )
        | ~ ( v1_partfun1 @ sk_D @ k1_xboole_0 )
        | ~ ( v1_partfun1 @ X0 @ k1_xboole_0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('61',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('62',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_partfun1 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('63',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v1_partfun1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_D )
        | ~ ( r1_partfun1 @ X0 @ sk_D )
        | ~ ( v1_partfun1 @ X0 @ k1_xboole_0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58','59','66'])).

thf('68',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ~ ( r1_partfun1 @ sk_C @ sk_D )
      | ( sk_C = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','67'])).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','42'])).

thf('72',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('73',plain,
    ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_C = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69','70','73','74'])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','42'])).

thf('77',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('78',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ( r2_relset_1 @ X5 @ X6 @ X4 @ X7 )
      | ( X4 != X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('79',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_relset_1 @ X5 @ X6 @ X7 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( r2_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( r2_relset_1 @ k1_xboole_0 @ X0 @ sk_C @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','80'])).

thf('82',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['36','75','81'])).

thf('83',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('84',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['33','84'])).

thf('86',plain,(
    sk_C = sk_D ),
    inference(clc,[status(thm)],['24','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_relset_1 @ X5 @ X6 @ X7 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('89',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['0','86','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3oF5BeAKTr
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:17:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.44/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.69  % Solved by: fo/fo7.sh
% 0.44/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.69  % done 442 iterations in 0.223s
% 0.44/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.69  % SZS output start Refutation
% 0.44/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.69  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.69  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.44/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.69  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.44/0.69  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.44/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.69  thf(t142_funct_2, conjecture,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.69       ( ![D:$i]:
% 0.44/0.69         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.69             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.69           ( ( r1_partfun1 @ C @ D ) =>
% 0.44/0.69             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.44/0.69               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.44/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.69    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.69        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.69            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.69          ( ![D:$i]:
% 0.44/0.69            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.69                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.69              ( ( r1_partfun1 @ C @ D ) =>
% 0.44/0.69                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.44/0.69                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.44/0.69    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.44/0.69  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('1', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('2', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(cc5_funct_2, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.69       ( ![C:$i]:
% 0.44/0.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.69           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.44/0.69             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.44/0.69  thf('3', plain,
% 0.44/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.44/0.69          | (v1_partfun1 @ X11 @ X12)
% 0.44/0.69          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 0.44/0.69          | ~ (v1_funct_1 @ X11)
% 0.44/0.69          | (v1_xboole_0 @ X13))),
% 0.44/0.69      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.69  thf('4', plain,
% 0.44/0.69      (((v1_xboole_0 @ sk_B)
% 0.44/0.69        | ~ (v1_funct_1 @ sk_D)
% 0.44/0.69        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.44/0.69        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.44/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.69  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('7', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.44/0.69      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.44/0.69  thf('8', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(t148_partfun1, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( ( v1_funct_1 @ C ) & 
% 0.44/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.69       ( ![D:$i]:
% 0.44/0.69         ( ( ( v1_funct_1 @ D ) & 
% 0.44/0.69             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.69           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.44/0.69               ( r1_partfun1 @ C @ D ) ) =>
% 0.44/0.69             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.44/0.69  thf('9', plain,
% 0.44/0.69      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.69         (~ (v1_funct_1 @ X14)
% 0.44/0.69          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.44/0.69          | ((X17) = (X14))
% 0.44/0.69          | ~ (r1_partfun1 @ X17 @ X14)
% 0.44/0.69          | ~ (v1_partfun1 @ X14 @ X15)
% 0.44/0.69          | ~ (v1_partfun1 @ X17 @ X15)
% 0.44/0.69          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.44/0.69          | ~ (v1_funct_1 @ X17))),
% 0.44/0.69      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.44/0.69  thf('10', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         (~ (v1_funct_1 @ X0)
% 0.44/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.44/0.69          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.44/0.69          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.44/0.69          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.44/0.69          | ((X0) = (sk_D))
% 0.44/0.69          | ~ (v1_funct_1 @ sk_D))),
% 0.44/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.69  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('12', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         (~ (v1_funct_1 @ X0)
% 0.44/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.44/0.69          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.44/0.69          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.44/0.69          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.44/0.69          | ((X0) = (sk_D)))),
% 0.44/0.69      inference('demod', [status(thm)], ['10', '11'])).
% 0.44/0.69  thf('13', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((v1_xboole_0 @ sk_B)
% 0.44/0.69          | ((X0) = (sk_D))
% 0.44/0.69          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.44/0.69          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.44/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.44/0.69          | ~ (v1_funct_1 @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['7', '12'])).
% 0.44/0.69  thf('14', plain,
% 0.44/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.44/0.69        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.44/0.69        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.44/0.69        | ((sk_C) = (sk_D))
% 0.44/0.69        | (v1_xboole_0 @ sk_B))),
% 0.44/0.69      inference('sup-', [status(thm)], ['1', '13'])).
% 0.44/0.69  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('16', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('17', plain,
% 0.44/0.69      ((~ (v1_partfun1 @ sk_C @ sk_A)
% 0.44/0.69        | ((sk_C) = (sk_D))
% 0.44/0.69        | (v1_xboole_0 @ sk_B))),
% 0.44/0.69      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.44/0.69  thf('18', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('19', plain,
% 0.44/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.44/0.69          | (v1_partfun1 @ X11 @ X12)
% 0.44/0.69          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 0.44/0.69          | ~ (v1_funct_1 @ X11)
% 0.44/0.69          | (v1_xboole_0 @ X13))),
% 0.44/0.69      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.69  thf('20', plain,
% 0.44/0.69      (((v1_xboole_0 @ sk_B)
% 0.44/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.44/0.69        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.44/0.69        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.44/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.69  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('23', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.44/0.69      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.44/0.69  thf('24', plain, (((v1_xboole_0 @ sk_B) | ((sk_C) = (sk_D)))),
% 0.44/0.69      inference('clc', [status(thm)], ['17', '23'])).
% 0.44/0.69  thf(l13_xboole_0, axiom,
% 0.44/0.69    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.69  thf('25', plain,
% 0.44/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.69  thf('26', plain,
% 0.44/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.69  thf('27', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]:
% 0.44/0.69         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.44/0.69      inference('sup+', [status(thm)], ['25', '26'])).
% 0.44/0.69  thf('28', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('29', plain,
% 0.44/0.69      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.69      inference('split', [status(esa)], ['28'])).
% 0.44/0.69  thf('30', plain,
% 0.44/0.69      ((![X0 : $i]:
% 0.44/0.69          (((X0) != (k1_xboole_0))
% 0.44/0.69           | ~ (v1_xboole_0 @ X0)
% 0.44/0.69           | ~ (v1_xboole_0 @ sk_B)))
% 0.44/0.69         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['27', '29'])).
% 0.44/0.69  thf('31', plain,
% 0.44/0.69      (((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.44/0.69         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.69      inference('simplify', [status(thm)], ['30'])).
% 0.44/0.69  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.44/0.69  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.69  thf('33', plain,
% 0.44/0.69      ((~ (v1_xboole_0 @ sk_B)) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.69      inference('simplify_reflect+', [status(thm)], ['31', '32'])).
% 0.44/0.69  thf('34', plain,
% 0.44/0.69      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('split', [status(esa)], ['28'])).
% 0.44/0.69  thf('35', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('36', plain,
% 0.44/0.69      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D))
% 0.44/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.69  thf('37', plain,
% 0.44/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.69  thf('38', plain,
% 0.44/0.69      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('split', [status(esa)], ['28'])).
% 0.44/0.69  thf('39', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('40', plain,
% 0.44/0.69      (((m1_subset_1 @ sk_C @ 
% 0.44/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.44/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('sup+', [status(thm)], ['38', '39'])).
% 0.44/0.69  thf(t113_zfmisc_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.44/0.69       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.44/0.69  thf('41', plain,
% 0.44/0.69      (![X2 : $i, X3 : $i]:
% 0.44/0.69         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.44/0.69      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.44/0.69  thf('42', plain,
% 0.44/0.69      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.44/0.69      inference('simplify', [status(thm)], ['41'])).
% 0.44/0.69  thf('43', plain,
% 0.44/0.69      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.44/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('demod', [status(thm)], ['40', '42'])).
% 0.44/0.69  thf('44', plain,
% 0.44/0.69      ((![X0 : $i]:
% 0.44/0.69          ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.44/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('sup+', [status(thm)], ['37', '43'])).
% 0.44/0.69  thf('45', plain,
% 0.44/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.69  thf('46', plain,
% 0.44/0.69      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('split', [status(esa)], ['28'])).
% 0.44/0.69  thf('47', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('48', plain,
% 0.44/0.69      (((m1_subset_1 @ sk_D @ 
% 0.44/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.44/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('sup+', [status(thm)], ['46', '47'])).
% 0.44/0.69  thf('49', plain,
% 0.44/0.69      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.44/0.69      inference('simplify', [status(thm)], ['41'])).
% 0.44/0.69  thf('50', plain,
% 0.44/0.69      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.44/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('demod', [status(thm)], ['48', '49'])).
% 0.44/0.69  thf('51', plain,
% 0.44/0.69      ((![X0 : $i]:
% 0.44/0.69          ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.44/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('sup+', [status(thm)], ['45', '50'])).
% 0.44/0.69  thf('52', plain,
% 0.44/0.69      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.44/0.69      inference('simplify', [status(thm)], ['41'])).
% 0.44/0.69  thf('53', plain,
% 0.44/0.69      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.69         (~ (v1_funct_1 @ X14)
% 0.44/0.69          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.44/0.69          | ((X17) = (X14))
% 0.44/0.69          | ~ (r1_partfun1 @ X17 @ X14)
% 0.44/0.69          | ~ (v1_partfun1 @ X14 @ X15)
% 0.44/0.69          | ~ (v1_partfun1 @ X17 @ X15)
% 0.44/0.69          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.44/0.69          | ~ (v1_funct_1 @ X17))),
% 0.44/0.69      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.44/0.69  thf('54', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.69          | ~ (v1_funct_1 @ X2)
% 0.44/0.69          | ~ (m1_subset_1 @ X2 @ 
% 0.44/0.69               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))
% 0.44/0.69          | ~ (v1_partfun1 @ X2 @ k1_xboole_0)
% 0.44/0.69          | ~ (v1_partfun1 @ X1 @ k1_xboole_0)
% 0.44/0.69          | ~ (r1_partfun1 @ X2 @ X1)
% 0.44/0.69          | ((X2) = (X1))
% 0.44/0.69          | ~ (v1_funct_1 @ X1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['52', '53'])).
% 0.44/0.69  thf('55', plain,
% 0.44/0.69      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.44/0.69      inference('simplify', [status(thm)], ['41'])).
% 0.44/0.69  thf('56', plain,
% 0.44/0.69      (![X1 : $i, X2 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.69          | ~ (v1_funct_1 @ X2)
% 0.44/0.69          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.69          | ~ (v1_partfun1 @ X2 @ k1_xboole_0)
% 0.44/0.69          | ~ (v1_partfun1 @ X1 @ k1_xboole_0)
% 0.44/0.69          | ~ (r1_partfun1 @ X2 @ X1)
% 0.44/0.69          | ((X2) = (X1))
% 0.44/0.69          | ~ (v1_funct_1 @ X1))),
% 0.44/0.69      inference('demod', [status(thm)], ['54', '55'])).
% 0.44/0.69  thf('57', plain,
% 0.44/0.69      ((![X0 : $i]:
% 0.44/0.69          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.44/0.69           | ~ (v1_funct_1 @ sk_D)
% 0.44/0.69           | ((X0) = (sk_D))
% 0.44/0.69           | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.44/0.69           | ~ (v1_partfun1 @ sk_D @ k1_xboole_0)
% 0.44/0.69           | ~ (v1_partfun1 @ X0 @ k1_xboole_0)
% 0.44/0.69           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.69           | ~ (v1_funct_1 @ X0)))
% 0.44/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['51', '56'])).
% 0.44/0.69  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.69  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('60', plain,
% 0.44/0.69      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.44/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('demod', [status(thm)], ['48', '49'])).
% 0.44/0.69  thf('61', plain,
% 0.44/0.69      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.44/0.69      inference('simplify', [status(thm)], ['41'])).
% 0.44/0.69  thf(cc1_partfun1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( v1_xboole_0 @ A ) =>
% 0.44/0.69       ( ![C:$i]:
% 0.44/0.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.69           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.44/0.69  thf('62', plain,
% 0.44/0.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.69         (~ (v1_xboole_0 @ X8)
% 0.44/0.69          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 0.44/0.69          | (v1_partfun1 @ X9 @ X8))),
% 0.44/0.69      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.44/0.69  thf('63', plain,
% 0.44/0.69      (![X1 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.69          | (v1_partfun1 @ X1 @ k1_xboole_0)
% 0.44/0.69          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['61', '62'])).
% 0.44/0.69  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.69  thf('65', plain,
% 0.44/0.69      (![X1 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.69          | (v1_partfun1 @ X1 @ k1_xboole_0))),
% 0.44/0.69      inference('demod', [status(thm)], ['63', '64'])).
% 0.44/0.69  thf('66', plain,
% 0.44/0.69      (((v1_partfun1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['60', '65'])).
% 0.44/0.69  thf('67', plain,
% 0.44/0.69      ((![X0 : $i]:
% 0.44/0.69          (((X0) = (sk_D))
% 0.44/0.69           | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.44/0.69           | ~ (v1_partfun1 @ X0 @ k1_xboole_0)
% 0.44/0.69           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.69           | ~ (v1_funct_1 @ X0)))
% 0.44/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('demod', [status(thm)], ['57', '58', '59', '66'])).
% 0.44/0.69  thf('68', plain,
% 0.44/0.69      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.44/0.69         | ~ (v1_funct_1 @ sk_C)
% 0.44/0.69         | ~ (v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.44/0.69         | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.44/0.69         | ((sk_C) = (sk_D)))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['44', '67'])).
% 0.44/0.69  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.69  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('71', plain,
% 0.44/0.69      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.44/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('demod', [status(thm)], ['40', '42'])).
% 0.44/0.69  thf('72', plain,
% 0.44/0.69      (![X1 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.69          | (v1_partfun1 @ X1 @ k1_xboole_0))),
% 0.44/0.69      inference('demod', [status(thm)], ['63', '64'])).
% 0.44/0.69  thf('73', plain,
% 0.44/0.69      (((v1_partfun1 @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['71', '72'])).
% 0.44/0.69  thf('74', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('75', plain, ((((sk_C) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('demod', [status(thm)], ['68', '69', '70', '73', '74'])).
% 0.44/0.69  thf('76', plain,
% 0.44/0.69      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.44/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('demod', [status(thm)], ['40', '42'])).
% 0.44/0.69  thf('77', plain,
% 0.44/0.69      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.44/0.69      inference('simplify', [status(thm)], ['41'])).
% 0.44/0.69  thf(redefinition_r2_relset_1, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.69     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.44/0.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.69       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.44/0.69  thf('78', plain,
% 0.44/0.69      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.44/0.69          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.44/0.69          | (r2_relset_1 @ X5 @ X6 @ X4 @ X7)
% 0.44/0.69          | ((X4) != (X7)))),
% 0.44/0.69      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.44/0.69  thf('79', plain,
% 0.44/0.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.69         ((r2_relset_1 @ X5 @ X6 @ X7 @ X7)
% 0.44/0.69          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.44/0.69      inference('simplify', [status(thm)], ['78'])).
% 0.44/0.69  thf('80', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.69          | (r2_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['77', '79'])).
% 0.44/0.69  thf('81', plain,
% 0.44/0.69      ((![X0 : $i]: (r2_relset_1 @ k1_xboole_0 @ X0 @ sk_C @ sk_C))
% 0.44/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['76', '80'])).
% 0.44/0.69  thf('82', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.44/0.69      inference('demod', [status(thm)], ['36', '75', '81'])).
% 0.44/0.69  thf('83', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.44/0.69      inference('split', [status(esa)], ['28'])).
% 0.44/0.69  thf('84', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.44/0.69      inference('sat_resolution*', [status(thm)], ['82', '83'])).
% 0.44/0.69  thf('85', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.69      inference('simpl_trail', [status(thm)], ['33', '84'])).
% 0.44/0.69  thf('86', plain, (((sk_C) = (sk_D))),
% 0.44/0.69      inference('clc', [status(thm)], ['24', '85'])).
% 0.44/0.69  thf('87', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('88', plain,
% 0.44/0.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.69         ((r2_relset_1 @ X5 @ X6 @ X7 @ X7)
% 0.44/0.69          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.44/0.69      inference('simplify', [status(thm)], ['78'])).
% 0.44/0.69  thf('89', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.44/0.69      inference('sup-', [status(thm)], ['87', '88'])).
% 0.44/0.69  thf('90', plain, ($false),
% 0.44/0.69      inference('demod', [status(thm)], ['0', '86', '89'])).
% 0.44/0.69  
% 0.44/0.69  % SZS output end Refutation
% 0.44/0.69  
% 0.55/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
