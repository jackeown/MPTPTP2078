%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KHohrO9BPk

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:06 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 306 expanded)
%              Number of leaves         :   24 (  98 expanded)
%              Depth                    :   19
%              Number of atoms          :  751 (3674 expanded)
%              Number of equality atoms :   62 ( 299 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( r2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X23 = X20 )
      | ~ ( r1_partfun1 @ X23 @ X20 )
      | ~ ( v1_partfun1 @ X20 @ X21 )
      | ~ ( v1_partfun1 @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X23 ) ) ),
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
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A_1 )
      | ~ ( v1_partfun1 @ sk_D @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( v1_partfun1 @ X15 @ X16 )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A_1 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_D @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A_1 ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('20',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('21',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['19','24'])).

thf('26',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('27',plain,(
    ~ ( r2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('30',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('32',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('36',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('39',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['20','23'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['20','23'])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('45',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','45'])).

thf('47',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('53',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('54',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['20','23'])).

thf('56',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('59',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('60',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_relset_1 @ X11 @ X12 @ X13 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['46','59','63'])).

thf('65',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('66',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','66'])).

thf('68',plain,(
    v1_partfun1 @ sk_D @ sk_A_1 ),
    inference(clc,[status(thm)],['12','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['6','68'])).

thf('70',plain,
    ( ( sk_C_1 = sk_D )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','69'])).

thf('71',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( v1_partfun1 @ X15 @ X16 )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B )
    | ( v1_partfun1 @ sk_C_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_C_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','66'])).

thf('79',plain,(
    v1_partfun1 @ sk_C_1 @ sk_A_1 ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_C_1 = sk_D ),
    inference(demod,[status(thm)],['70','71','79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['61'])).

thf('84',plain,(
    r2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['0','81','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KHohrO9BPk
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:21:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 291 iterations in 0.122s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.58  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.58  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.40/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.58  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.58  thf(t142_funct_2, conjecture,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.58       ( ![D:$i]:
% 0.40/0.58         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.40/0.58             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.58           ( ( r1_partfun1 @ C @ D ) =>
% 0.40/0.58             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.40/0.58               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.58            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.58          ( ![D:$i]:
% 0.40/0.58            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.40/0.58                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.58              ( ( r1_partfun1 @ C @ D ) =>
% 0.40/0.58                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.40/0.58                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.40/0.58  thf('0', plain, (~ (r2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 @ sk_D)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t148_partfun1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.58       ( ![D:$i]:
% 0.40/0.58         ( ( ( v1_funct_1 @ D ) & 
% 0.40/0.58             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.58           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.40/0.58               ( r1_partfun1 @ C @ D ) ) =>
% 0.40/0.58             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.58         (~ (v1_funct_1 @ X20)
% 0.40/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.40/0.58          | ((X23) = (X20))
% 0.40/0.58          | ~ (r1_partfun1 @ X23 @ X20)
% 0.40/0.58          | ~ (v1_partfun1 @ X20 @ X21)
% 0.40/0.58          | ~ (v1_partfun1 @ X23 @ X21)
% 0.40/0.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.40/0.58          | ~ (v1_funct_1 @ X23))),
% 0.40/0.58      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_funct_1 @ X0)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 0.40/0.58          | ~ (v1_partfun1 @ X0 @ sk_A_1)
% 0.40/0.58          | ~ (v1_partfun1 @ sk_D @ sk_A_1)
% 0.40/0.58          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.40/0.58          | ((X0) = (sk_D))
% 0.40/0.58          | ~ (v1_funct_1 @ sk_D))),
% 0.40/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.58  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_funct_1 @ X0)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 0.40/0.58          | ~ (v1_partfun1 @ X0 @ sk_A_1)
% 0.40/0.58          | ~ (v1_partfun1 @ sk_D @ sk_A_1)
% 0.40/0.58          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.40/0.58          | ((X0) = (sk_D)))),
% 0.40/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(cc5_funct_2, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.58       ( ![C:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.40/0.58             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.40/0.58          | (v1_partfun1 @ X15 @ X16)
% 0.40/0.58          | ~ (v1_funct_2 @ X15 @ X16 @ X17)
% 0.40/0.58          | ~ (v1_funct_1 @ X15)
% 0.40/0.58          | (v1_xboole_0 @ X17))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (((v1_xboole_0 @ sk_B)
% 0.40/0.58        | ~ (v1_funct_1 @ sk_D)
% 0.40/0.58        | ~ (v1_funct_2 @ sk_D @ sk_A_1 @ sk_B)
% 0.40/0.58        | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.58  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('11', plain, ((v1_funct_2 @ sk_D @ sk_A_1 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('12', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.40/0.58  thf(l13_xboole_0, axiom,
% 0.40/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.40/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.40/0.58  thf('16', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A_1) = (k1_xboole_0)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.40/0.58      inference('split', [status(esa)], ['16'])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      ((![X0 : $i]:
% 0.40/0.58          (((X0) != (k1_xboole_0))
% 0.40/0.58           | ~ (v1_xboole_0 @ X0)
% 0.40/0.58           | ~ (v1_xboole_0 @ sk_B)))
% 0.40/0.58         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['15', '17'])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.40/0.58         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.40/0.58      inference('simplify', [status(thm)], ['18'])).
% 0.40/0.58  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.40/0.58  thf('20', plain, ((v1_xboole_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.40/0.58  thf('21', plain, ((v1_xboole_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.40/0.58  thf('23', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.58  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('demod', [status(thm)], ['20', '23'])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      ((~ (v1_xboole_0 @ sk_B)) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.40/0.58      inference('simplify_reflect+', [status(thm)], ['19', '24'])).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('split', [status(esa)], ['16'])).
% 0.40/0.58  thf('27', plain, (~ (r2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 @ sk_D)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ sk_D))
% 0.40/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.58  thf(t113_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.40/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      (![X2 : $i, X3 : $i]:
% 0.40/0.58         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.40/0.58  thf('30', plain,
% 0.40/0.58      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['29'])).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('split', [status(esa)], ['16'])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      (((m1_subset_1 @ sk_C_1 @ 
% 0.40/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.40/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['32', '33'])).
% 0.40/0.58  thf('35', plain,
% 0.40/0.58      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['29'])).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.40/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      ((![X0 : $i]:
% 0.40/0.58          ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.40/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['31', '36'])).
% 0.40/0.58  thf(cc3_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_xboole_0 @ A ) =>
% 0.40/0.58       ( ![C:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58           ( v1_xboole_0 @ C ) ) ) ))).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.58         (~ (v1_xboole_0 @ X8)
% 0.40/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 0.40/0.58          | (v1_xboole_0 @ X9))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      ((![X0 : $i, X1 : $i]:
% 0.40/0.58          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.40/0.58           | (v1_xboole_0 @ sk_C_1)
% 0.40/0.58           | ~ (v1_xboole_0 @ X1)))
% 0.40/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.58         | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.58         | (v1_xboole_0 @ sk_C_1))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['30', '39'])).
% 0.40/0.58  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('demod', [status(thm)], ['20', '23'])).
% 0.40/0.58  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('demod', [status(thm)], ['20', '23'])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      (((v1_xboole_0 @ sk_C_1)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.40/0.58  thf('45', plain,
% 0.40/0.58      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.40/0.58  thf('46', plain,
% 0.40/0.58      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ sk_D))
% 0.40/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('demod', [status(thm)], ['28', '45'])).
% 0.40/0.58  thf('47', plain,
% 0.40/0.58      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('split', [status(esa)], ['16'])).
% 0.40/0.58  thf('48', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('49', plain,
% 0.40/0.58      (((m1_subset_1 @ sk_D @ 
% 0.40/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.40/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['47', '48'])).
% 0.40/0.58  thf('50', plain,
% 0.40/0.58      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['29'])).
% 0.40/0.58  thf('51', plain,
% 0.40/0.58      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.40/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('demod', [status(thm)], ['49', '50'])).
% 0.40/0.58  thf('52', plain,
% 0.40/0.58      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['29'])).
% 0.40/0.58  thf('53', plain,
% 0.40/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.58         (~ (v1_xboole_0 @ X8)
% 0.40/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 0.40/0.58          | (v1_xboole_0 @ X9))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.40/0.58  thf('54', plain,
% 0.40/0.58      (![X1 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.40/0.58          | (v1_xboole_0 @ X1)
% 0.40/0.58          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.40/0.58  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('demod', [status(thm)], ['20', '23'])).
% 0.40/0.58  thf('56', plain,
% 0.40/0.58      (![X1 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.40/0.58          | (v1_xboole_0 @ X1))),
% 0.40/0.58      inference('demod', [status(thm)], ['54', '55'])).
% 0.40/0.58  thf('57', plain, (((v1_xboole_0 @ sk_D)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['51', '56'])).
% 0.40/0.58  thf('58', plain,
% 0.40/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.40/0.58  thf('59', plain,
% 0.40/0.58      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.40/0.58  thf(t4_subset_1, axiom,
% 0.40/0.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.40/0.58  thf('60', plain,
% 0.40/0.58      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.40/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.40/0.58  thf(reflexivity_r2_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.58     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.40/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.58       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.40/0.58  thf('61', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.58         ((r2_relset_1 @ X11 @ X12 @ X13 @ X13)
% 0.40/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.40/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.40/0.58      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.40/0.58  thf('62', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.40/0.58      inference('condensation', [status(thm)], ['61'])).
% 0.40/0.58  thf('63', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('sup-', [status(thm)], ['60', '62'])).
% 0.40/0.58  thf('64', plain, (~ (((sk_A_1) = (k1_xboole_0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['46', '59', '63'])).
% 0.40/0.58  thf('65', plain,
% 0.40/0.58      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A_1) = (k1_xboole_0)))),
% 0.40/0.58      inference('split', [status(esa)], ['16'])).
% 0.40/0.58  thf('66', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.40/0.58      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 0.40/0.58  thf('67', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.58      inference('simpl_trail', [status(thm)], ['25', '66'])).
% 0.40/0.58  thf('68', plain, ((v1_partfun1 @ sk_D @ sk_A_1)),
% 0.40/0.58      inference('clc', [status(thm)], ['12', '67'])).
% 0.40/0.58  thf('69', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_funct_1 @ X0)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 0.40/0.58          | ~ (v1_partfun1 @ X0 @ sk_A_1)
% 0.40/0.58          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.40/0.58          | ((X0) = (sk_D)))),
% 0.40/0.58      inference('demod', [status(thm)], ['6', '68'])).
% 0.40/0.58  thf('70', plain,
% 0.40/0.58      ((((sk_C_1) = (sk_D))
% 0.40/0.58        | ~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 0.40/0.58        | ~ (v1_partfun1 @ sk_C_1 @ sk_A_1)
% 0.40/0.58        | ~ (v1_funct_1 @ sk_C_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '69'])).
% 0.40/0.58  thf('71', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('72', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('73', plain,
% 0.40/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.40/0.58          | (v1_partfun1 @ X15 @ X16)
% 0.40/0.58          | ~ (v1_funct_2 @ X15 @ X16 @ X17)
% 0.40/0.58          | ~ (v1_funct_1 @ X15)
% 0.40/0.58          | (v1_xboole_0 @ X17))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.40/0.58  thf('74', plain,
% 0.40/0.58      (((v1_xboole_0 @ sk_B)
% 0.40/0.58        | ~ (v1_funct_1 @ sk_C_1)
% 0.40/0.58        | ~ (v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B)
% 0.40/0.58        | (v1_partfun1 @ sk_C_1 @ sk_A_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['72', '73'])).
% 0.40/0.58  thf('75', plain, ((v1_funct_1 @ sk_C_1)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('76', plain, ((v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('77', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_C_1 @ sk_A_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.40/0.58  thf('78', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.58      inference('simpl_trail', [status(thm)], ['25', '66'])).
% 0.40/0.58  thf('79', plain, ((v1_partfun1 @ sk_C_1 @ sk_A_1)),
% 0.40/0.58      inference('clc', [status(thm)], ['77', '78'])).
% 0.40/0.58  thf('80', plain, ((v1_funct_1 @ sk_C_1)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('81', plain, (((sk_C_1) = (sk_D))),
% 0.40/0.58      inference('demod', [status(thm)], ['70', '71', '79', '80'])).
% 0.40/0.58  thf('82', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('83', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.40/0.58      inference('condensation', [status(thm)], ['61'])).
% 0.40/0.58  thf('84', plain, ((r2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 @ sk_C_1)),
% 0.40/0.58      inference('sup-', [status(thm)], ['82', '83'])).
% 0.40/0.58  thf('85', plain, ($false),
% 0.40/0.58      inference('demod', [status(thm)], ['0', '81', '84'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
