%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uXsyIEuBxm

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:10 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 316 expanded)
%              Number of leaves         :   25 ( 101 expanded)
%              Depth                    :   16
%              Number of atoms          :  762 (5054 expanded)
%              Number of equality atoms :   80 ( 426 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_partfun1_type,type,(
    k3_partfun1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X20 = X17 )
      | ~ ( r1_partfun1 @ X20 @ X17 )
      | ~ ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_partfun1 @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t133_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( v1_partfun1 @ ( k3_partfun1 @ C @ A @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X16 ) ) )
      | ( v1_partfun1 @ ( k3_partfun1 @ X15 @ X14 @ X16 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t133_funct_2])).

thf('7',plain,
    ( ( v1_partfun1 @ ( k3_partfun1 @ sk_D @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k3_partfun1 @ C @ A @ B )
        = C ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k3_partfun1 @ X25 @ X26 @ X27 )
        = X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t87_partfun1])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k3_partfun1 @ sk_D @ sk_A @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k3_partfun1 @ sk_D @ sk_A @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_partfun1 @ sk_D @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','12','13','14'])).

thf('16',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('19',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X5 ) @ X4 )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('25',plain,
    ( ( ( k9_relat_1 @ ( k6_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) @ sk_C )
      = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('28',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X3: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('30',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','27','28','29'])).

thf('31',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','30'])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X5 ) @ X4 )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('36',plain,
    ( ( ( k9_relat_1 @ ( k6_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) @ sk_D )
      = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('38',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('39',plain,(
    ! [X3: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('40',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','40'])).

thf('42',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( r2_relset_1 @ X7 @ X8 @ X6 @ X9 )
      | ( X6 != X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('45',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_relset_1 @ X7 @ X8 @ X9 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','46'])).

thf('48',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','27','28','29'])).

thf('49',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','27','28','29'])).

thf('50',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['41','50'])).

thf('52',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('53',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['17','53'])).

thf('55',plain,(
    v1_partfun1 @ sk_D @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['15','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['4','55','56'])).

thf('58',plain,
    ( ( sk_C = sk_D )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','57'])).

thf('59',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X16 ) ) )
      | ( v1_partfun1 @ ( k3_partfun1 @ X15 @ X14 @ X16 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t133_funct_2])).

thf('62',plain,
    ( ( v1_partfun1 @ ( k3_partfun1 @ sk_C @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k3_partfun1 @ X25 @ X26 @ X27 )
        = X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t87_partfun1])).

thf('65',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k3_partfun1 @ sk_C @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k3_partfun1 @ sk_C @ sk_A @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_partfun1 @ sk_C @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','67','68','69'])).

thf('71',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['17','53'])).

thf('72',plain,(
    v1_partfun1 @ sk_C @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    sk_C = sk_D ),
    inference(demod,[status(thm)],['58','59','72','73'])).

thf('75',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['43','45'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['0','74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uXsyIEuBxm
% 0.16/0.36  % Computer   : n008.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 15:33:45 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.24/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.52  % Solved by: fo/fo7.sh
% 0.24/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.52  % done 93 iterations in 0.041s
% 0.24/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.52  % SZS output start Refutation
% 0.24/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.24/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.52  thf(k3_partfun1_type, type, k3_partfun1: $i > $i > $i > $i).
% 0.24/0.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.24/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.24/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.24/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.24/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.24/0.52  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.24/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.52  thf(t142_funct_2, conjecture,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.24/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.52       ( ![D:$i]:
% 0.24/0.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.24/0.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.52           ( ( r1_partfun1 @ C @ D ) =>
% 0.24/0.52             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.24/0.52               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.24/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.52        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.24/0.52            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.52          ( ![D:$i]:
% 0.24/0.52            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.24/0.52                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.52              ( ( r1_partfun1 @ C @ D ) =>
% 0.24/0.52                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.24/0.52                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.24/0.52    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.24/0.52  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('1', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('2', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(t148_partfun1, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( ( v1_funct_1 @ C ) & 
% 0.24/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.52       ( ![D:$i]:
% 0.24/0.52         ( ( ( v1_funct_1 @ D ) & 
% 0.24/0.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.52           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.24/0.52               ( r1_partfun1 @ C @ D ) ) =>
% 0.24/0.52             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.24/0.52  thf('3', plain,
% 0.24/0.52      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.24/0.52         (~ (v1_funct_1 @ X17)
% 0.24/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.24/0.52          | ((X20) = (X17))
% 0.24/0.52          | ~ (r1_partfun1 @ X20 @ X17)
% 0.24/0.52          | ~ (v1_partfun1 @ X17 @ X18)
% 0.24/0.52          | ~ (v1_partfun1 @ X20 @ X18)
% 0.24/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.24/0.52          | ~ (v1_funct_1 @ X20))),
% 0.24/0.52      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.24/0.52  thf('4', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (v1_funct_1 @ X0)
% 0.24/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.24/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.24/0.52          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.24/0.52          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.24/0.52          | ((X0) = (sk_D))
% 0.24/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.24/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.52  thf('5', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(t133_funct_2, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.24/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.24/0.52         ( v1_partfun1 @ ( k3_partfun1 @ C @ A @ B ) @ A ) ) ))).
% 0.24/0.52  thf('6', plain,
% 0.24/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.52         (((X16) = (k1_xboole_0))
% 0.24/0.52          | ~ (v1_funct_1 @ X15)
% 0.24/0.52          | ~ (v1_funct_2 @ X15 @ X14 @ X16)
% 0.24/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X16)))
% 0.24/0.52          | (v1_partfun1 @ (k3_partfun1 @ X15 @ X14 @ X16) @ X14))),
% 0.24/0.52      inference('cnf', [status(esa)], [t133_funct_2])).
% 0.24/0.52  thf('7', plain,
% 0.24/0.52      (((v1_partfun1 @ (k3_partfun1 @ sk_D @ sk_A @ sk_B) @ sk_A)
% 0.24/0.52        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.24/0.52        | ~ (v1_funct_1 @ sk_D)
% 0.24/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.24/0.52  thf('8', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(t87_partfun1, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( ( v1_funct_1 @ C ) & 
% 0.24/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.52       ( ( k3_partfun1 @ C @ A @ B ) = ( C ) ) ))).
% 0.24/0.52  thf('9', plain,
% 0.24/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.24/0.52         (((k3_partfun1 @ X25 @ X26 @ X27) = (X25))
% 0.24/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.24/0.52          | ~ (v1_funct_1 @ X25))),
% 0.24/0.52      inference('cnf', [status(esa)], [t87_partfun1])).
% 0.24/0.52  thf('10', plain,
% 0.24/0.52      ((~ (v1_funct_1 @ sk_D) | ((k3_partfun1 @ sk_D @ sk_A @ sk_B) = (sk_D)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.52  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('12', plain, (((k3_partfun1 @ sk_D @ sk_A @ sk_B) = (sk_D))),
% 0.24/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.24/0.52  thf('13', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('15', plain, (((v1_partfun1 @ sk_D @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.24/0.52      inference('demod', [status(thm)], ['7', '12', '13', '14'])).
% 0.24/0.52  thf('16', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('17', plain,
% 0.24/0.52      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.24/0.52      inference('split', [status(esa)], ['16'])).
% 0.24/0.52  thf('18', plain,
% 0.24/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('split', [status(esa)], ['16'])).
% 0.24/0.52  thf('19', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('20', plain,
% 0.24/0.52      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D))
% 0.24/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.24/0.52  thf('21', plain,
% 0.24/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('split', [status(esa)], ['16'])).
% 0.24/0.52  thf('22', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('23', plain,
% 0.24/0.52      (((m1_subset_1 @ sk_C @ 
% 0.24/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.24/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.24/0.52  thf(t162_funct_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.52       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.24/0.52  thf('24', plain,
% 0.24/0.52      (![X4 : $i, X5 : $i]:
% 0.24/0.52         (((k9_relat_1 @ (k6_relat_1 @ X5) @ X4) = (X4))
% 0.24/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.24/0.52      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.24/0.52  thf('25', plain,
% 0.24/0.52      ((((k9_relat_1 @ (k6_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B)) @ sk_C)
% 0.24/0.52          = (sk_C)))
% 0.24/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.24/0.52  thf(t113_zfmisc_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.24/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.24/0.52  thf('26', plain,
% 0.24/0.52      (![X1 : $i, X2 : $i]:
% 0.24/0.52         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.24/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.24/0.52  thf('27', plain,
% 0.24/0.52      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.24/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.24/0.52  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.24/0.52  thf('28', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.24/0.52  thf(t150_relat_1, axiom,
% 0.24/0.52    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.24/0.52  thf('29', plain,
% 0.24/0.52      (![X3 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.24/0.52  thf('30', plain,
% 0.24/0.52      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('demod', [status(thm)], ['25', '27', '28', '29'])).
% 0.24/0.52  thf('31', plain,
% 0.24/0.52      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ sk_D))
% 0.24/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('demod', [status(thm)], ['20', '30'])).
% 0.24/0.52  thf('32', plain,
% 0.24/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('split', [status(esa)], ['16'])).
% 0.24/0.52  thf('33', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('34', plain,
% 0.24/0.52      (((m1_subset_1 @ sk_D @ 
% 0.24/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.24/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('sup+', [status(thm)], ['32', '33'])).
% 0.24/0.52  thf('35', plain,
% 0.24/0.52      (![X4 : $i, X5 : $i]:
% 0.24/0.52         (((k9_relat_1 @ (k6_relat_1 @ X5) @ X4) = (X4))
% 0.24/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.24/0.52      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.24/0.52  thf('36', plain,
% 0.24/0.52      ((((k9_relat_1 @ (k6_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B)) @ sk_D)
% 0.24/0.52          = (sk_D)))
% 0.24/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.24/0.52  thf('37', plain,
% 0.24/0.52      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.24/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.24/0.52  thf('38', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.24/0.52  thf('39', plain,
% 0.24/0.52      (![X3 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.24/0.52  thf('40', plain,
% 0.24/0.52      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.24/0.52  thf('41', plain,
% 0.24/0.52      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0))
% 0.24/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('demod', [status(thm)], ['31', '40'])).
% 0.24/0.52  thf('42', plain,
% 0.24/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('split', [status(esa)], ['16'])).
% 0.24/0.52  thf('43', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(redefinition_r2_relset_1, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.24/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.52       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.24/0.52  thf('44', plain,
% 0.24/0.52      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.24/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.24/0.52          | (r2_relset_1 @ X7 @ X8 @ X6 @ X9)
% 0.24/0.52          | ((X6) != (X9)))),
% 0.24/0.52      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.24/0.52  thf('45', plain,
% 0.24/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.52         ((r2_relset_1 @ X7 @ X8 @ X9 @ X9)
% 0.24/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.24/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.24/0.52  thf('46', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.24/0.52      inference('sup-', [status(thm)], ['43', '45'])).
% 0.24/0.52  thf('47', plain,
% 0.24/0.52      (((r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C))
% 0.24/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('sup+', [status(thm)], ['42', '46'])).
% 0.24/0.52  thf('48', plain,
% 0.24/0.52      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('demod', [status(thm)], ['25', '27', '28', '29'])).
% 0.24/0.52  thf('49', plain,
% 0.24/0.52      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('demod', [status(thm)], ['25', '27', '28', '29'])).
% 0.24/0.52  thf('50', plain,
% 0.24/0.52      (((r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0))
% 0.24/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.52      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.24/0.52  thf('51', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.24/0.52      inference('demod', [status(thm)], ['41', '50'])).
% 0.24/0.52  thf('52', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.24/0.52      inference('split', [status(esa)], ['16'])).
% 0.24/0.52  thf('53', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.24/0.52      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.24/0.52  thf('54', plain, (((sk_B) != (k1_xboole_0))),
% 0.24/0.52      inference('simpl_trail', [status(thm)], ['17', '53'])).
% 0.24/0.52  thf('55', plain, ((v1_partfun1 @ sk_D @ sk_A)),
% 0.24/0.52      inference('simplify_reflect-', [status(thm)], ['15', '54'])).
% 0.24/0.52  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('57', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (v1_funct_1 @ X0)
% 0.24/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.24/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.24/0.52          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.24/0.52          | ((X0) = (sk_D)))),
% 0.24/0.52      inference('demod', [status(thm)], ['4', '55', '56'])).
% 0.24/0.52  thf('58', plain,
% 0.24/0.52      ((((sk_C) = (sk_D))
% 0.24/0.52        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.24/0.52        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.24/0.52        | ~ (v1_funct_1 @ sk_C))),
% 0.24/0.52      inference('sup-', [status(thm)], ['1', '57'])).
% 0.24/0.52  thf('59', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('60', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('61', plain,
% 0.24/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.52         (((X16) = (k1_xboole_0))
% 0.24/0.52          | ~ (v1_funct_1 @ X15)
% 0.24/0.52          | ~ (v1_funct_2 @ X15 @ X14 @ X16)
% 0.24/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X16)))
% 0.24/0.52          | (v1_partfun1 @ (k3_partfun1 @ X15 @ X14 @ X16) @ X14))),
% 0.24/0.52      inference('cnf', [status(esa)], [t133_funct_2])).
% 0.24/0.52  thf('62', plain,
% 0.24/0.52      (((v1_partfun1 @ (k3_partfun1 @ sk_C @ sk_A @ sk_B) @ sk_A)
% 0.24/0.52        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.24/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.24/0.52  thf('63', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('64', plain,
% 0.24/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.24/0.52         (((k3_partfun1 @ X25 @ X26 @ X27) = (X25))
% 0.24/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.24/0.52          | ~ (v1_funct_1 @ X25))),
% 0.24/0.52      inference('cnf', [status(esa)], [t87_partfun1])).
% 0.24/0.52  thf('65', plain,
% 0.24/0.52      ((~ (v1_funct_1 @ sk_C) | ((k3_partfun1 @ sk_C @ sk_A @ sk_B) = (sk_C)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['63', '64'])).
% 0.24/0.52  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('67', plain, (((k3_partfun1 @ sk_C @ sk_A @ sk_B) = (sk_C))),
% 0.24/0.52      inference('demod', [status(thm)], ['65', '66'])).
% 0.24/0.52  thf('68', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('70', plain, (((v1_partfun1 @ sk_C @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.24/0.52      inference('demod', [status(thm)], ['62', '67', '68', '69'])).
% 0.24/0.52  thf('71', plain, (((sk_B) != (k1_xboole_0))),
% 0.24/0.52      inference('simpl_trail', [status(thm)], ['17', '53'])).
% 0.24/0.52  thf('72', plain, ((v1_partfun1 @ sk_C @ sk_A)),
% 0.24/0.52      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.24/0.52  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('74', plain, (((sk_C) = (sk_D))),
% 0.24/0.52      inference('demod', [status(thm)], ['58', '59', '72', '73'])).
% 0.24/0.52  thf('75', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.24/0.52      inference('sup-', [status(thm)], ['43', '45'])).
% 0.24/0.52  thf('76', plain, ($false),
% 0.24/0.52      inference('demod', [status(thm)], ['0', '74', '75'])).
% 0.24/0.52  
% 0.24/0.52  % SZS output end Refutation
% 0.24/0.52  
% 0.24/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
