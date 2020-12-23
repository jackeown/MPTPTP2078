%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.94HUG715m4

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:43 EST 2020

% Result     : Theorem 36.78s
% Output     : Refutation 36.78s
% Verified   : 
% Statistics : Number of formulae       :  248 (4124 expanded)
%              Number of leaves         :   43 (1236 expanded)
%              Depth                    :   31
%              Number of atoms          : 1818 (43962 expanded)
%              Number of equality atoms :  141 (3302 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X45 @ X46 @ X44 @ X47 ) ) ) ),
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
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ( ( k2_partfun1 @ X49 @ X50 @ X48 @ X51 )
        = ( k7_relat_1 @ X48 @ X51 ) ) ) ),
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
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['19','24'])).

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

thf('26',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('32',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( v5_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('56',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('59',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['54','55'])).

thf('66',plain,(
    r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('68',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['53','56','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['42','69'])).

thf('71',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['19','24'])).

thf('72',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_B
        = ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('76',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('78',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['41','78'])).

thf('80',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['81'])).

thf('84',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('85',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['81'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('90',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('94',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['81'])).

thf('96',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('99',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('101',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['53','56','68'])).

thf('104',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('105',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ( ( k2_partfun1 @ X49 @ X50 @ X48 @ X51 )
        = ( k7_relat_1 @ X48 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('108',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X23 @ X24 ) @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('109',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['54','55'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['107','112'])).

thf('114',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','113'])).

thf('115',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('116',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('117',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('118',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['81'])).

thf('119',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('120',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('121',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','113'])).

thf('122',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('123',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('124',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['53','56','68'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('128',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X25 @ ( k1_relat_1 @ X26 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) )
        = X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['54','55'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = X2 ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['126','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['125','133'])).

thf('135',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('139',plain,(
    ! [X36: $i] :
      ( zip_tseitin_0 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('141',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['137','143'])).

thf('145',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['85','94','99','114','115','116','117','118','119','120','121','122','144'])).

thf('146',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['81'])).

thf('147',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['145','146'])).

thf('148',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['82','147'])).

thf('149',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['80','148'])).

thf('150',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X25 @ ( k1_relat_1 @ X26 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) )
        = X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','153'])).

thf('155',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('157',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X23 @ X24 ) @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('159',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('160',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['157','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('163',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('165',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('171',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('174',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['169','174'])).

thf('176',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('177',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X33 ) @ X34 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X33 ) @ X35 )
      | ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['175','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('181',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['154','181'])).

thf('183',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['13','182'])).

thf('184',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['154','181'])).

thf('185',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('186',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','153'])).

thf('188',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('190',plain,
    ( ( sk_C != sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['154','181'])).

thf('193',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('194',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_B
        = ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X1 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['82','147'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(condensation,[status(thm)],['199'])).

thf('201',plain,(
    zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['194','200'])).

thf('202',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['191','201'])).

thf('203',plain,(
    $false ),
    inference(demod,[status(thm)],['183','202'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.94HUG715m4
% 0.13/0.32  % Computer   : n001.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 09:44:59 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running portfolio for 600 s
% 0.13/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 36.78/36.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 36.78/36.99  % Solved by: fo/fo7.sh
% 36.78/36.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 36.78/36.99  % done 21454 iterations in 36.552s
% 36.78/36.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 36.78/36.99  % SZS output start Refutation
% 36.78/36.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 36.78/36.99  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 36.78/36.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 36.78/36.99  thf(sk_C_type, type, sk_C: $i).
% 36.78/36.99  thf(sk_B_type, type, sk_B: $i).
% 36.78/36.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 36.78/36.99  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 36.78/36.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 36.78/36.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 36.78/36.99  thf(sk_D_type, type, sk_D: $i).
% 36.78/36.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 36.78/36.99  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 36.78/36.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 36.78/36.99  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 36.78/36.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 36.78/36.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 36.78/36.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 36.78/36.99  thf(sk_A_type, type, sk_A: $i).
% 36.78/36.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 36.78/36.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 36.78/36.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 36.78/36.99  thf(t38_funct_2, conjecture,
% 36.78/36.99    (![A:$i,B:$i,C:$i,D:$i]:
% 36.78/36.99     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 36.78/36.99         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 36.78/36.99       ( ( r1_tarski @ C @ A ) =>
% 36.78/36.99         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 36.78/36.99           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 36.78/36.99             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 36.78/36.99             ( m1_subset_1 @
% 36.78/36.99               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 36.78/36.99               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 36.78/36.99  thf(zf_stmt_0, negated_conjecture,
% 36.78/36.99    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 36.78/36.99        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 36.78/36.99            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 36.78/36.99          ( ( r1_tarski @ C @ A ) =>
% 36.78/36.99            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 36.78/36.99              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 36.78/36.99                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 36.78/36.99                ( m1_subset_1 @
% 36.78/36.99                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 36.78/36.99                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 36.78/36.99    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 36.78/36.99  thf('0', plain,
% 36.78/36.99      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 36.78/36.99        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 36.78/36.99             sk_B)
% 36.78/36.99        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 36.78/36.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 36.78/36.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/36.99  thf('1', plain,
% 36.78/36.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.78/36.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/36.99  thf(dt_k2_partfun1, axiom,
% 36.78/36.99    (![A:$i,B:$i,C:$i,D:$i]:
% 36.78/36.99     ( ( ( v1_funct_1 @ C ) & 
% 36.78/36.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 36.78/36.99       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 36.78/36.99         ( m1_subset_1 @
% 36.78/36.99           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 36.78/36.99           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 36.78/36.99  thf('2', plain,
% 36.78/36.99      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 36.78/36.99         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 36.78/36.99          | ~ (v1_funct_1 @ X44)
% 36.78/36.99          | (v1_funct_1 @ (k2_partfun1 @ X45 @ X46 @ X44 @ X47)))),
% 36.78/36.99      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 36.78/36.99  thf('3', plain,
% 36.78/36.99      (![X0 : $i]:
% 36.78/36.99         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 36.78/36.99          | ~ (v1_funct_1 @ sk_D))),
% 36.78/36.99      inference('sup-', [status(thm)], ['1', '2'])).
% 36.78/36.99  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 36.78/36.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/36.99  thf('5', plain,
% 36.78/36.99      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 36.78/36.99      inference('demod', [status(thm)], ['3', '4'])).
% 36.78/36.99  thf('6', plain,
% 36.78/36.99      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 36.78/36.99        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 36.78/36.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 36.78/36.99      inference('demod', [status(thm)], ['0', '5'])).
% 36.78/36.99  thf('7', plain,
% 36.78/36.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.78/36.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/36.99  thf(redefinition_k2_partfun1, axiom,
% 36.78/36.99    (![A:$i,B:$i,C:$i,D:$i]:
% 36.78/36.99     ( ( ( v1_funct_1 @ C ) & 
% 36.78/36.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 36.78/36.99       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 36.78/36.99  thf('8', plain,
% 36.78/36.99      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 36.78/36.99         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 36.78/36.99          | ~ (v1_funct_1 @ X48)
% 36.78/36.99          | ((k2_partfun1 @ X49 @ X50 @ X48 @ X51) = (k7_relat_1 @ X48 @ X51)))),
% 36.78/36.99      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 36.78/36.99  thf('9', plain,
% 36.78/36.99      (![X0 : $i]:
% 36.78/36.99         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 36.78/36.99          | ~ (v1_funct_1 @ sk_D))),
% 36.78/36.99      inference('sup-', [status(thm)], ['7', '8'])).
% 36.78/36.99  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 36.78/36.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/36.99  thf('11', plain,
% 36.78/36.99      (![X0 : $i]:
% 36.78/36.99         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 36.78/36.99      inference('demod', [status(thm)], ['9', '10'])).
% 36.78/36.99  thf('12', plain,
% 36.78/36.99      (![X0 : $i]:
% 36.78/36.99         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 36.78/36.99      inference('demod', [status(thm)], ['9', '10'])).
% 36.78/36.99  thf('13', plain,
% 36.78/36.99      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 36.78/36.99        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 36.78/36.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 36.78/36.99      inference('demod', [status(thm)], ['6', '11', '12'])).
% 36.78/36.99  thf('14', plain, ((r1_tarski @ sk_C @ sk_A)),
% 36.78/36.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/36.99  thf('15', plain,
% 36.78/36.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.78/36.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/36.99  thf(cc2_relset_1, axiom,
% 36.78/36.99    (![A:$i,B:$i,C:$i]:
% 36.78/36.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 36.78/36.99       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 36.78/36.99  thf('16', plain,
% 36.78/36.99      (![X27 : $i, X28 : $i, X29 : $i]:
% 36.78/36.99         ((v5_relat_1 @ X27 @ X29)
% 36.78/36.99          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 36.78/36.99      inference('cnf', [status(esa)], [cc2_relset_1])).
% 36.78/36.99  thf('17', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 36.78/36.99      inference('sup-', [status(thm)], ['15', '16'])).
% 36.78/36.99  thf(d19_relat_1, axiom,
% 36.78/36.99    (![A:$i,B:$i]:
% 36.78/36.99     ( ( v1_relat_1 @ B ) =>
% 36.78/36.99       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 36.78/36.99  thf('18', plain,
% 36.78/36.99      (![X15 : $i, X16 : $i]:
% 36.78/36.99         (~ (v5_relat_1 @ X15 @ X16)
% 36.78/36.99          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 36.78/36.99          | ~ (v1_relat_1 @ X15))),
% 36.78/36.99      inference('cnf', [status(esa)], [d19_relat_1])).
% 36.78/36.99  thf('19', plain,
% 36.78/36.99      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 36.78/36.99      inference('sup-', [status(thm)], ['17', '18'])).
% 36.78/36.99  thf('20', plain,
% 36.78/36.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.78/36.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/36.99  thf(cc2_relat_1, axiom,
% 36.78/36.99    (![A:$i]:
% 36.78/36.99     ( ( v1_relat_1 @ A ) =>
% 36.78/36.99       ( ![B:$i]:
% 36.78/36.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 36.78/36.99  thf('21', plain,
% 36.78/36.99      (![X13 : $i, X14 : $i]:
% 36.78/36.99         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 36.78/36.99          | (v1_relat_1 @ X13)
% 36.78/36.99          | ~ (v1_relat_1 @ X14))),
% 36.78/36.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 36.78/36.99  thf('22', plain,
% 36.78/36.99      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 36.78/36.99      inference('sup-', [status(thm)], ['20', '21'])).
% 36.78/36.99  thf(fc6_relat_1, axiom,
% 36.78/36.99    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 36.78/36.99  thf('23', plain,
% 36.78/36.99      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 36.78/36.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 36.78/36.99  thf('24', plain, ((v1_relat_1 @ sk_D)),
% 36.78/36.99      inference('demod', [status(thm)], ['22', '23'])).
% 36.78/36.99  thf('25', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 36.78/36.99      inference('demod', [status(thm)], ['19', '24'])).
% 36.78/36.99  thf(d1_funct_2, axiom,
% 36.78/36.99    (![A:$i,B:$i,C:$i]:
% 36.78/36.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 36.78/36.99       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 36.78/36.99           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 36.78/36.99             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 36.78/36.99         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 36.78/36.99           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 36.78/36.99             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 36.78/36.99  thf(zf_stmt_1, axiom,
% 36.78/36.99    (![B:$i,A:$i]:
% 36.78/36.99     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 36.78/36.99       ( zip_tseitin_0 @ B @ A ) ))).
% 36.78/36.99  thf('26', plain,
% 36.78/36.99      (![X36 : $i, X37 : $i]:
% 36.78/36.99         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 36.78/36.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 36.78/36.99  thf(t3_xboole_1, axiom,
% 36.78/36.99    (![A:$i]:
% 36.78/36.99     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 36.78/36.99  thf('27', plain,
% 36.78/36.99      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 36.78/36.99      inference('cnf', [status(esa)], [t3_xboole_1])).
% 36.78/36.99  thf('28', plain,
% 36.78/36.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.78/36.99         (~ (r1_tarski @ X1 @ X0)
% 36.78/36.99          | (zip_tseitin_0 @ X0 @ X2)
% 36.78/36.99          | ((X1) = (k1_xboole_0)))),
% 36.78/36.99      inference('sup-', [status(thm)], ['26', '27'])).
% 36.78/36.99  thf('29', plain,
% 36.78/36.99      (![X0 : $i]:
% 36.78/36.99         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B @ X0))),
% 36.78/36.99      inference('sup-', [status(thm)], ['25', '28'])).
% 36.78/36.99  thf('30', plain,
% 36.78/36.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.78/36.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/36.99  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 36.78/36.99  thf(zf_stmt_3, axiom,
% 36.78/36.99    (![C:$i,B:$i,A:$i]:
% 36.78/36.99     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 36.78/36.99       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 36.78/36.99  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 36.78/36.99  thf(zf_stmt_5, axiom,
% 36.78/36.99    (![A:$i,B:$i,C:$i]:
% 36.78/36.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 36.78/36.99       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 36.78/36.99         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 36.78/36.99           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 36.78/36.99             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 36.78/36.99  thf('31', plain,
% 36.78/36.99      (![X41 : $i, X42 : $i, X43 : $i]:
% 36.78/36.99         (~ (zip_tseitin_0 @ X41 @ X42)
% 36.78/36.99          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 36.78/36.99          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 36.78/36.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 36.78/36.99  thf('32', plain,
% 36.78/36.99      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 36.78/36.99      inference('sup-', [status(thm)], ['30', '31'])).
% 36.78/36.99  thf('33', plain,
% 36.78/36.99      ((((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 36.78/36.99        | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 36.78/36.99      inference('sup-', [status(thm)], ['29', '32'])).
% 36.78/36.99  thf('34', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 36.78/36.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/36.99  thf('35', plain,
% 36.78/36.99      (![X38 : $i, X39 : $i, X40 : $i]:
% 36.78/36.99         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 36.78/36.99          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 36.78/36.99          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 36.78/36.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 36.78/36.99  thf('36', plain,
% 36.78/36.99      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 36.78/36.99        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 36.78/36.99      inference('sup-', [status(thm)], ['34', '35'])).
% 36.78/36.99  thf('37', plain,
% 36.78/36.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.78/36.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/36.99  thf(redefinition_k1_relset_1, axiom,
% 36.78/36.99    (![A:$i,B:$i,C:$i]:
% 36.78/36.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 36.78/36.99       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 36.78/36.99  thf('38', plain,
% 36.78/36.99      (![X30 : $i, X31 : $i, X32 : $i]:
% 36.78/36.99         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 36.78/36.99          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 36.78/36.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 36.78/36.99  thf('39', plain,
% 36.78/36.99      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 36.78/37.00      inference('sup-', [status(thm)], ['37', '38'])).
% 36.78/37.00  thf('40', plain,
% 36.78/37.00      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 36.78/37.00      inference('demod', [status(thm)], ['36', '39'])).
% 36.78/37.00  thf('41', plain,
% 36.78/37.00      ((((k2_relat_1 @ sk_D) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 36.78/37.00      inference('sup-', [status(thm)], ['33', '40'])).
% 36.78/37.00  thf('42', plain,
% 36.78/37.00      (![X36 : $i, X37 : $i]:
% 36.78/37.00         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 36.78/37.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 36.78/37.00  thf(t113_zfmisc_1, axiom,
% 36.78/37.00    (![A:$i,B:$i]:
% 36.78/37.00     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 36.78/37.00       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 36.78/37.00  thf('43', plain,
% 36.78/37.00      (![X8 : $i, X9 : $i]:
% 36.78/37.00         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 36.78/37.00      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 36.78/37.00  thf('44', plain,
% 36.78/37.00      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 36.78/37.00      inference('simplify', [status(thm)], ['43'])).
% 36.78/37.00  thf(d10_xboole_0, axiom,
% 36.78/37.00    (![A:$i,B:$i]:
% 36.78/37.00     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 36.78/37.00  thf('45', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 36.78/37.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.78/37.00  thf('46', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 36.78/37.00      inference('simplify', [status(thm)], ['45'])).
% 36.78/37.00  thf(t3_subset, axiom,
% 36.78/37.00    (![A:$i,B:$i]:
% 36.78/37.00     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 36.78/37.00  thf('47', plain,
% 36.78/37.00      (![X10 : $i, X12 : $i]:
% 36.78/37.00         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 36.78/37.00      inference('cnf', [status(esa)], [t3_subset])).
% 36.78/37.00  thf('48', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['46', '47'])).
% 36.78/37.00  thf('49', plain,
% 36.78/37.00      (![X27 : $i, X28 : $i, X29 : $i]:
% 36.78/37.00         ((v5_relat_1 @ X27 @ X29)
% 36.78/37.00          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 36.78/37.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 36.78/37.00  thf('50', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i]: (v5_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0)),
% 36.78/37.00      inference('sup-', [status(thm)], ['48', '49'])).
% 36.78/37.00  thf('51', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 36.78/37.00      inference('sup+', [status(thm)], ['44', '50'])).
% 36.78/37.00  thf('52', plain,
% 36.78/37.00      (![X15 : $i, X16 : $i]:
% 36.78/37.00         (~ (v5_relat_1 @ X15 @ X16)
% 36.78/37.00          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 36.78/37.00          | ~ (v1_relat_1 @ X15))),
% 36.78/37.00      inference('cnf', [status(esa)], [d19_relat_1])).
% 36.78/37.00  thf('53', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         (~ (v1_relat_1 @ k1_xboole_0)
% 36.78/37.00          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['51', '52'])).
% 36.78/37.00  thf('54', plain,
% 36.78/37.00      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 36.78/37.00      inference('simplify', [status(thm)], ['43'])).
% 36.78/37.00  thf('55', plain,
% 36.78/37.00      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 36.78/37.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 36.78/37.00  thf('56', plain, ((v1_relat_1 @ k1_xboole_0)),
% 36.78/37.00      inference('sup+', [status(thm)], ['54', '55'])).
% 36.78/37.00  thf('57', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['46', '47'])).
% 36.78/37.00  thf('58', plain,
% 36.78/37.00      (![X8 : $i, X9 : $i]:
% 36.78/37.00         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 36.78/37.00      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 36.78/37.00  thf('59', plain,
% 36.78/37.00      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 36.78/37.00      inference('simplify', [status(thm)], ['58'])).
% 36.78/37.00  thf('60', plain,
% 36.78/37.00      (![X27 : $i, X28 : $i, X29 : $i]:
% 36.78/37.00         ((v5_relat_1 @ X27 @ X29)
% 36.78/37.00          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 36.78/37.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 36.78/37.00  thf('61', plain,
% 36.78/37.00      (![X1 : $i]:
% 36.78/37.00         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 36.78/37.00          | (v5_relat_1 @ X1 @ k1_xboole_0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['59', '60'])).
% 36.78/37.00  thf('62', plain, ((v5_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 36.78/37.00      inference('sup-', [status(thm)], ['57', '61'])).
% 36.78/37.00  thf('63', plain,
% 36.78/37.00      (![X15 : $i, X16 : $i]:
% 36.78/37.00         (~ (v5_relat_1 @ X15 @ X16)
% 36.78/37.00          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 36.78/37.00          | ~ (v1_relat_1 @ X15))),
% 36.78/37.00      inference('cnf', [status(esa)], [d19_relat_1])).
% 36.78/37.00  thf('64', plain,
% 36.78/37.00      ((~ (v1_relat_1 @ k1_xboole_0)
% 36.78/37.00        | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['62', '63'])).
% 36.78/37.00  thf('65', plain, ((v1_relat_1 @ k1_xboole_0)),
% 36.78/37.00      inference('sup+', [status(thm)], ['54', '55'])).
% 36.78/37.00  thf('66', plain, ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 36.78/37.00      inference('demod', [status(thm)], ['64', '65'])).
% 36.78/37.00  thf('67', plain,
% 36.78/37.00      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 36.78/37.00      inference('cnf', [status(esa)], [t3_xboole_1])).
% 36.78/37.00  thf('68', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['66', '67'])).
% 36.78/37.00  thf('69', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 36.78/37.00      inference('demod', [status(thm)], ['53', '56', '68'])).
% 36.78/37.00  thf('70', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.78/37.00         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 36.78/37.00      inference('sup+', [status(thm)], ['42', '69'])).
% 36.78/37.00  thf('71', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 36.78/37.00      inference('demod', [status(thm)], ['19', '24'])).
% 36.78/37.00  thf('72', plain,
% 36.78/37.00      (![X0 : $i, X2 : $i]:
% 36.78/37.00         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 36.78/37.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.78/37.00  thf('73', plain,
% 36.78/37.00      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 36.78/37.00        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 36.78/37.00      inference('sup-', [status(thm)], ['71', '72'])).
% 36.78/37.00  thf('74', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         ((zip_tseitin_0 @ sk_B @ X0) | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 36.78/37.00      inference('sup-', [status(thm)], ['70', '73'])).
% 36.78/37.00  thf('75', plain,
% 36.78/37.00      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 36.78/37.00      inference('sup-', [status(thm)], ['30', '31'])).
% 36.78/37.00  thf('76', plain,
% 36.78/37.00      ((((sk_B) = (k2_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 36.78/37.00      inference('sup-', [status(thm)], ['74', '75'])).
% 36.78/37.00  thf('77', plain,
% 36.78/37.00      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 36.78/37.00      inference('demod', [status(thm)], ['36', '39'])).
% 36.78/37.00  thf('78', plain,
% 36.78/37.00      ((((sk_B) = (k2_relat_1 @ sk_D)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 36.78/37.00      inference('sup-', [status(thm)], ['76', '77'])).
% 36.78/37.00  thf('79', plain,
% 36.78/37.00      ((((sk_B) = (k1_xboole_0))
% 36.78/37.00        | ((sk_A) = (k1_relat_1 @ sk_D))
% 36.78/37.00        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 36.78/37.00      inference('sup+', [status(thm)], ['41', '78'])).
% 36.78/37.00  thf('80', plain,
% 36.78/37.00      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((sk_B) = (k1_xboole_0)))),
% 36.78/37.00      inference('simplify', [status(thm)], ['79'])).
% 36.78/37.00  thf('81', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 36.78/37.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/37.00  thf('82', plain,
% 36.78/37.00      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 36.78/37.00      inference('split', [status(esa)], ['81'])).
% 36.78/37.00  thf('83', plain,
% 36.78/37.00      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('split', [status(esa)], ['81'])).
% 36.78/37.00  thf('84', plain,
% 36.78/37.00      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 36.78/37.00        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 36.78/37.00             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 36.78/37.00      inference('demod', [status(thm)], ['0', '5'])).
% 36.78/37.00  thf('85', plain,
% 36.78/37.00      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 36.78/37.00            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 36.78/37.00         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 36.78/37.00              sk_B)))
% 36.78/37.00         <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('sup-', [status(thm)], ['83', '84'])).
% 36.78/37.00  thf('86', plain,
% 36.78/37.00      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('split', [status(esa)], ['81'])).
% 36.78/37.00  thf('87', plain,
% 36.78/37.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.78/37.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/37.00  thf('88', plain,
% 36.78/37.00      (((m1_subset_1 @ sk_D @ 
% 36.78/37.00         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 36.78/37.00         <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('sup+', [status(thm)], ['86', '87'])).
% 36.78/37.00  thf('89', plain,
% 36.78/37.00      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 36.78/37.00      inference('simplify', [status(thm)], ['43'])).
% 36.78/37.00  thf('90', plain,
% 36.78/37.00      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 36.78/37.00         <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('demod', [status(thm)], ['88', '89'])).
% 36.78/37.00  thf('91', plain,
% 36.78/37.00      (![X10 : $i, X11 : $i]:
% 36.78/37.00         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 36.78/37.00      inference('cnf', [status(esa)], [t3_subset])).
% 36.78/37.00  thf('92', plain,
% 36.78/37.00      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('sup-', [status(thm)], ['90', '91'])).
% 36.78/37.00  thf('93', plain,
% 36.78/37.00      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 36.78/37.00      inference('cnf', [status(esa)], [t3_xboole_1])).
% 36.78/37.00  thf('94', plain,
% 36.78/37.00      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('sup-', [status(thm)], ['92', '93'])).
% 36.78/37.00  thf('95', plain,
% 36.78/37.00      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('split', [status(esa)], ['81'])).
% 36.78/37.00  thf('96', plain, ((r1_tarski @ sk_C @ sk_A)),
% 36.78/37.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/37.00  thf('97', plain,
% 36.78/37.00      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('sup+', [status(thm)], ['95', '96'])).
% 36.78/37.00  thf('98', plain,
% 36.78/37.00      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 36.78/37.00      inference('cnf', [status(esa)], [t3_xboole_1])).
% 36.78/37.00  thf('99', plain,
% 36.78/37.00      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('sup-', [status(thm)], ['97', '98'])).
% 36.78/37.00  thf('100', plain,
% 36.78/37.00      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('sup-', [status(thm)], ['92', '93'])).
% 36.78/37.00  thf('101', plain, ((v1_funct_1 @ sk_D)),
% 36.78/37.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/37.00  thf('102', plain,
% 36.78/37.00      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('sup+', [status(thm)], ['100', '101'])).
% 36.78/37.00  thf('103', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 36.78/37.00      inference('demod', [status(thm)], ['53', '56', '68'])).
% 36.78/37.00  thf('104', plain,
% 36.78/37.00      (![X10 : $i, X12 : $i]:
% 36.78/37.00         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 36.78/37.00      inference('cnf', [status(esa)], [t3_subset])).
% 36.78/37.00  thf('105', plain,
% 36.78/37.00      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['103', '104'])).
% 36.78/37.00  thf('106', plain,
% 36.78/37.00      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 36.78/37.00         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 36.78/37.00          | ~ (v1_funct_1 @ X48)
% 36.78/37.00          | ((k2_partfun1 @ X49 @ X50 @ X48 @ X51) = (k7_relat_1 @ X48 @ X51)))),
% 36.78/37.00      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 36.78/37.00  thf('107', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.78/37.00         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 36.78/37.00            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 36.78/37.00          | ~ (v1_funct_1 @ k1_xboole_0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['105', '106'])).
% 36.78/37.00  thf(t88_relat_1, axiom,
% 36.78/37.00    (![A:$i,B:$i]:
% 36.78/37.00     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 36.78/37.00  thf('108', plain,
% 36.78/37.00      (![X23 : $i, X24 : $i]:
% 36.78/37.00         ((r1_tarski @ (k7_relat_1 @ X23 @ X24) @ X23) | ~ (v1_relat_1 @ X23))),
% 36.78/37.00      inference('cnf', [status(esa)], [t88_relat_1])).
% 36.78/37.00  thf('109', plain,
% 36.78/37.00      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 36.78/37.00      inference('cnf', [status(esa)], [t3_xboole_1])).
% 36.78/37.00  thf('110', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         (~ (v1_relat_1 @ k1_xboole_0)
% 36.78/37.00          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 36.78/37.00      inference('sup-', [status(thm)], ['108', '109'])).
% 36.78/37.00  thf('111', plain, ((v1_relat_1 @ k1_xboole_0)),
% 36.78/37.00      inference('sup+', [status(thm)], ['54', '55'])).
% 36.78/37.00  thf('112', plain,
% 36.78/37.00      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 36.78/37.00      inference('demod', [status(thm)], ['110', '111'])).
% 36.78/37.00  thf('113', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.78/37.00         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 36.78/37.00          | ~ (v1_funct_1 @ k1_xboole_0))),
% 36.78/37.00      inference('demod', [status(thm)], ['107', '112'])).
% 36.78/37.00  thf('114', plain,
% 36.78/37.00      ((![X0 : $i, X1 : $i, X2 : $i]:
% 36.78/37.00          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 36.78/37.00         <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('sup-', [status(thm)], ['102', '113'])).
% 36.78/37.00  thf('115', plain,
% 36.78/37.00      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('sup-', [status(thm)], ['97', '98'])).
% 36.78/37.00  thf('116', plain,
% 36.78/37.00      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 36.78/37.00      inference('simplify', [status(thm)], ['43'])).
% 36.78/37.00  thf('117', plain,
% 36.78/37.00      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['103', '104'])).
% 36.78/37.00  thf('118', plain,
% 36.78/37.00      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('split', [status(esa)], ['81'])).
% 36.78/37.00  thf('119', plain,
% 36.78/37.00      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('sup-', [status(thm)], ['92', '93'])).
% 36.78/37.00  thf('120', plain,
% 36.78/37.00      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('sup-', [status(thm)], ['97', '98'])).
% 36.78/37.00  thf('121', plain,
% 36.78/37.00      ((![X0 : $i, X1 : $i, X2 : $i]:
% 36.78/37.00          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 36.78/37.00         <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('sup-', [status(thm)], ['102', '113'])).
% 36.78/37.00  thf('122', plain,
% 36.78/37.00      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 36.78/37.00      inference('sup-', [status(thm)], ['97', '98'])).
% 36.78/37.00  thf('123', plain,
% 36.78/37.00      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['103', '104'])).
% 36.78/37.00  thf('124', plain,
% 36.78/37.00      (![X30 : $i, X31 : $i, X32 : $i]:
% 36.78/37.00         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 36.78/37.00          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 36.78/37.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 36.78/37.00  thf('125', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i]:
% 36.78/37.00         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['123', '124'])).
% 36.78/37.00  thf('126', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 36.78/37.00      inference('demod', [status(thm)], ['53', '56', '68'])).
% 36.78/37.00  thf('127', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i]:
% 36.78/37.00         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['123', '124'])).
% 36.78/37.00  thf(t91_relat_1, axiom,
% 36.78/37.00    (![A:$i,B:$i]:
% 36.78/37.00     ( ( v1_relat_1 @ B ) =>
% 36.78/37.00       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 36.78/37.00         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 36.78/37.00  thf('128', plain,
% 36.78/37.00      (![X25 : $i, X26 : $i]:
% 36.78/37.00         (~ (r1_tarski @ X25 @ (k1_relat_1 @ X26))
% 36.78/37.00          | ((k1_relat_1 @ (k7_relat_1 @ X26 @ X25)) = (X25))
% 36.78/37.00          | ~ (v1_relat_1 @ X26))),
% 36.78/37.00      inference('cnf', [status(esa)], [t91_relat_1])).
% 36.78/37.00  thf('129', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.78/37.00         (~ (r1_tarski @ X2 @ (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))
% 36.78/37.00          | ~ (v1_relat_1 @ k1_xboole_0)
% 36.78/37.00          | ((k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ X2)) = (X2)))),
% 36.78/37.00      inference('sup-', [status(thm)], ['127', '128'])).
% 36.78/37.00  thf('130', plain, ((v1_relat_1 @ k1_xboole_0)),
% 36.78/37.00      inference('sup+', [status(thm)], ['54', '55'])).
% 36.78/37.00  thf('131', plain,
% 36.78/37.00      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 36.78/37.00      inference('demod', [status(thm)], ['110', '111'])).
% 36.78/37.00  thf('132', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.78/37.00         (~ (r1_tarski @ X2 @ (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))
% 36.78/37.00          | ((k1_relat_1 @ k1_xboole_0) = (X2)))),
% 36.78/37.00      inference('demod', [status(thm)], ['129', '130', '131'])).
% 36.78/37.00  thf('133', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['126', '132'])).
% 36.78/37.00  thf('134', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i]:
% 36.78/37.00         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 36.78/37.00      inference('demod', [status(thm)], ['125', '133'])).
% 36.78/37.00  thf('135', plain,
% 36.78/37.00      (![X38 : $i, X39 : $i, X40 : $i]:
% 36.78/37.00         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 36.78/37.00          | (v1_funct_2 @ X40 @ X38 @ X39)
% 36.78/37.00          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 36.78/37.00      inference('cnf', [status(esa)], [zf_stmt_3])).
% 36.78/37.00  thf('136', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i]:
% 36.78/37.00         (((X1) != (k1_xboole_0))
% 36.78/37.00          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 36.78/37.00          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['134', '135'])).
% 36.78/37.00  thf('137', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 36.78/37.00          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 36.78/37.00      inference('simplify', [status(thm)], ['136'])).
% 36.78/37.00  thf('138', plain,
% 36.78/37.00      (![X36 : $i, X37 : $i]:
% 36.78/37.00         ((zip_tseitin_0 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 36.78/37.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 36.78/37.00  thf('139', plain, (![X36 : $i]: (zip_tseitin_0 @ X36 @ k1_xboole_0)),
% 36.78/37.00      inference('simplify', [status(thm)], ['138'])).
% 36.78/37.00  thf('140', plain,
% 36.78/37.00      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['103', '104'])).
% 36.78/37.00  thf('141', plain,
% 36.78/37.00      (![X41 : $i, X42 : $i, X43 : $i]:
% 36.78/37.00         (~ (zip_tseitin_0 @ X41 @ X42)
% 36.78/37.00          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 36.78/37.00          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 36.78/37.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 36.78/37.00  thf('142', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i]:
% 36.78/37.00         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 36.78/37.00      inference('sup-', [status(thm)], ['140', '141'])).
% 36.78/37.00  thf('143', plain,
% 36.78/37.00      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 36.78/37.00      inference('sup-', [status(thm)], ['139', '142'])).
% 36.78/37.00  thf('144', plain,
% 36.78/37.00      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 36.78/37.00      inference('demod', [status(thm)], ['137', '143'])).
% 36.78/37.00  thf('145', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 36.78/37.00      inference('demod', [status(thm)],
% 36.78/37.00                ['85', '94', '99', '114', '115', '116', '117', '118', '119', 
% 36.78/37.00                 '120', '121', '122', '144'])).
% 36.78/37.00  thf('146', plain,
% 36.78/37.00      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 36.78/37.00      inference('split', [status(esa)], ['81'])).
% 36.78/37.00  thf('147', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 36.78/37.00      inference('sat_resolution*', [status(thm)], ['145', '146'])).
% 36.78/37.00  thf('148', plain, (((sk_B) != (k1_xboole_0))),
% 36.78/37.00      inference('simpl_trail', [status(thm)], ['82', '147'])).
% 36.78/37.00  thf('149', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 36.78/37.00      inference('simplify_reflect-', [status(thm)], ['80', '148'])).
% 36.78/37.00  thf('150', plain,
% 36.78/37.00      (![X25 : $i, X26 : $i]:
% 36.78/37.00         (~ (r1_tarski @ X25 @ (k1_relat_1 @ X26))
% 36.78/37.00          | ((k1_relat_1 @ (k7_relat_1 @ X26 @ X25)) = (X25))
% 36.78/37.00          | ~ (v1_relat_1 @ X26))),
% 36.78/37.00      inference('cnf', [status(esa)], [t91_relat_1])).
% 36.78/37.00  thf('151', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         (~ (r1_tarski @ X0 @ sk_A)
% 36.78/37.00          | ~ (v1_relat_1 @ sk_D)
% 36.78/37.00          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 36.78/37.00      inference('sup-', [status(thm)], ['149', '150'])).
% 36.78/37.00  thf('152', plain, ((v1_relat_1 @ sk_D)),
% 36.78/37.00      inference('demod', [status(thm)], ['22', '23'])).
% 36.78/37.00  thf('153', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         (~ (r1_tarski @ X0 @ sk_A)
% 36.78/37.00          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 36.78/37.00      inference('demod', [status(thm)], ['151', '152'])).
% 36.78/37.00  thf('154', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 36.78/37.00      inference('sup-', [status(thm)], ['14', '153'])).
% 36.78/37.00  thf('155', plain,
% 36.78/37.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.78/37.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.78/37.00  thf('156', plain,
% 36.78/37.00      (![X10 : $i, X11 : $i]:
% 36.78/37.00         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 36.78/37.00      inference('cnf', [status(esa)], [t3_subset])).
% 36.78/37.00  thf('157', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 36.78/37.00      inference('sup-', [status(thm)], ['155', '156'])).
% 36.78/37.00  thf('158', plain,
% 36.78/37.00      (![X23 : $i, X24 : $i]:
% 36.78/37.00         ((r1_tarski @ (k7_relat_1 @ X23 @ X24) @ X23) | ~ (v1_relat_1 @ X23))),
% 36.78/37.00      inference('cnf', [status(esa)], [t88_relat_1])).
% 36.78/37.00  thf(t1_xboole_1, axiom,
% 36.78/37.00    (![A:$i,B:$i,C:$i]:
% 36.78/37.00     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 36.78/37.00       ( r1_tarski @ A @ C ) ))).
% 36.78/37.00  thf('159', plain,
% 36.78/37.00      (![X3 : $i, X4 : $i, X5 : $i]:
% 36.78/37.00         (~ (r1_tarski @ X3 @ X4)
% 36.78/37.00          | ~ (r1_tarski @ X4 @ X5)
% 36.78/37.00          | (r1_tarski @ X3 @ X5))),
% 36.78/37.00      inference('cnf', [status(esa)], [t1_xboole_1])).
% 36.78/37.00  thf('160', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.78/37.00         (~ (v1_relat_1 @ X0)
% 36.78/37.00          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 36.78/37.00          | ~ (r1_tarski @ X0 @ X2))),
% 36.78/37.00      inference('sup-', [status(thm)], ['158', '159'])).
% 36.78/37.00  thf('161', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 36.78/37.00          | ~ (v1_relat_1 @ sk_D))),
% 36.78/37.00      inference('sup-', [status(thm)], ['157', '160'])).
% 36.78/37.00  thf('162', plain, ((v1_relat_1 @ sk_D)),
% 36.78/37.00      inference('demod', [status(thm)], ['22', '23'])).
% 36.78/37.00  thf('163', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 36.78/37.00      inference('demod', [status(thm)], ['161', '162'])).
% 36.78/37.00  thf('164', plain,
% 36.78/37.00      (![X10 : $i, X12 : $i]:
% 36.78/37.00         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 36.78/37.00      inference('cnf', [status(esa)], [t3_subset])).
% 36.78/37.00  thf('165', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 36.78/37.00          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.78/37.00      inference('sup-', [status(thm)], ['163', '164'])).
% 36.78/37.00  thf('166', plain,
% 36.78/37.00      (![X27 : $i, X28 : $i, X29 : $i]:
% 36.78/37.00         ((v5_relat_1 @ X27 @ X29)
% 36.78/37.00          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 36.78/37.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 36.78/37.00  thf('167', plain,
% 36.78/37.00      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 36.78/37.00      inference('sup-', [status(thm)], ['165', '166'])).
% 36.78/37.00  thf('168', plain,
% 36.78/37.00      (![X15 : $i, X16 : $i]:
% 36.78/37.00         (~ (v5_relat_1 @ X15 @ X16)
% 36.78/37.00          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 36.78/37.00          | ~ (v1_relat_1 @ X15))),
% 36.78/37.00      inference('cnf', [status(esa)], [d19_relat_1])).
% 36.78/37.00  thf('169', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 36.78/37.00          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 36.78/37.00      inference('sup-', [status(thm)], ['167', '168'])).
% 36.78/37.00  thf('170', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 36.78/37.00          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 36.78/37.00      inference('sup-', [status(thm)], ['163', '164'])).
% 36.78/37.00  thf('171', plain,
% 36.78/37.00      (![X13 : $i, X14 : $i]:
% 36.78/37.00         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 36.78/37.00          | (v1_relat_1 @ X13)
% 36.78/37.00          | ~ (v1_relat_1 @ X14))),
% 36.78/37.00      inference('cnf', [status(esa)], [cc2_relat_1])).
% 36.78/37.00  thf('172', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 36.78/37.00          | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 36.78/37.00      inference('sup-', [status(thm)], ['170', '171'])).
% 36.78/37.00  thf('173', plain,
% 36.78/37.00      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 36.78/37.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 36.78/37.00  thf('174', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 36.78/37.00      inference('demod', [status(thm)], ['172', '173'])).
% 36.78/37.00  thf('175', plain,
% 36.78/37.00      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 36.78/37.00      inference('demod', [status(thm)], ['169', '174'])).
% 36.78/37.00  thf('176', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 36.78/37.00      inference('simplify', [status(thm)], ['45'])).
% 36.78/37.00  thf(t11_relset_1, axiom,
% 36.78/37.00    (![A:$i,B:$i,C:$i]:
% 36.78/37.00     ( ( v1_relat_1 @ C ) =>
% 36.78/37.00       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 36.78/37.00           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 36.78/37.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 36.78/37.00  thf('177', plain,
% 36.78/37.00      (![X33 : $i, X34 : $i, X35 : $i]:
% 36.78/37.00         (~ (r1_tarski @ (k1_relat_1 @ X33) @ X34)
% 36.78/37.00          | ~ (r1_tarski @ (k2_relat_1 @ X33) @ X35)
% 36.78/37.00          | (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 36.78/37.00          | ~ (v1_relat_1 @ X33))),
% 36.78/37.00      inference('cnf', [status(esa)], [t11_relset_1])).
% 36.78/37.00  thf('178', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i]:
% 36.78/37.00         (~ (v1_relat_1 @ X0)
% 36.78/37.00          | (m1_subset_1 @ X0 @ 
% 36.78/37.00             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 36.78/37.00          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 36.78/37.00      inference('sup-', [status(thm)], ['176', '177'])).
% 36.78/37.00  thf('179', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 36.78/37.00           (k1_zfmisc_1 @ 
% 36.78/37.00            (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))
% 36.78/37.00          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 36.78/37.00      inference('sup-', [status(thm)], ['175', '178'])).
% 36.78/37.00  thf('180', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 36.78/37.00      inference('demod', [status(thm)], ['172', '173'])).
% 36.78/37.00  thf('181', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 36.78/37.00          (k1_zfmisc_1 @ 
% 36.78/37.00           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 36.78/37.00      inference('demod', [status(thm)], ['179', '180'])).
% 36.78/37.00  thf('182', plain,
% 36.78/37.00      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 36.78/37.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 36.78/37.00      inference('sup+', [status(thm)], ['154', '181'])).
% 36.78/37.00  thf('183', plain,
% 36.78/37.00      (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 36.78/37.00      inference('demod', [status(thm)], ['13', '182'])).
% 36.78/37.00  thf('184', plain,
% 36.78/37.00      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 36.78/37.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 36.78/37.00      inference('sup+', [status(thm)], ['154', '181'])).
% 36.78/37.00  thf('185', plain,
% 36.78/37.00      (![X30 : $i, X31 : $i, X32 : $i]:
% 36.78/37.00         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 36.78/37.00          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 36.78/37.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 36.78/37.00  thf('186', plain,
% 36.78/37.00      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C))
% 36.78/37.00         = (k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)))),
% 36.78/37.00      inference('sup-', [status(thm)], ['184', '185'])).
% 36.78/37.00  thf('187', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 36.78/37.00      inference('sup-', [status(thm)], ['14', '153'])).
% 36.78/37.00  thf('188', plain,
% 36.78/37.00      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 36.78/37.00      inference('demod', [status(thm)], ['186', '187'])).
% 36.78/37.00  thf('189', plain,
% 36.78/37.00      (![X38 : $i, X39 : $i, X40 : $i]:
% 36.78/37.00         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 36.78/37.00          | (v1_funct_2 @ X40 @ X38 @ X39)
% 36.78/37.00          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 36.78/37.00      inference('cnf', [status(esa)], [zf_stmt_3])).
% 36.78/37.00  thf('190', plain,
% 36.78/37.00      ((((sk_C) != (sk_C))
% 36.78/37.00        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 36.78/37.00        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 36.78/37.00      inference('sup-', [status(thm)], ['188', '189'])).
% 36.78/37.00  thf('191', plain,
% 36.78/37.00      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 36.78/37.00        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C))),
% 36.78/37.00      inference('simplify', [status(thm)], ['190'])).
% 36.78/37.00  thf('192', plain,
% 36.78/37.00      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 36.78/37.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 36.78/37.00      inference('sup+', [status(thm)], ['154', '181'])).
% 36.78/37.00  thf('193', plain,
% 36.78/37.00      (![X41 : $i, X42 : $i, X43 : $i]:
% 36.78/37.00         (~ (zip_tseitin_0 @ X41 @ X42)
% 36.78/37.00          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 36.78/37.00          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 36.78/37.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 36.78/37.00  thf('194', plain,
% 36.78/37.00      (((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 36.78/37.00        | ~ (zip_tseitin_0 @ sk_B @ sk_C))),
% 36.78/37.00      inference('sup-', [status(thm)], ['192', '193'])).
% 36.78/37.00  thf('195', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B @ X0))),
% 36.78/37.00      inference('sup-', [status(thm)], ['25', '28'])).
% 36.78/37.00  thf('196', plain,
% 36.78/37.00      (![X0 : $i]:
% 36.78/37.00         ((zip_tseitin_0 @ sk_B @ X0) | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 36.78/37.00      inference('sup-', [status(thm)], ['70', '73'])).
% 36.78/37.00  thf('197', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i]:
% 36.78/37.00         (((sk_B) = (k1_xboole_0))
% 36.78/37.00          | (zip_tseitin_0 @ sk_B @ X1)
% 36.78/37.00          | (zip_tseitin_0 @ sk_B @ X0))),
% 36.78/37.00      inference('sup+', [status(thm)], ['195', '196'])).
% 36.78/37.00  thf('198', plain, (((sk_B) != (k1_xboole_0))),
% 36.78/37.00      inference('simpl_trail', [status(thm)], ['82', '147'])).
% 36.78/37.00  thf('199', plain,
% 36.78/37.00      (![X0 : $i, X1 : $i]:
% 36.78/37.00         ((zip_tseitin_0 @ sk_B @ X1) | (zip_tseitin_0 @ sk_B @ X0))),
% 36.78/37.00      inference('simplify_reflect-', [status(thm)], ['197', '198'])).
% 36.78/37.00  thf('200', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 36.78/37.00      inference('condensation', [status(thm)], ['199'])).
% 36.78/37.00  thf('201', plain,
% 36.78/37.00      ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)),
% 36.78/37.00      inference('demod', [status(thm)], ['194', '200'])).
% 36.78/37.00  thf('202', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 36.78/37.00      inference('demod', [status(thm)], ['191', '201'])).
% 36.78/37.00  thf('203', plain, ($false), inference('demod', [status(thm)], ['183', '202'])).
% 36.78/37.00  
% 36.78/37.00  % SZS output end Refutation
% 36.78/37.00  
% 36.78/37.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
