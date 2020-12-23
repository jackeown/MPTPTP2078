%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1NokLXXWWm

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:38 EST 2020

% Result     : Theorem 45.94s
% Output     : Refutation 45.94s
% Verified   : 
% Statistics : Number of formulae       :  222 (2118 expanded)
%              Number of leaves         :   44 ( 632 expanded)
%              Depth                    :   26
%              Number of atoms          : 1673 (30753 expanded)
%              Number of equality atoms :  131 (2036 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['19','22'])).

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

thf('24',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

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
      = sk_B )
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
      = sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['19','22'])).

thf('43',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('44',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('51',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('52',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('56',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('57',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','57'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('62',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('64',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('67',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('69',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('70',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('71',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('72',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('73',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('74',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','62','67','68','69','70','71','72','73'])).

thf('75',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('76',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('79',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ( ( k2_partfun1 @ X49 @ X50 @ X48 @ X51 )
        = ( k7_relat_1 @ X48 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('83',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X20 @ X21 ) @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('84',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('87',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('88',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','89'])).

thf('91',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('93',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','90'])).

thf('94',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('95',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('98',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('99',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','100'])).

thf('102',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['86','87'])).

thf('103',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','103'])).

thf('105',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('109',plain,(
    ! [X36: $i] :
      ( zip_tseitin_0 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('111',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['107','113'])).

thf('115',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['74','91','92','93','114'])).

thf('116',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('117',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['115','116'])).

thf('118',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['49','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['47','118'])).

thf('120',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('121',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('123',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('131',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X20 @ X21 ) @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('133',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['131','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('137',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('139',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('145',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['143','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('149',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['148'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('150',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X33 ) @ X34 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X33 ) @ X35 )
      | ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['147','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('154',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['128','154'])).

thf('156',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['13','155'])).

thf('157',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['128','154'])).

thf('158',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('159',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','127'])).

thf('161',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('163',plain,
    ( ( sk_C != sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['128','154'])).

thf('166',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('167',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X1 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['49','117'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(condensation,[status(thm)],['172'])).

thf('174',plain,(
    zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['167','173'])).

thf('175',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['164','174'])).

thf('176',plain,(
    $false ),
    inference(demod,[status(thm)],['156','175'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1NokLXXWWm
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 45.94/46.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 45.94/46.18  % Solved by: fo/fo7.sh
% 45.94/46.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 45.94/46.18  % done 23791 iterations in 45.709s
% 45.94/46.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 45.94/46.18  % SZS output start Refutation
% 45.94/46.18  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 45.94/46.18  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 45.94/46.18  thf(sk_C_type, type, sk_C: $i).
% 45.94/46.18  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 45.94/46.18  thf(sk_B_type, type, sk_B: $i).
% 45.94/46.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 45.94/46.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 45.94/46.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 45.94/46.18  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 45.94/46.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 45.94/46.18  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 45.94/46.18  thf(sk_D_type, type, sk_D: $i).
% 45.94/46.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 45.94/46.18  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 45.94/46.18  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 45.94/46.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 45.94/46.18  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 45.94/46.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 45.94/46.18  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 45.94/46.18  thf(sk_A_type, type, sk_A: $i).
% 45.94/46.18  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 45.94/46.18  thf(t38_funct_2, conjecture,
% 45.94/46.18    (![A:$i,B:$i,C:$i,D:$i]:
% 45.94/46.18     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 45.94/46.18         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 45.94/46.18       ( ( r1_tarski @ C @ A ) =>
% 45.94/46.18         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 45.94/46.18           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 45.94/46.18             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 45.94/46.18             ( m1_subset_1 @
% 45.94/46.18               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 45.94/46.18               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 45.94/46.18  thf(zf_stmt_0, negated_conjecture,
% 45.94/46.18    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 45.94/46.18        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 45.94/46.18            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 45.94/46.18          ( ( r1_tarski @ C @ A ) =>
% 45.94/46.18            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 45.94/46.18              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 45.94/46.18                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 45.94/46.18                ( m1_subset_1 @
% 45.94/46.18                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 45.94/46.18                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 45.94/46.18    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 45.94/46.18  thf('0', plain,
% 45.94/46.18      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 45.94/46.18        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 45.94/46.18             sk_B)
% 45.94/46.18        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 45.94/46.18             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf('1', plain,
% 45.94/46.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf(dt_k2_partfun1, axiom,
% 45.94/46.18    (![A:$i,B:$i,C:$i,D:$i]:
% 45.94/46.18     ( ( ( v1_funct_1 @ C ) & 
% 45.94/46.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 45.94/46.18       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 45.94/46.18         ( m1_subset_1 @
% 45.94/46.18           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 45.94/46.18           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 45.94/46.18  thf('2', plain,
% 45.94/46.18      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 45.94/46.18         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 45.94/46.18          | ~ (v1_funct_1 @ X44)
% 45.94/46.18          | (v1_funct_1 @ (k2_partfun1 @ X45 @ X46 @ X44 @ X47)))),
% 45.94/46.18      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 45.94/46.18  thf('3', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 45.94/46.18          | ~ (v1_funct_1 @ sk_D))),
% 45.94/46.18      inference('sup-', [status(thm)], ['1', '2'])).
% 45.94/46.18  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf('5', plain,
% 45.94/46.18      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 45.94/46.18      inference('demod', [status(thm)], ['3', '4'])).
% 45.94/46.18  thf('6', plain,
% 45.94/46.18      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 45.94/46.18        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 45.94/46.18             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 45.94/46.18      inference('demod', [status(thm)], ['0', '5'])).
% 45.94/46.18  thf('7', plain,
% 45.94/46.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf(redefinition_k2_partfun1, axiom,
% 45.94/46.18    (![A:$i,B:$i,C:$i,D:$i]:
% 45.94/46.18     ( ( ( v1_funct_1 @ C ) & 
% 45.94/46.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 45.94/46.18       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 45.94/46.18  thf('8', plain,
% 45.94/46.18      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 45.94/46.18         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 45.94/46.18          | ~ (v1_funct_1 @ X48)
% 45.94/46.18          | ((k2_partfun1 @ X49 @ X50 @ X48 @ X51) = (k7_relat_1 @ X48 @ X51)))),
% 45.94/46.18      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 45.94/46.18  thf('9', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 45.94/46.18          | ~ (v1_funct_1 @ sk_D))),
% 45.94/46.18      inference('sup-', [status(thm)], ['7', '8'])).
% 45.94/46.18  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf('11', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 45.94/46.18      inference('demod', [status(thm)], ['9', '10'])).
% 45.94/46.18  thf('12', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 45.94/46.18      inference('demod', [status(thm)], ['9', '10'])).
% 45.94/46.18  thf('13', plain,
% 45.94/46.18      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 45.94/46.18        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 45.94/46.18             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 45.94/46.18      inference('demod', [status(thm)], ['6', '11', '12'])).
% 45.94/46.18  thf('14', plain, ((r1_tarski @ sk_C @ sk_A)),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf('15', plain,
% 45.94/46.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf(cc2_relset_1, axiom,
% 45.94/46.18    (![A:$i,B:$i,C:$i]:
% 45.94/46.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 45.94/46.18       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 45.94/46.18  thf('16', plain,
% 45.94/46.18      (![X27 : $i, X28 : $i, X29 : $i]:
% 45.94/46.18         ((v5_relat_1 @ X27 @ X29)
% 45.94/46.18          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 45.94/46.18      inference('cnf', [status(esa)], [cc2_relset_1])).
% 45.94/46.18  thf('17', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 45.94/46.18      inference('sup-', [status(thm)], ['15', '16'])).
% 45.94/46.18  thf(d19_relat_1, axiom,
% 45.94/46.18    (![A:$i,B:$i]:
% 45.94/46.18     ( ( v1_relat_1 @ B ) =>
% 45.94/46.18       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 45.94/46.18  thf('18', plain,
% 45.94/46.18      (![X14 : $i, X15 : $i]:
% 45.94/46.18         (~ (v5_relat_1 @ X14 @ X15)
% 45.94/46.18          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 45.94/46.18          | ~ (v1_relat_1 @ X14))),
% 45.94/46.18      inference('cnf', [status(esa)], [d19_relat_1])).
% 45.94/46.18  thf('19', plain,
% 45.94/46.18      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 45.94/46.18      inference('sup-', [status(thm)], ['17', '18'])).
% 45.94/46.18  thf('20', plain,
% 45.94/46.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf(cc1_relset_1, axiom,
% 45.94/46.18    (![A:$i,B:$i,C:$i]:
% 45.94/46.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 45.94/46.18       ( v1_relat_1 @ C ) ))).
% 45.94/46.18  thf('21', plain,
% 45.94/46.18      (![X24 : $i, X25 : $i, X26 : $i]:
% 45.94/46.18         ((v1_relat_1 @ X24)
% 45.94/46.18          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 45.94/46.18      inference('cnf', [status(esa)], [cc1_relset_1])).
% 45.94/46.18  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 45.94/46.18      inference('sup-', [status(thm)], ['20', '21'])).
% 45.94/46.18  thf('23', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 45.94/46.18      inference('demod', [status(thm)], ['19', '22'])).
% 45.94/46.18  thf(d1_funct_2, axiom,
% 45.94/46.18    (![A:$i,B:$i,C:$i]:
% 45.94/46.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 45.94/46.18       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 45.94/46.18           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 45.94/46.18             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 45.94/46.18         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 45.94/46.18           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 45.94/46.18             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 45.94/46.18  thf(zf_stmt_1, axiom,
% 45.94/46.18    (![B:$i,A:$i]:
% 45.94/46.18     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 45.94/46.18       ( zip_tseitin_0 @ B @ A ) ))).
% 45.94/46.18  thf('24', plain,
% 45.94/46.18      (![X36 : $i, X37 : $i]:
% 45.94/46.18         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 45.94/46.18  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 45.94/46.18  thf('25', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 45.94/46.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 45.94/46.18  thf('26', plain,
% 45.94/46.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.94/46.18         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 45.94/46.18      inference('sup+', [status(thm)], ['24', '25'])).
% 45.94/46.18  thf(d10_xboole_0, axiom,
% 45.94/46.18    (![A:$i,B:$i]:
% 45.94/46.18     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 45.94/46.18  thf('27', plain,
% 45.94/46.18      (![X0 : $i, X2 : $i]:
% 45.94/46.18         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 45.94/46.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 45.94/46.18  thf('28', plain,
% 45.94/46.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.94/46.18         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 45.94/46.18      inference('sup-', [status(thm)], ['26', '27'])).
% 45.94/46.18  thf('29', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (((k2_relat_1 @ sk_D) = (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 45.94/46.18      inference('sup-', [status(thm)], ['23', '28'])).
% 45.94/46.18  thf('30', plain,
% 45.94/46.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 45.94/46.18  thf(zf_stmt_3, axiom,
% 45.94/46.18    (![C:$i,B:$i,A:$i]:
% 45.94/46.18     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 45.94/46.18       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 45.94/46.18  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 45.94/46.18  thf(zf_stmt_5, axiom,
% 45.94/46.18    (![A:$i,B:$i,C:$i]:
% 45.94/46.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 45.94/46.18       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 45.94/46.18         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 45.94/46.18           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 45.94/46.18             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 45.94/46.18  thf('31', plain,
% 45.94/46.18      (![X41 : $i, X42 : $i, X43 : $i]:
% 45.94/46.18         (~ (zip_tseitin_0 @ X41 @ X42)
% 45.94/46.18          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 45.94/46.18          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_5])).
% 45.94/46.18  thf('32', plain,
% 45.94/46.18      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 45.94/46.18      inference('sup-', [status(thm)], ['30', '31'])).
% 45.94/46.18  thf('33', plain,
% 45.94/46.18      ((((k2_relat_1 @ sk_D) = (sk_B)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 45.94/46.18      inference('sup-', [status(thm)], ['29', '32'])).
% 45.94/46.18  thf('34', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf('35', plain,
% 45.94/46.18      (![X38 : $i, X39 : $i, X40 : $i]:
% 45.94/46.18         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 45.94/46.18          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 45.94/46.18          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 45.94/46.18  thf('36', plain,
% 45.94/46.18      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 45.94/46.18        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 45.94/46.18      inference('sup-', [status(thm)], ['34', '35'])).
% 45.94/46.18  thf('37', plain,
% 45.94/46.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf(redefinition_k1_relset_1, axiom,
% 45.94/46.18    (![A:$i,B:$i,C:$i]:
% 45.94/46.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 45.94/46.18       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 45.94/46.18  thf('38', plain,
% 45.94/46.18      (![X30 : $i, X31 : $i, X32 : $i]:
% 45.94/46.18         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 45.94/46.18          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 45.94/46.18      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 45.94/46.18  thf('39', plain,
% 45.94/46.18      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 45.94/46.18      inference('sup-', [status(thm)], ['37', '38'])).
% 45.94/46.18  thf('40', plain,
% 45.94/46.18      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 45.94/46.18      inference('demod', [status(thm)], ['36', '39'])).
% 45.94/46.18  thf('41', plain,
% 45.94/46.18      ((((k2_relat_1 @ sk_D) = (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 45.94/46.18      inference('sup-', [status(thm)], ['33', '40'])).
% 45.94/46.18  thf('42', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 45.94/46.18      inference('demod', [status(thm)], ['19', '22'])).
% 45.94/46.18  thf('43', plain,
% 45.94/46.18      (![X36 : $i, X37 : $i]:
% 45.94/46.18         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 45.94/46.18  thf(t3_xboole_1, axiom,
% 45.94/46.18    (![A:$i]:
% 45.94/46.18     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 45.94/46.18  thf('44', plain,
% 45.94/46.18      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 45.94/46.18      inference('cnf', [status(esa)], [t3_xboole_1])).
% 45.94/46.18  thf('45', plain,
% 45.94/46.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.94/46.18         (~ (r1_tarski @ X1 @ X0)
% 45.94/46.18          | (zip_tseitin_0 @ X0 @ X2)
% 45.94/46.18          | ((X1) = (k1_xboole_0)))),
% 45.94/46.18      inference('sup-', [status(thm)], ['43', '44'])).
% 45.94/46.18  thf('46', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B @ X0))),
% 45.94/46.18      inference('sup-', [status(thm)], ['42', '45'])).
% 45.94/46.18  thf('47', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (((sk_B) = (k1_xboole_0))
% 45.94/46.18          | ((sk_A) = (k1_relat_1 @ sk_D))
% 45.94/46.18          | (zip_tseitin_0 @ sk_B @ X0))),
% 45.94/46.18      inference('sup+', [status(thm)], ['41', '46'])).
% 45.94/46.18  thf('48', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf('49', plain,
% 45.94/46.18      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 45.94/46.18      inference('split', [status(esa)], ['48'])).
% 45.94/46.18  thf('50', plain,
% 45.94/46.18      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('split', [status(esa)], ['48'])).
% 45.94/46.18  thf('51', plain,
% 45.94/46.18      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 45.94/46.18        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 45.94/46.18             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 45.94/46.18      inference('demod', [status(thm)], ['0', '5'])).
% 45.94/46.18  thf('52', plain,
% 45.94/46.18      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 45.94/46.18            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 45.94/46.18         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 45.94/46.18              sk_B)))
% 45.94/46.18         <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('sup-', [status(thm)], ['50', '51'])).
% 45.94/46.18  thf('53', plain,
% 45.94/46.18      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('split', [status(esa)], ['48'])).
% 45.94/46.18  thf('54', plain,
% 45.94/46.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf('55', plain,
% 45.94/46.18      (((m1_subset_1 @ sk_D @ 
% 45.94/46.18         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 45.94/46.18         <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('sup+', [status(thm)], ['53', '54'])).
% 45.94/46.18  thf(t113_zfmisc_1, axiom,
% 45.94/46.18    (![A:$i,B:$i]:
% 45.94/46.18     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 45.94/46.18       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 45.94/46.18  thf('56', plain,
% 45.94/46.18      (![X9 : $i, X10 : $i]:
% 45.94/46.18         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 45.94/46.18      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 45.94/46.18  thf('57', plain,
% 45.94/46.18      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 45.94/46.18      inference('simplify', [status(thm)], ['56'])).
% 45.94/46.18  thf('58', plain,
% 45.94/46.18      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 45.94/46.18         <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('demod', [status(thm)], ['55', '57'])).
% 45.94/46.18  thf(t3_subset, axiom,
% 45.94/46.18    (![A:$i,B:$i]:
% 45.94/46.18     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 45.94/46.18  thf('59', plain,
% 45.94/46.18      (![X11 : $i, X12 : $i]:
% 45.94/46.18         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 45.94/46.18      inference('cnf', [status(esa)], [t3_subset])).
% 45.94/46.18  thf('60', plain,
% 45.94/46.18      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('sup-', [status(thm)], ['58', '59'])).
% 45.94/46.18  thf('61', plain,
% 45.94/46.18      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 45.94/46.18      inference('cnf', [status(esa)], [t3_xboole_1])).
% 45.94/46.18  thf('62', plain,
% 45.94/46.18      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('sup-', [status(thm)], ['60', '61'])).
% 45.94/46.18  thf('63', plain,
% 45.94/46.18      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('split', [status(esa)], ['48'])).
% 45.94/46.18  thf('64', plain, ((r1_tarski @ sk_C @ sk_A)),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf('65', plain,
% 45.94/46.18      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('sup+', [status(thm)], ['63', '64'])).
% 45.94/46.18  thf('66', plain,
% 45.94/46.18      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 45.94/46.18      inference('cnf', [status(esa)], [t3_xboole_1])).
% 45.94/46.18  thf('67', plain,
% 45.94/46.18      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('sup-', [status(thm)], ['65', '66'])).
% 45.94/46.18  thf('68', plain,
% 45.94/46.18      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('sup-', [status(thm)], ['65', '66'])).
% 45.94/46.18  thf('69', plain,
% 45.94/46.18      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 45.94/46.18      inference('simplify', [status(thm)], ['56'])).
% 45.94/46.18  thf('70', plain,
% 45.94/46.18      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('split', [status(esa)], ['48'])).
% 45.94/46.18  thf('71', plain,
% 45.94/46.18      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('sup-', [status(thm)], ['60', '61'])).
% 45.94/46.18  thf('72', plain,
% 45.94/46.18      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('sup-', [status(thm)], ['65', '66'])).
% 45.94/46.18  thf('73', plain,
% 45.94/46.18      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('sup-', [status(thm)], ['65', '66'])).
% 45.94/46.18  thf('74', plain,
% 45.94/46.18      (((~ (m1_subset_1 @ 
% 45.94/46.18            (k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0) @ 
% 45.94/46.18            (k1_zfmisc_1 @ k1_xboole_0))
% 45.94/46.18         | ~ (v1_funct_2 @ 
% 45.94/46.18              (k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0) @ 
% 45.94/46.18              k1_xboole_0 @ sk_B)))
% 45.94/46.18         <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('demod', [status(thm)],
% 45.94/46.18                ['52', '62', '67', '68', '69', '70', '71', '72', '73'])).
% 45.94/46.18  thf('75', plain,
% 45.94/46.18      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('sup-', [status(thm)], ['60', '61'])).
% 45.94/46.18  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf('77', plain,
% 45.94/46.18      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('sup+', [status(thm)], ['75', '76'])).
% 45.94/46.18  thf('78', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 45.94/46.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 45.94/46.18  thf('79', plain,
% 45.94/46.18      (![X11 : $i, X13 : $i]:
% 45.94/46.18         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 45.94/46.18      inference('cnf', [status(esa)], [t3_subset])).
% 45.94/46.18  thf('80', plain,
% 45.94/46.18      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 45.94/46.18      inference('sup-', [status(thm)], ['78', '79'])).
% 45.94/46.18  thf('81', plain,
% 45.94/46.18      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 45.94/46.18         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 45.94/46.18          | ~ (v1_funct_1 @ X48)
% 45.94/46.18          | ((k2_partfun1 @ X49 @ X50 @ X48 @ X51) = (k7_relat_1 @ X48 @ X51)))),
% 45.94/46.18      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 45.94/46.18  thf('82', plain,
% 45.94/46.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.94/46.18         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 45.94/46.18            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 45.94/46.18          | ~ (v1_funct_1 @ k1_xboole_0))),
% 45.94/46.18      inference('sup-', [status(thm)], ['80', '81'])).
% 45.94/46.18  thf(t88_relat_1, axiom,
% 45.94/46.18    (![A:$i,B:$i]:
% 45.94/46.18     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 45.94/46.18  thf('83', plain,
% 45.94/46.18      (![X20 : $i, X21 : $i]:
% 45.94/46.18         ((r1_tarski @ (k7_relat_1 @ X20 @ X21) @ X20) | ~ (v1_relat_1 @ X20))),
% 45.94/46.18      inference('cnf', [status(esa)], [t88_relat_1])).
% 45.94/46.18  thf('84', plain,
% 45.94/46.18      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 45.94/46.18      inference('cnf', [status(esa)], [t3_xboole_1])).
% 45.94/46.18  thf('85', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (~ (v1_relat_1 @ k1_xboole_0)
% 45.94/46.18          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 45.94/46.18      inference('sup-', [status(thm)], ['83', '84'])).
% 45.94/46.18  thf('86', plain,
% 45.94/46.18      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 45.94/46.18      inference('simplify', [status(thm)], ['56'])).
% 45.94/46.18  thf(fc6_relat_1, axiom,
% 45.94/46.18    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 45.94/46.18  thf('87', plain,
% 45.94/46.18      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 45.94/46.18      inference('cnf', [status(esa)], [fc6_relat_1])).
% 45.94/46.18  thf('88', plain, ((v1_relat_1 @ k1_xboole_0)),
% 45.94/46.18      inference('sup+', [status(thm)], ['86', '87'])).
% 45.94/46.18  thf('89', plain,
% 45.94/46.18      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 45.94/46.18      inference('demod', [status(thm)], ['85', '88'])).
% 45.94/46.18  thf('90', plain,
% 45.94/46.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.94/46.18         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 45.94/46.18          | ~ (v1_funct_1 @ k1_xboole_0))),
% 45.94/46.18      inference('demod', [status(thm)], ['82', '89'])).
% 45.94/46.18  thf('91', plain,
% 45.94/46.18      ((![X0 : $i, X1 : $i, X2 : $i]:
% 45.94/46.18          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 45.94/46.18         <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('sup-', [status(thm)], ['77', '90'])).
% 45.94/46.18  thf('92', plain,
% 45.94/46.18      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 45.94/46.18      inference('sup-', [status(thm)], ['78', '79'])).
% 45.94/46.18  thf('93', plain,
% 45.94/46.18      ((![X0 : $i, X1 : $i, X2 : $i]:
% 45.94/46.18          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 45.94/46.18         <= ((((sk_A) = (k1_xboole_0))))),
% 45.94/46.18      inference('sup-', [status(thm)], ['77', '90'])).
% 45.94/46.18  thf('94', plain,
% 45.94/46.18      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 45.94/46.18      inference('sup-', [status(thm)], ['78', '79'])).
% 45.94/46.18  thf('95', plain,
% 45.94/46.18      (![X30 : $i, X31 : $i, X32 : $i]:
% 45.94/46.18         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 45.94/46.18          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 45.94/46.18      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 45.94/46.18  thf('96', plain,
% 45.94/46.18      (![X0 : $i, X1 : $i]:
% 45.94/46.18         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 45.94/46.18      inference('sup-', [status(thm)], ['94', '95'])).
% 45.94/46.18  thf('97', plain,
% 45.94/46.18      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 45.94/46.18      inference('demod', [status(thm)], ['85', '88'])).
% 45.94/46.18  thf('98', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 45.94/46.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 45.94/46.18  thf(t91_relat_1, axiom,
% 45.94/46.18    (![A:$i,B:$i]:
% 45.94/46.18     ( ( v1_relat_1 @ B ) =>
% 45.94/46.18       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 45.94/46.18         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 45.94/46.18  thf('99', plain,
% 45.94/46.18      (![X22 : $i, X23 : $i]:
% 45.94/46.18         (~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 45.94/46.18          | ((k1_relat_1 @ (k7_relat_1 @ X23 @ X22)) = (X22))
% 45.94/46.18          | ~ (v1_relat_1 @ X23))),
% 45.94/46.18      inference('cnf', [status(esa)], [t91_relat_1])).
% 45.94/46.18  thf('100', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (~ (v1_relat_1 @ X0)
% 45.94/46.18          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 45.94/46.18      inference('sup-', [status(thm)], ['98', '99'])).
% 45.94/46.18  thf('101', plain,
% 45.94/46.18      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 45.94/46.18        | ~ (v1_relat_1 @ k1_xboole_0))),
% 45.94/46.18      inference('sup+', [status(thm)], ['97', '100'])).
% 45.94/46.18  thf('102', plain, ((v1_relat_1 @ k1_xboole_0)),
% 45.94/46.18      inference('sup+', [status(thm)], ['86', '87'])).
% 45.94/46.18  thf('103', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 45.94/46.18      inference('demod', [status(thm)], ['101', '102'])).
% 45.94/46.18  thf('104', plain,
% 45.94/46.18      (![X0 : $i, X1 : $i]:
% 45.94/46.18         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 45.94/46.18      inference('demod', [status(thm)], ['96', '103'])).
% 45.94/46.18  thf('105', plain,
% 45.94/46.18      (![X38 : $i, X39 : $i, X40 : $i]:
% 45.94/46.18         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 45.94/46.18          | (v1_funct_2 @ X40 @ X38 @ X39)
% 45.94/46.18          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 45.94/46.18  thf('106', plain,
% 45.94/46.18      (![X0 : $i, X1 : $i]:
% 45.94/46.18         (((X1) != (k1_xboole_0))
% 45.94/46.18          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 45.94/46.18          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 45.94/46.18      inference('sup-', [status(thm)], ['104', '105'])).
% 45.94/46.18  thf('107', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 45.94/46.18          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 45.94/46.18      inference('simplify', [status(thm)], ['106'])).
% 45.94/46.18  thf('108', plain,
% 45.94/46.18      (![X36 : $i, X37 : $i]:
% 45.94/46.18         ((zip_tseitin_0 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 45.94/46.18  thf('109', plain, (![X36 : $i]: (zip_tseitin_0 @ X36 @ k1_xboole_0)),
% 45.94/46.18      inference('simplify', [status(thm)], ['108'])).
% 45.94/46.18  thf('110', plain,
% 45.94/46.18      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 45.94/46.18      inference('sup-', [status(thm)], ['78', '79'])).
% 45.94/46.18  thf('111', plain,
% 45.94/46.18      (![X41 : $i, X42 : $i, X43 : $i]:
% 45.94/46.18         (~ (zip_tseitin_0 @ X41 @ X42)
% 45.94/46.18          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 45.94/46.18          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_5])).
% 45.94/46.18  thf('112', plain,
% 45.94/46.18      (![X0 : $i, X1 : $i]:
% 45.94/46.18         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 45.94/46.18      inference('sup-', [status(thm)], ['110', '111'])).
% 45.94/46.18  thf('113', plain,
% 45.94/46.18      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 45.94/46.18      inference('sup-', [status(thm)], ['109', '112'])).
% 45.94/46.18  thf('114', plain,
% 45.94/46.18      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 45.94/46.18      inference('demod', [status(thm)], ['107', '113'])).
% 45.94/46.18  thf('115', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 45.94/46.18      inference('demod', [status(thm)], ['74', '91', '92', '93', '114'])).
% 45.94/46.18  thf('116', plain,
% 45.94/46.18      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 45.94/46.18      inference('split', [status(esa)], ['48'])).
% 45.94/46.18  thf('117', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 45.94/46.18      inference('sat_resolution*', [status(thm)], ['115', '116'])).
% 45.94/46.18  thf('118', plain, (((sk_B) != (k1_xboole_0))),
% 45.94/46.18      inference('simpl_trail', [status(thm)], ['49', '117'])).
% 45.94/46.18  thf('119', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ sk_B @ X0))),
% 45.94/46.18      inference('simplify_reflect-', [status(thm)], ['47', '118'])).
% 45.94/46.18  thf('120', plain,
% 45.94/46.18      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 45.94/46.18      inference('sup-', [status(thm)], ['30', '31'])).
% 45.94/46.18  thf('121', plain,
% 45.94/46.18      ((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 45.94/46.18      inference('sup-', [status(thm)], ['119', '120'])).
% 45.94/46.18  thf('122', plain,
% 45.94/46.18      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 45.94/46.18      inference('demod', [status(thm)], ['36', '39'])).
% 45.94/46.18  thf('123', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 45.94/46.18      inference('clc', [status(thm)], ['121', '122'])).
% 45.94/46.18  thf('124', plain,
% 45.94/46.18      (![X22 : $i, X23 : $i]:
% 45.94/46.18         (~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 45.94/46.18          | ((k1_relat_1 @ (k7_relat_1 @ X23 @ X22)) = (X22))
% 45.94/46.18          | ~ (v1_relat_1 @ X23))),
% 45.94/46.18      inference('cnf', [status(esa)], [t91_relat_1])).
% 45.94/46.18  thf('125', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (~ (r1_tarski @ X0 @ sk_A)
% 45.94/46.18          | ~ (v1_relat_1 @ sk_D)
% 45.94/46.18          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 45.94/46.18      inference('sup-', [status(thm)], ['123', '124'])).
% 45.94/46.18  thf('126', plain, ((v1_relat_1 @ sk_D)),
% 45.94/46.18      inference('sup-', [status(thm)], ['20', '21'])).
% 45.94/46.18  thf('127', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (~ (r1_tarski @ X0 @ sk_A)
% 45.94/46.18          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 45.94/46.18      inference('demod', [status(thm)], ['125', '126'])).
% 45.94/46.18  thf('128', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 45.94/46.18      inference('sup-', [status(thm)], ['14', '127'])).
% 45.94/46.18  thf('129', plain,
% 45.94/46.18      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.94/46.18  thf('130', plain,
% 45.94/46.18      (![X11 : $i, X12 : $i]:
% 45.94/46.18         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 45.94/46.18      inference('cnf', [status(esa)], [t3_subset])).
% 45.94/46.18  thf('131', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 45.94/46.18      inference('sup-', [status(thm)], ['129', '130'])).
% 45.94/46.18  thf('132', plain,
% 45.94/46.18      (![X20 : $i, X21 : $i]:
% 45.94/46.18         ((r1_tarski @ (k7_relat_1 @ X20 @ X21) @ X20) | ~ (v1_relat_1 @ X20))),
% 45.94/46.18      inference('cnf', [status(esa)], [t88_relat_1])).
% 45.94/46.18  thf(t1_xboole_1, axiom,
% 45.94/46.18    (![A:$i,B:$i,C:$i]:
% 45.94/46.18     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 45.94/46.18       ( r1_tarski @ A @ C ) ))).
% 45.94/46.18  thf('133', plain,
% 45.94/46.18      (![X3 : $i, X4 : $i, X5 : $i]:
% 45.94/46.18         (~ (r1_tarski @ X3 @ X4)
% 45.94/46.18          | ~ (r1_tarski @ X4 @ X5)
% 45.94/46.18          | (r1_tarski @ X3 @ X5))),
% 45.94/46.18      inference('cnf', [status(esa)], [t1_xboole_1])).
% 45.94/46.18  thf('134', plain,
% 45.94/46.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.94/46.18         (~ (v1_relat_1 @ X0)
% 45.94/46.18          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 45.94/46.18          | ~ (r1_tarski @ X0 @ X2))),
% 45.94/46.18      inference('sup-', [status(thm)], ['132', '133'])).
% 45.94/46.18  thf('135', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 45.94/46.18          | ~ (v1_relat_1 @ sk_D))),
% 45.94/46.18      inference('sup-', [status(thm)], ['131', '134'])).
% 45.94/46.18  thf('136', plain, ((v1_relat_1 @ sk_D)),
% 45.94/46.18      inference('sup-', [status(thm)], ['20', '21'])).
% 45.94/46.18  thf('137', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 45.94/46.18      inference('demod', [status(thm)], ['135', '136'])).
% 45.94/46.18  thf('138', plain,
% 45.94/46.18      (![X11 : $i, X13 : $i]:
% 45.94/46.18         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 45.94/46.18      inference('cnf', [status(esa)], [t3_subset])).
% 45.94/46.18  thf('139', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 45.94/46.18          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 45.94/46.18      inference('sup-', [status(thm)], ['137', '138'])).
% 45.94/46.18  thf('140', plain,
% 45.94/46.18      (![X27 : $i, X28 : $i, X29 : $i]:
% 45.94/46.18         ((v5_relat_1 @ X27 @ X29)
% 45.94/46.18          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 45.94/46.18      inference('cnf', [status(esa)], [cc2_relset_1])).
% 45.94/46.18  thf('141', plain,
% 45.94/46.18      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 45.94/46.18      inference('sup-', [status(thm)], ['139', '140'])).
% 45.94/46.18  thf('142', plain,
% 45.94/46.18      (![X14 : $i, X15 : $i]:
% 45.94/46.18         (~ (v5_relat_1 @ X14 @ X15)
% 45.94/46.18          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 45.94/46.18          | ~ (v1_relat_1 @ X14))),
% 45.94/46.18      inference('cnf', [status(esa)], [d19_relat_1])).
% 45.94/46.18  thf('143', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 45.94/46.18          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 45.94/46.18      inference('sup-', [status(thm)], ['141', '142'])).
% 45.94/46.18  thf('144', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 45.94/46.18          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 45.94/46.18      inference('sup-', [status(thm)], ['137', '138'])).
% 45.94/46.18  thf('145', plain,
% 45.94/46.18      (![X24 : $i, X25 : $i, X26 : $i]:
% 45.94/46.18         ((v1_relat_1 @ X24)
% 45.94/46.18          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 45.94/46.18      inference('cnf', [status(esa)], [cc1_relset_1])).
% 45.94/46.18  thf('146', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 45.94/46.18      inference('sup-', [status(thm)], ['144', '145'])).
% 45.94/46.18  thf('147', plain,
% 45.94/46.18      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 45.94/46.18      inference('demod', [status(thm)], ['143', '146'])).
% 45.94/46.18  thf('148', plain,
% 45.94/46.18      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 45.94/46.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 45.94/46.18  thf('149', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 45.94/46.18      inference('simplify', [status(thm)], ['148'])).
% 45.94/46.18  thf(t11_relset_1, axiom,
% 45.94/46.18    (![A:$i,B:$i,C:$i]:
% 45.94/46.18     ( ( v1_relat_1 @ C ) =>
% 45.94/46.18       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 45.94/46.18           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 45.94/46.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 45.94/46.18  thf('150', plain,
% 45.94/46.18      (![X33 : $i, X34 : $i, X35 : $i]:
% 45.94/46.18         (~ (r1_tarski @ (k1_relat_1 @ X33) @ X34)
% 45.94/46.18          | ~ (r1_tarski @ (k2_relat_1 @ X33) @ X35)
% 45.94/46.18          | (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 45.94/46.18          | ~ (v1_relat_1 @ X33))),
% 45.94/46.18      inference('cnf', [status(esa)], [t11_relset_1])).
% 45.94/46.18  thf('151', plain,
% 45.94/46.18      (![X0 : $i, X1 : $i]:
% 45.94/46.18         (~ (v1_relat_1 @ X0)
% 45.94/46.18          | (m1_subset_1 @ X0 @ 
% 45.94/46.18             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 45.94/46.18          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 45.94/46.18      inference('sup-', [status(thm)], ['149', '150'])).
% 45.94/46.18  thf('152', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 45.94/46.18           (k1_zfmisc_1 @ 
% 45.94/46.18            (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))
% 45.94/46.18          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 45.94/46.18      inference('sup-', [status(thm)], ['147', '151'])).
% 45.94/46.18  thf('153', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 45.94/46.18      inference('sup-', [status(thm)], ['144', '145'])).
% 45.94/46.18  thf('154', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 45.94/46.18          (k1_zfmisc_1 @ 
% 45.94/46.18           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 45.94/46.18      inference('demod', [status(thm)], ['152', '153'])).
% 45.94/46.18  thf('155', plain,
% 45.94/46.18      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 45.94/46.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 45.94/46.18      inference('sup+', [status(thm)], ['128', '154'])).
% 45.94/46.18  thf('156', plain,
% 45.94/46.18      (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 45.94/46.18      inference('demod', [status(thm)], ['13', '155'])).
% 45.94/46.18  thf('157', plain,
% 45.94/46.18      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 45.94/46.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 45.94/46.18      inference('sup+', [status(thm)], ['128', '154'])).
% 45.94/46.18  thf('158', plain,
% 45.94/46.18      (![X30 : $i, X31 : $i, X32 : $i]:
% 45.94/46.18         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 45.94/46.18          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 45.94/46.18      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 45.94/46.18  thf('159', plain,
% 45.94/46.18      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C))
% 45.94/46.18         = (k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)))),
% 45.94/46.18      inference('sup-', [status(thm)], ['157', '158'])).
% 45.94/46.18  thf('160', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 45.94/46.18      inference('sup-', [status(thm)], ['14', '127'])).
% 45.94/46.18  thf('161', plain,
% 45.94/46.18      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 45.94/46.18      inference('demod', [status(thm)], ['159', '160'])).
% 45.94/46.18  thf('162', plain,
% 45.94/46.18      (![X38 : $i, X39 : $i, X40 : $i]:
% 45.94/46.18         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 45.94/46.18          | (v1_funct_2 @ X40 @ X38 @ X39)
% 45.94/46.18          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 45.94/46.18  thf('163', plain,
% 45.94/46.18      ((((sk_C) != (sk_C))
% 45.94/46.18        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 45.94/46.18        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 45.94/46.18      inference('sup-', [status(thm)], ['161', '162'])).
% 45.94/46.18  thf('164', plain,
% 45.94/46.18      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 45.94/46.18        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C))),
% 45.94/46.18      inference('simplify', [status(thm)], ['163'])).
% 45.94/46.18  thf('165', plain,
% 45.94/46.18      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 45.94/46.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 45.94/46.18      inference('sup+', [status(thm)], ['128', '154'])).
% 45.94/46.18  thf('166', plain,
% 45.94/46.18      (![X41 : $i, X42 : $i, X43 : $i]:
% 45.94/46.18         (~ (zip_tseitin_0 @ X41 @ X42)
% 45.94/46.18          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 45.94/46.18          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 45.94/46.18      inference('cnf', [status(esa)], [zf_stmt_5])).
% 45.94/46.18  thf('167', plain,
% 45.94/46.18      (((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 45.94/46.18        | ~ (zip_tseitin_0 @ sk_B @ sk_C))),
% 45.94/46.18      inference('sup-', [status(thm)], ['165', '166'])).
% 45.94/46.18  thf('168', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B @ X0))),
% 45.94/46.18      inference('sup-', [status(thm)], ['42', '45'])).
% 45.94/46.18  thf('169', plain,
% 45.94/46.18      (![X0 : $i]:
% 45.94/46.18         (((k2_relat_1 @ sk_D) = (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 45.94/46.18      inference('sup-', [status(thm)], ['23', '28'])).
% 45.94/46.18  thf('170', plain,
% 45.94/46.18      (![X0 : $i, X1 : $i]:
% 45.94/46.18         (((k1_xboole_0) = (sk_B))
% 45.94/46.18          | (zip_tseitin_0 @ sk_B @ X1)
% 45.94/46.18          | (zip_tseitin_0 @ sk_B @ X0))),
% 45.94/46.18      inference('sup+', [status(thm)], ['168', '169'])).
% 45.94/46.18  thf('171', plain, (((sk_B) != (k1_xboole_0))),
% 45.94/46.18      inference('simpl_trail', [status(thm)], ['49', '117'])).
% 45.94/46.18  thf('172', plain,
% 45.94/46.18      (![X0 : $i, X1 : $i]:
% 45.94/46.18         ((zip_tseitin_0 @ sk_B @ X1) | (zip_tseitin_0 @ sk_B @ X0))),
% 45.94/46.18      inference('simplify_reflect-', [status(thm)], ['170', '171'])).
% 45.94/46.18  thf('173', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 45.94/46.18      inference('condensation', [status(thm)], ['172'])).
% 45.94/46.18  thf('174', plain,
% 45.94/46.18      ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)),
% 45.94/46.18      inference('demod', [status(thm)], ['167', '173'])).
% 45.94/46.18  thf('175', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 45.94/46.18      inference('demod', [status(thm)], ['164', '174'])).
% 45.94/46.18  thf('176', plain, ($false), inference('demod', [status(thm)], ['156', '175'])).
% 45.94/46.18  
% 45.94/46.18  % SZS output end Refutation
% 45.94/46.18  
% 45.94/46.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
