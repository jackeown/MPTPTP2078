%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H166Ub2JJK

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:36 EST 2020

% Result     : Timeout 59.44s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  209 ( 943 expanded)
%              Number of leaves         :   44 ( 294 expanded)
%              Depth                    :   20
%              Number of atoms          : 1571 (15528 expanded)
%              Number of equality atoms :  118 ( 858 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v5_relat_1 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( v5_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
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

thf('44',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','48'])).

thf('50',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('53',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('54',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('55',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('56',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('66',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('68',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
      | ( k1_xboole_0 = sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('73',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('74',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('75',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ( ( k2_partfun1 @ X49 @ X50 @ X48 @ X51 )
        = ( k7_relat_1 @ X48 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('78',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v4_relat_1 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('79',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('80',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('83',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('84',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_funct_1 @ B ) ) ) )).

thf('88',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc3_funct_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('92',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','85','92'])).

thf('94',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('95',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('96',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('97',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('98',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('99',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','85','92'])).

thf('101',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('102',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('103',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('105',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('111',plain,(
    ! [X36: $i] :
      ( zip_tseitin_0 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('113',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['109','115'])).

thf('117',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['54','66','73','93','94','95','96','97','98','99','100','101','116'])).

thf('118',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('119',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['117','118'])).

thf('120',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['51','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','120'])).

thf('122',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('123',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('125',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['123','124'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('126',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X45 @ X46 @ X44 @ X47 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('137',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v5_relat_1 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v5_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('143',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['141','144'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('146',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X52 ) @ X53 )
      | ( v1_funct_2 @ X52 @ ( k1_relat_1 @ X52 ) @ X53 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('149',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('151',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['147','148','151'])).

thf('153',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['130','152'])).

thf('154',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','153'])).

thf('155',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','129'])).

thf('156',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['141','144'])).

thf('157',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X52 ) @ X53 )
      | ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X52 ) @ X53 ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('160',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('161',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['155','161'])).

thf('163',plain,(
    $false ),
    inference(demod,[status(thm)],['154','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H166Ub2JJK
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 59.44/59.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 59.44/59.62  % Solved by: fo/fo7.sh
% 59.44/59.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 59.44/59.62  % done 29944 iterations in 59.147s
% 59.44/59.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 59.44/59.62  % SZS output start Refutation
% 59.44/59.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 59.44/59.62  thf(sk_D_type, type, sk_D: $i).
% 59.44/59.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 59.44/59.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 59.44/59.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 59.44/59.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 59.44/59.62  thf(sk_B_type, type, sk_B: $i).
% 59.44/59.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 59.44/59.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 59.44/59.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 59.44/59.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 59.44/59.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 59.44/59.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 59.44/59.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 59.44/59.62  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 59.44/59.63  thf(sk_A_type, type, sk_A: $i).
% 59.44/59.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 59.44/59.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 59.44/59.63  thf(sk_C_type, type, sk_C: $i).
% 59.44/59.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 59.44/59.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 59.44/59.63  thf(t38_funct_2, conjecture,
% 59.44/59.63    (![A:$i,B:$i,C:$i,D:$i]:
% 59.44/59.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 59.44/59.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 59.44/59.63       ( ( r1_tarski @ C @ A ) =>
% 59.44/59.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 59.44/59.63           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 59.44/59.63             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 59.44/59.63             ( m1_subset_1 @
% 59.44/59.63               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 59.44/59.63               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 59.44/59.63  thf(zf_stmt_0, negated_conjecture,
% 59.44/59.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 59.44/59.63        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 59.44/59.63            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 59.44/59.63          ( ( r1_tarski @ C @ A ) =>
% 59.44/59.63            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 59.44/59.63              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 59.44/59.63                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 59.44/59.63                ( m1_subset_1 @
% 59.44/59.63                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 59.44/59.63                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 59.44/59.63    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 59.44/59.63  thf('0', plain,
% 59.44/59.63      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 59.44/59.63        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 59.44/59.63             sk_B)
% 59.44/59.63        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 59.44/59.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf('1', plain,
% 59.44/59.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf(dt_k2_partfun1, axiom,
% 59.44/59.63    (![A:$i,B:$i,C:$i,D:$i]:
% 59.44/59.63     ( ( ( v1_funct_1 @ C ) & 
% 59.44/59.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 59.44/59.63       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 59.44/59.63         ( m1_subset_1 @
% 59.44/59.63           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 59.44/59.63           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 59.44/59.63  thf('2', plain,
% 59.44/59.63      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 59.44/59.63         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 59.44/59.63          | ~ (v1_funct_1 @ X44)
% 59.44/59.63          | (v1_funct_1 @ (k2_partfun1 @ X45 @ X46 @ X44 @ X47)))),
% 59.44/59.63      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 59.44/59.63  thf('3', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 59.44/59.63          | ~ (v1_funct_1 @ sk_D))),
% 59.44/59.63      inference('sup-', [status(thm)], ['1', '2'])).
% 59.44/59.63  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf('5', plain,
% 59.44/59.63      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 59.44/59.63      inference('demod', [status(thm)], ['3', '4'])).
% 59.44/59.63  thf('6', plain,
% 59.44/59.63      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 59.44/59.63        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 59.44/59.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 59.44/59.63      inference('demod', [status(thm)], ['0', '5'])).
% 59.44/59.63  thf('7', plain,
% 59.44/59.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf(redefinition_k2_partfun1, axiom,
% 59.44/59.63    (![A:$i,B:$i,C:$i,D:$i]:
% 59.44/59.63     ( ( ( v1_funct_1 @ C ) & 
% 59.44/59.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 59.44/59.63       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 59.44/59.63  thf('8', plain,
% 59.44/59.63      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 59.44/59.63         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 59.44/59.63          | ~ (v1_funct_1 @ X48)
% 59.44/59.63          | ((k2_partfun1 @ X49 @ X50 @ X48 @ X51) = (k7_relat_1 @ X48 @ X51)))),
% 59.44/59.63      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 59.44/59.63  thf('9', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 59.44/59.63          | ~ (v1_funct_1 @ sk_D))),
% 59.44/59.63      inference('sup-', [status(thm)], ['7', '8'])).
% 59.44/59.63  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf('11', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 59.44/59.63      inference('demod', [status(thm)], ['9', '10'])).
% 59.44/59.63  thf('12', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 59.44/59.63      inference('demod', [status(thm)], ['9', '10'])).
% 59.44/59.63  thf('13', plain,
% 59.44/59.63      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 59.44/59.63        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 59.44/59.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 59.44/59.63      inference('demod', [status(thm)], ['6', '11', '12'])).
% 59.44/59.63  thf('14', plain, ((r1_tarski @ sk_C @ sk_A)),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf('15', plain,
% 59.44/59.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf(cc2_relset_1, axiom,
% 59.44/59.63    (![A:$i,B:$i,C:$i]:
% 59.44/59.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 59.44/59.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 59.44/59.63  thf('16', plain,
% 59.44/59.63      (![X30 : $i, X31 : $i, X32 : $i]:
% 59.44/59.63         ((v5_relat_1 @ X30 @ X32)
% 59.44/59.63          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 59.44/59.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 59.44/59.63  thf('17', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 59.44/59.63      inference('sup-', [status(thm)], ['15', '16'])).
% 59.44/59.63  thf(d19_relat_1, axiom,
% 59.44/59.63    (![A:$i,B:$i]:
% 59.44/59.63     ( ( v1_relat_1 @ B ) =>
% 59.44/59.63       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 59.44/59.63  thf('18', plain,
% 59.44/59.63      (![X17 : $i, X18 : $i]:
% 59.44/59.63         (~ (v5_relat_1 @ X17 @ X18)
% 59.44/59.63          | (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 59.44/59.63          | ~ (v1_relat_1 @ X17))),
% 59.44/59.63      inference('cnf', [status(esa)], [d19_relat_1])).
% 59.44/59.63  thf('19', plain,
% 59.44/59.63      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 59.44/59.63      inference('sup-', [status(thm)], ['17', '18'])).
% 59.44/59.63  thf('20', plain,
% 59.44/59.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf(cc1_relset_1, axiom,
% 59.44/59.63    (![A:$i,B:$i,C:$i]:
% 59.44/59.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 59.44/59.63       ( v1_relat_1 @ C ) ))).
% 59.44/59.63  thf('21', plain,
% 59.44/59.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 59.44/59.63         ((v1_relat_1 @ X27)
% 59.44/59.63          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 59.44/59.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 59.44/59.63  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 59.44/59.63      inference('sup-', [status(thm)], ['20', '21'])).
% 59.44/59.63  thf('23', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 59.44/59.63      inference('demod', [status(thm)], ['19', '22'])).
% 59.44/59.63  thf(d1_funct_2, axiom,
% 59.44/59.63    (![A:$i,B:$i,C:$i]:
% 59.44/59.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 59.44/59.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 59.44/59.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 59.44/59.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 59.44/59.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 59.44/59.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 59.44/59.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 59.44/59.63  thf(zf_stmt_1, axiom,
% 59.44/59.63    (![B:$i,A:$i]:
% 59.44/59.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 59.44/59.63       ( zip_tseitin_0 @ B @ A ) ))).
% 59.44/59.63  thf('24', plain,
% 59.44/59.63      (![X36 : $i, X37 : $i]:
% 59.44/59.63         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 59.44/59.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 59.44/59.63  thf('25', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 59.44/59.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 59.44/59.63  thf('26', plain,
% 59.44/59.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.44/59.63         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 59.44/59.63      inference('sup+', [status(thm)], ['24', '25'])).
% 59.44/59.63  thf(d10_xboole_0, axiom,
% 59.44/59.63    (![A:$i,B:$i]:
% 59.44/59.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 59.44/59.63  thf('27', plain,
% 59.44/59.63      (![X0 : $i, X2 : $i]:
% 59.44/59.63         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 59.44/59.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 59.44/59.63  thf('28', plain,
% 59.44/59.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.44/59.63         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 59.44/59.63      inference('sup-', [status(thm)], ['26', '27'])).
% 59.44/59.63  thf('29', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (((k2_relat_1 @ sk_D) = (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 59.44/59.63      inference('sup-', [status(thm)], ['23', '28'])).
% 59.44/59.63  thf('30', plain,
% 59.44/59.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 59.44/59.63  thf(zf_stmt_3, axiom,
% 59.44/59.63    (![C:$i,B:$i,A:$i]:
% 59.44/59.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 59.44/59.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 59.44/59.63  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 59.44/59.63  thf(zf_stmt_5, axiom,
% 59.44/59.63    (![A:$i,B:$i,C:$i]:
% 59.44/59.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 59.44/59.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 59.44/59.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 59.44/59.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 59.44/59.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 59.44/59.63  thf('31', plain,
% 59.44/59.63      (![X41 : $i, X42 : $i, X43 : $i]:
% 59.44/59.63         (~ (zip_tseitin_0 @ X41 @ X42)
% 59.44/59.63          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 59.44/59.63          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 59.44/59.63  thf('32', plain,
% 59.44/59.63      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 59.44/59.63      inference('sup-', [status(thm)], ['30', '31'])).
% 59.44/59.63  thf('33', plain,
% 59.44/59.63      ((((k2_relat_1 @ sk_D) = (sk_B)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 59.44/59.63      inference('sup-', [status(thm)], ['29', '32'])).
% 59.44/59.63  thf('34', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf('35', plain,
% 59.44/59.63      (![X38 : $i, X39 : $i, X40 : $i]:
% 59.44/59.63         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 59.44/59.63          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 59.44/59.63          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 59.44/59.63  thf('36', plain,
% 59.44/59.63      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 59.44/59.63        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 59.44/59.63      inference('sup-', [status(thm)], ['34', '35'])).
% 59.44/59.63  thf('37', plain,
% 59.44/59.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf(redefinition_k1_relset_1, axiom,
% 59.44/59.63    (![A:$i,B:$i,C:$i]:
% 59.44/59.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 59.44/59.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 59.44/59.63  thf('38', plain,
% 59.44/59.63      (![X33 : $i, X34 : $i, X35 : $i]:
% 59.44/59.63         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 59.44/59.63          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 59.44/59.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 59.44/59.63  thf('39', plain,
% 59.44/59.63      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 59.44/59.63      inference('sup-', [status(thm)], ['37', '38'])).
% 59.44/59.63  thf('40', plain,
% 59.44/59.63      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 59.44/59.63      inference('demod', [status(thm)], ['36', '39'])).
% 59.44/59.63  thf('41', plain,
% 59.44/59.63      ((((k2_relat_1 @ sk_D) = (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 59.44/59.63      inference('sup-', [status(thm)], ['33', '40'])).
% 59.44/59.63  thf('42', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 59.44/59.63      inference('demod', [status(thm)], ['19', '22'])).
% 59.44/59.63  thf('43', plain,
% 59.44/59.63      (![X36 : $i, X37 : $i]:
% 59.44/59.63         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 59.44/59.63  thf('44', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 59.44/59.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 59.44/59.63  thf('45', plain,
% 59.44/59.63      (![X0 : $i, X2 : $i]:
% 59.44/59.63         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 59.44/59.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 59.44/59.63  thf('46', plain,
% 59.44/59.63      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 59.44/59.63      inference('sup-', [status(thm)], ['44', '45'])).
% 59.44/59.63  thf('47', plain,
% 59.44/59.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.44/59.63         (~ (r1_tarski @ X1 @ X0)
% 59.44/59.63          | (zip_tseitin_0 @ X0 @ X2)
% 59.44/59.63          | ((X1) = (k1_xboole_0)))),
% 59.44/59.63      inference('sup-', [status(thm)], ['43', '46'])).
% 59.44/59.63  thf('48', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B @ X0))),
% 59.44/59.63      inference('sup-', [status(thm)], ['42', '47'])).
% 59.44/59.63  thf('49', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (((sk_B) = (k1_xboole_0))
% 59.44/59.63          | ((sk_A) = (k1_relat_1 @ sk_D))
% 59.44/59.63          | (zip_tseitin_0 @ sk_B @ X0))),
% 59.44/59.63      inference('sup+', [status(thm)], ['41', '48'])).
% 59.44/59.63  thf('50', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf('51', plain,
% 59.44/59.63      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 59.44/59.63      inference('split', [status(esa)], ['50'])).
% 59.44/59.63  thf('52', plain,
% 59.44/59.63      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('split', [status(esa)], ['50'])).
% 59.44/59.63  thf('53', plain,
% 59.44/59.63      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 59.44/59.63        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 59.44/59.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 59.44/59.63      inference('demod', [status(thm)], ['0', '5'])).
% 59.44/59.63  thf('54', plain,
% 59.44/59.63      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 59.44/59.63            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 59.44/59.63         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 59.44/59.63              sk_B)))
% 59.44/59.63         <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('sup-', [status(thm)], ['52', '53'])).
% 59.44/59.63  thf(t113_zfmisc_1, axiom,
% 59.44/59.63    (![A:$i,B:$i]:
% 59.44/59.63     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 59.44/59.63       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 59.44/59.63  thf('55', plain,
% 59.44/59.63      (![X8 : $i, X9 : $i]:
% 59.44/59.63         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 59.44/59.63      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 59.44/59.63  thf('56', plain,
% 59.44/59.63      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 59.44/59.63      inference('simplify', [status(thm)], ['55'])).
% 59.44/59.63  thf('57', plain,
% 59.44/59.63      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('split', [status(esa)], ['50'])).
% 59.44/59.63  thf('58', plain,
% 59.44/59.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf('59', plain,
% 59.44/59.63      (((m1_subset_1 @ sk_D @ 
% 59.44/59.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 59.44/59.63         <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('sup+', [status(thm)], ['57', '58'])).
% 59.44/59.63  thf('60', plain,
% 59.44/59.63      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 59.44/59.63         <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('sup+', [status(thm)], ['56', '59'])).
% 59.44/59.63  thf(t3_subset, axiom,
% 59.44/59.63    (![A:$i,B:$i]:
% 59.44/59.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 59.44/59.63  thf('61', plain,
% 59.44/59.63      (![X11 : $i, X12 : $i]:
% 59.44/59.63         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 59.44/59.63      inference('cnf', [status(esa)], [t3_subset])).
% 59.44/59.63  thf('62', plain,
% 59.44/59.63      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('sup-', [status(thm)], ['60', '61'])).
% 59.44/59.63  thf('63', plain,
% 59.44/59.63      (![X0 : $i, X2 : $i]:
% 59.44/59.63         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 59.44/59.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 59.44/59.63  thf('64', plain,
% 59.44/59.63      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 59.44/59.63         <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('sup-', [status(thm)], ['62', '63'])).
% 59.44/59.63  thf('65', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 59.44/59.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 59.44/59.63  thf('66', plain,
% 59.44/59.63      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('demod', [status(thm)], ['64', '65'])).
% 59.44/59.63  thf('67', plain,
% 59.44/59.63      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('split', [status(esa)], ['50'])).
% 59.44/59.63  thf('68', plain, ((r1_tarski @ sk_C @ sk_A)),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf('69', plain,
% 59.44/59.63      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('sup+', [status(thm)], ['67', '68'])).
% 59.44/59.63  thf('70', plain,
% 59.44/59.63      (![X0 : $i, X2 : $i]:
% 59.44/59.63         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 59.44/59.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 59.44/59.63  thf('71', plain,
% 59.44/59.63      (((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C))))
% 59.44/59.63         <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('sup-', [status(thm)], ['69', '70'])).
% 59.44/59.63  thf('72', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 59.44/59.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 59.44/59.63  thf('73', plain,
% 59.44/59.63      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('demod', [status(thm)], ['71', '72'])).
% 59.44/59.63  thf(t4_subset_1, axiom,
% 59.44/59.63    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 59.44/59.63  thf('74', plain,
% 59.44/59.63      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 59.44/59.63      inference('cnf', [status(esa)], [t4_subset_1])).
% 59.44/59.63  thf('75', plain,
% 59.44/59.63      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 59.44/59.63         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 59.44/59.63          | ~ (v1_funct_1 @ X48)
% 59.44/59.63          | ((k2_partfun1 @ X49 @ X50 @ X48 @ X51) = (k7_relat_1 @ X48 @ X51)))),
% 59.44/59.63      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 59.44/59.63  thf('76', plain,
% 59.44/59.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.44/59.63         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 59.44/59.63            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 59.44/59.63          | ~ (v1_funct_1 @ k1_xboole_0))),
% 59.44/59.63      inference('sup-', [status(thm)], ['74', '75'])).
% 59.44/59.63  thf('77', plain,
% 59.44/59.63      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 59.44/59.63      inference('cnf', [status(esa)], [t4_subset_1])).
% 59.44/59.63  thf('78', plain,
% 59.44/59.63      (![X30 : $i, X31 : $i, X32 : $i]:
% 59.44/59.63         ((v4_relat_1 @ X30 @ X31)
% 59.44/59.63          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 59.44/59.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 59.44/59.63  thf('79', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 59.44/59.63      inference('sup-', [status(thm)], ['77', '78'])).
% 59.44/59.63  thf(t209_relat_1, axiom,
% 59.44/59.63    (![A:$i,B:$i]:
% 59.44/59.63     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 59.44/59.63       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 59.44/59.63  thf('80', plain,
% 59.44/59.63      (![X19 : $i, X20 : $i]:
% 59.44/59.63         (((X19) = (k7_relat_1 @ X19 @ X20))
% 59.44/59.63          | ~ (v4_relat_1 @ X19 @ X20)
% 59.44/59.63          | ~ (v1_relat_1 @ X19))),
% 59.44/59.63      inference('cnf', [status(esa)], [t209_relat_1])).
% 59.44/59.63  thf('81', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (~ (v1_relat_1 @ k1_xboole_0)
% 59.44/59.63          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 59.44/59.63      inference('sup-', [status(thm)], ['79', '80'])).
% 59.44/59.63  thf('82', plain,
% 59.44/59.63      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 59.44/59.63      inference('cnf', [status(esa)], [t4_subset_1])).
% 59.44/59.63  thf('83', plain,
% 59.44/59.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 59.44/59.63         ((v1_relat_1 @ X27)
% 59.44/59.63          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 59.44/59.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 59.44/59.63  thf('84', plain, ((v1_relat_1 @ k1_xboole_0)),
% 59.44/59.63      inference('sup-', [status(thm)], ['82', '83'])).
% 59.44/59.63  thf('85', plain,
% 59.44/59.63      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 59.44/59.63      inference('demod', [status(thm)], ['81', '84'])).
% 59.44/59.63  thf('86', plain, ((v1_funct_1 @ sk_D)),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf('87', plain,
% 59.44/59.63      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 59.44/59.63      inference('cnf', [status(esa)], [t4_subset_1])).
% 59.44/59.63  thf(cc3_funct_1, axiom,
% 59.44/59.63    (![A:$i]:
% 59.44/59.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 59.44/59.63       ( ![B:$i]:
% 59.44/59.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_funct_1 @ B ) ) ) ))).
% 59.44/59.63  thf('88', plain,
% 59.44/59.63      (![X25 : $i, X26 : $i]:
% 59.44/59.63         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 59.44/59.63          | (v1_funct_1 @ X25)
% 59.44/59.63          | ~ (v1_funct_1 @ X26)
% 59.44/59.63          | ~ (v1_relat_1 @ X26))),
% 59.44/59.63      inference('cnf', [status(esa)], [cc3_funct_1])).
% 59.44/59.63  thf('89', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (~ (v1_relat_1 @ X0)
% 59.44/59.63          | ~ (v1_funct_1 @ X0)
% 59.44/59.63          | (v1_funct_1 @ k1_xboole_0))),
% 59.44/59.63      inference('sup-', [status(thm)], ['87', '88'])).
% 59.44/59.63  thf('90', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_relat_1 @ sk_D))),
% 59.44/59.63      inference('sup-', [status(thm)], ['86', '89'])).
% 59.44/59.63  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 59.44/59.63      inference('sup-', [status(thm)], ['20', '21'])).
% 59.44/59.63  thf('92', plain, ((v1_funct_1 @ k1_xboole_0)),
% 59.44/59.63      inference('demod', [status(thm)], ['90', '91'])).
% 59.44/59.63  thf('93', plain,
% 59.44/59.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.44/59.63         ((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 59.44/59.63      inference('demod', [status(thm)], ['76', '85', '92'])).
% 59.44/59.63  thf('94', plain,
% 59.44/59.63      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('demod', [status(thm)], ['71', '72'])).
% 59.44/59.63  thf('95', plain,
% 59.44/59.63      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 59.44/59.63      inference('simplify', [status(thm)], ['55'])).
% 59.44/59.63  thf('96', plain,
% 59.44/59.63      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 59.44/59.63      inference('cnf', [status(esa)], [t4_subset_1])).
% 59.44/59.63  thf('97', plain,
% 59.44/59.63      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('split', [status(esa)], ['50'])).
% 59.44/59.63  thf('98', plain,
% 59.44/59.63      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('demod', [status(thm)], ['64', '65'])).
% 59.44/59.63  thf('99', plain,
% 59.44/59.63      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('demod', [status(thm)], ['71', '72'])).
% 59.44/59.63  thf('100', plain,
% 59.44/59.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.44/59.63         ((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 59.44/59.63      inference('demod', [status(thm)], ['76', '85', '92'])).
% 59.44/59.63  thf('101', plain,
% 59.44/59.63      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 59.44/59.63      inference('demod', [status(thm)], ['71', '72'])).
% 59.44/59.63  thf('102', plain,
% 59.44/59.63      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 59.44/59.63      inference('cnf', [status(esa)], [t4_subset_1])).
% 59.44/59.63  thf('103', plain,
% 59.44/59.63      (![X33 : $i, X34 : $i, X35 : $i]:
% 59.44/59.63         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 59.44/59.63          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 59.44/59.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 59.44/59.63  thf('104', plain,
% 59.44/59.63      (![X0 : $i, X1 : $i]:
% 59.44/59.63         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 59.44/59.63      inference('sup-', [status(thm)], ['102', '103'])).
% 59.44/59.63  thf(t60_relat_1, axiom,
% 59.44/59.63    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 59.44/59.63     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 59.44/59.63  thf('105', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 59.44/59.63      inference('cnf', [status(esa)], [t60_relat_1])).
% 59.44/59.63  thf('106', plain,
% 59.44/59.63      (![X0 : $i, X1 : $i]:
% 59.44/59.63         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 59.44/59.63      inference('demod', [status(thm)], ['104', '105'])).
% 59.44/59.63  thf('107', plain,
% 59.44/59.63      (![X38 : $i, X39 : $i, X40 : $i]:
% 59.44/59.63         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 59.44/59.63          | (v1_funct_2 @ X40 @ X38 @ X39)
% 59.44/59.63          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 59.44/59.63  thf('108', plain,
% 59.44/59.63      (![X0 : $i, X1 : $i]:
% 59.44/59.63         (((X1) != (k1_xboole_0))
% 59.44/59.63          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 59.44/59.63          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 59.44/59.63      inference('sup-', [status(thm)], ['106', '107'])).
% 59.44/59.63  thf('109', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 59.44/59.63          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 59.44/59.63      inference('simplify', [status(thm)], ['108'])).
% 59.44/59.63  thf('110', plain,
% 59.44/59.63      (![X36 : $i, X37 : $i]:
% 59.44/59.63         ((zip_tseitin_0 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 59.44/59.63  thf('111', plain, (![X36 : $i]: (zip_tseitin_0 @ X36 @ k1_xboole_0)),
% 59.44/59.63      inference('simplify', [status(thm)], ['110'])).
% 59.44/59.63  thf('112', plain,
% 59.44/59.63      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 59.44/59.63      inference('cnf', [status(esa)], [t4_subset_1])).
% 59.44/59.63  thf('113', plain,
% 59.44/59.63      (![X41 : $i, X42 : $i, X43 : $i]:
% 59.44/59.63         (~ (zip_tseitin_0 @ X41 @ X42)
% 59.44/59.63          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 59.44/59.63          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 59.44/59.63  thf('114', plain,
% 59.44/59.63      (![X0 : $i, X1 : $i]:
% 59.44/59.63         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 59.44/59.63      inference('sup-', [status(thm)], ['112', '113'])).
% 59.44/59.63  thf('115', plain,
% 59.44/59.63      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 59.44/59.63      inference('sup-', [status(thm)], ['111', '114'])).
% 59.44/59.63  thf('116', plain,
% 59.44/59.63      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 59.44/59.63      inference('demod', [status(thm)], ['109', '115'])).
% 59.44/59.63  thf('117', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 59.44/59.63      inference('demod', [status(thm)],
% 59.44/59.63                ['54', '66', '73', '93', '94', '95', '96', '97', '98', '99', 
% 59.44/59.63                 '100', '101', '116'])).
% 59.44/59.63  thf('118', plain,
% 59.44/59.63      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 59.44/59.63      inference('split', [status(esa)], ['50'])).
% 59.44/59.63  thf('119', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 59.44/59.63      inference('sat_resolution*', [status(thm)], ['117', '118'])).
% 59.44/59.63  thf('120', plain, (((sk_B) != (k1_xboole_0))),
% 59.44/59.63      inference('simpl_trail', [status(thm)], ['51', '119'])).
% 59.44/59.63  thf('121', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ sk_B @ X0))),
% 59.44/59.63      inference('simplify_reflect-', [status(thm)], ['49', '120'])).
% 59.44/59.63  thf('122', plain,
% 59.44/59.63      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 59.44/59.63      inference('sup-', [status(thm)], ['30', '31'])).
% 59.44/59.63  thf('123', plain,
% 59.44/59.63      ((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 59.44/59.63      inference('sup-', [status(thm)], ['121', '122'])).
% 59.44/59.63  thf('124', plain,
% 59.44/59.63      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 59.44/59.63      inference('demod', [status(thm)], ['36', '39'])).
% 59.44/59.63  thf('125', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 59.44/59.63      inference('clc', [status(thm)], ['123', '124'])).
% 59.44/59.63  thf(t91_relat_1, axiom,
% 59.44/59.63    (![A:$i,B:$i]:
% 59.44/59.63     ( ( v1_relat_1 @ B ) =>
% 59.44/59.63       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 59.44/59.63         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 59.44/59.63  thf('126', plain,
% 59.44/59.63      (![X21 : $i, X22 : $i]:
% 59.44/59.63         (~ (r1_tarski @ X21 @ (k1_relat_1 @ X22))
% 59.44/59.63          | ((k1_relat_1 @ (k7_relat_1 @ X22 @ X21)) = (X21))
% 59.44/59.63          | ~ (v1_relat_1 @ X22))),
% 59.44/59.63      inference('cnf', [status(esa)], [t91_relat_1])).
% 59.44/59.63  thf('127', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (~ (r1_tarski @ X0 @ sk_A)
% 59.44/59.63          | ~ (v1_relat_1 @ sk_D)
% 59.44/59.63          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 59.44/59.63      inference('sup-', [status(thm)], ['125', '126'])).
% 59.44/59.63  thf('128', plain, ((v1_relat_1 @ sk_D)),
% 59.44/59.63      inference('sup-', [status(thm)], ['20', '21'])).
% 59.44/59.63  thf('129', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (~ (r1_tarski @ X0 @ sk_A)
% 59.44/59.63          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 59.44/59.63      inference('demod', [status(thm)], ['127', '128'])).
% 59.44/59.63  thf('130', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 59.44/59.63      inference('sup-', [status(thm)], ['14', '129'])).
% 59.44/59.63  thf('131', plain,
% 59.44/59.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf('132', plain,
% 59.44/59.63      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 59.44/59.63         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 59.44/59.63          | ~ (v1_funct_1 @ X44)
% 59.44/59.63          | (m1_subset_1 @ (k2_partfun1 @ X45 @ X46 @ X44 @ X47) @ 
% 59.44/59.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 59.44/59.63      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 59.44/59.63  thf('133', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 59.44/59.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 59.44/59.63          | ~ (v1_funct_1 @ sk_D))),
% 59.44/59.63      inference('sup-', [status(thm)], ['131', '132'])).
% 59.44/59.63  thf('134', plain, ((v1_funct_1 @ sk_D)),
% 59.44/59.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.44/59.63  thf('135', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 59.44/59.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 59.44/59.63      inference('demod', [status(thm)], ['133', '134'])).
% 59.44/59.63  thf('136', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 59.44/59.63      inference('demod', [status(thm)], ['9', '10'])).
% 59.44/59.63  thf('137', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 59.44/59.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 59.44/59.63      inference('demod', [status(thm)], ['135', '136'])).
% 59.44/59.63  thf('138', plain,
% 59.44/59.63      (![X30 : $i, X31 : $i, X32 : $i]:
% 59.44/59.63         ((v5_relat_1 @ X30 @ X32)
% 59.44/59.63          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 59.44/59.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 59.44/59.63  thf('139', plain,
% 59.44/59.63      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 59.44/59.63      inference('sup-', [status(thm)], ['137', '138'])).
% 59.44/59.63  thf('140', plain,
% 59.44/59.63      (![X17 : $i, X18 : $i]:
% 59.44/59.63         (~ (v5_relat_1 @ X17 @ X18)
% 59.44/59.63          | (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 59.44/59.63          | ~ (v1_relat_1 @ X17))),
% 59.44/59.63      inference('cnf', [status(esa)], [d19_relat_1])).
% 59.44/59.63  thf('141', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 59.44/59.63          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 59.44/59.63      inference('sup-', [status(thm)], ['139', '140'])).
% 59.44/59.63  thf('142', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 59.44/59.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 59.44/59.63      inference('demod', [status(thm)], ['135', '136'])).
% 59.44/59.63  thf('143', plain,
% 59.44/59.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 59.44/59.63         ((v1_relat_1 @ X27)
% 59.44/59.63          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 59.44/59.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 59.44/59.63  thf('144', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 59.44/59.63      inference('sup-', [status(thm)], ['142', '143'])).
% 59.44/59.63  thf('145', plain,
% 59.44/59.63      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 59.44/59.63      inference('demod', [status(thm)], ['141', '144'])).
% 59.44/59.63  thf(t4_funct_2, axiom,
% 59.44/59.63    (![A:$i,B:$i]:
% 59.44/59.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 59.44/59.63       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 59.44/59.63         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 59.44/59.63           ( m1_subset_1 @
% 59.44/59.63             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 59.44/59.63  thf('146', plain,
% 59.44/59.63      (![X52 : $i, X53 : $i]:
% 59.44/59.63         (~ (r1_tarski @ (k2_relat_1 @ X52) @ X53)
% 59.44/59.63          | (v1_funct_2 @ X52 @ (k1_relat_1 @ X52) @ X53)
% 59.44/59.63          | ~ (v1_funct_1 @ X52)
% 59.44/59.63          | ~ (v1_relat_1 @ X52))),
% 59.44/59.63      inference('cnf', [status(esa)], [t4_funct_2])).
% 59.44/59.63  thf('147', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 59.44/59.63          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 59.44/59.63          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 59.44/59.63             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 59.44/59.63      inference('sup-', [status(thm)], ['145', '146'])).
% 59.44/59.63  thf('148', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 59.44/59.63      inference('sup-', [status(thm)], ['142', '143'])).
% 59.44/59.63  thf('149', plain,
% 59.44/59.63      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 59.44/59.63      inference('demod', [status(thm)], ['3', '4'])).
% 59.44/59.63  thf('150', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 59.44/59.63      inference('demod', [status(thm)], ['9', '10'])).
% 59.44/59.63  thf('151', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 59.44/59.63      inference('demod', [status(thm)], ['149', '150'])).
% 59.44/59.63  thf('152', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 59.44/59.63          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 59.44/59.63      inference('demod', [status(thm)], ['147', '148', '151'])).
% 59.44/59.63  thf('153', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 59.44/59.63      inference('sup+', [status(thm)], ['130', '152'])).
% 59.44/59.63  thf('154', plain,
% 59.44/59.63      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 59.44/59.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 59.44/59.63      inference('demod', [status(thm)], ['13', '153'])).
% 59.44/59.63  thf('155', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 59.44/59.63      inference('sup-', [status(thm)], ['14', '129'])).
% 59.44/59.63  thf('156', plain,
% 59.44/59.63      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 59.44/59.63      inference('demod', [status(thm)], ['141', '144'])).
% 59.44/59.63  thf('157', plain,
% 59.44/59.63      (![X52 : $i, X53 : $i]:
% 59.44/59.63         (~ (r1_tarski @ (k2_relat_1 @ X52) @ X53)
% 59.44/59.63          | (m1_subset_1 @ X52 @ 
% 59.44/59.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X52) @ X53)))
% 59.44/59.63          | ~ (v1_funct_1 @ X52)
% 59.44/59.63          | ~ (v1_relat_1 @ X52))),
% 59.44/59.63      inference('cnf', [status(esa)], [t4_funct_2])).
% 59.44/59.63  thf('158', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 59.44/59.63          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 59.44/59.63          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 59.44/59.63             (k1_zfmisc_1 @ 
% 59.44/59.63              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 59.44/59.63      inference('sup-', [status(thm)], ['156', '157'])).
% 59.44/59.63  thf('159', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 59.44/59.63      inference('sup-', [status(thm)], ['142', '143'])).
% 59.44/59.63  thf('160', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 59.44/59.63      inference('demod', [status(thm)], ['149', '150'])).
% 59.44/59.63  thf('161', plain,
% 59.44/59.63      (![X0 : $i]:
% 59.44/59.63         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 59.44/59.63          (k1_zfmisc_1 @ 
% 59.44/59.63           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 59.44/59.63      inference('demod', [status(thm)], ['158', '159', '160'])).
% 59.44/59.63  thf('162', plain,
% 59.44/59.63      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 59.44/59.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 59.44/59.63      inference('sup+', [status(thm)], ['155', '161'])).
% 59.44/59.63  thf('163', plain, ($false), inference('demod', [status(thm)], ['154', '162'])).
% 59.44/59.63  
% 59.44/59.63  % SZS output end Refutation
% 59.44/59.63  
% 59.44/59.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
