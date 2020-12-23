%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4pZI4ezWMp

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:42 EST 2020

% Result     : Theorem 9.94s
% Output     : Refutation 9.94s
% Verified   : 
% Statistics : Number of formulae       :  183 (1639 expanded)
%              Number of leaves         :   39 ( 487 expanded)
%              Depth                    :   25
%              Number of atoms          : 1416 (23764 expanded)
%              Number of equality atoms :  120 (1760 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X40 @ X41 @ X39 @ X42 ) ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X44 @ X45 @ X43 @ X46 )
        = ( k7_relat_1 @ X43 @ X46 ) ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

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

thf('18',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','34'])).

thf('36',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('39',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('40',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','45'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('49',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('50',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('52',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('55',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('60',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X44 @ X45 @ X43 @ X46 )
        = ( k7_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('64',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('65',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('69',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['63','70'])).

thf('72',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','71'])).

thf('73',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('74',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('75',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('77',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('78',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('79',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','71'])).

thf('80',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('81',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('82',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('85',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('86',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','87'])).

thf('89',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['67','68'])).

thf('90',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('96',plain,(
    ! [X31: $i] :
      ( zip_tseitin_0 @ X31 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('98',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['94','100'])).

thf('102',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['40','50','55','72','73','74','75','76','77','78','79','80','101'])).

thf('103',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('104',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['102','103'])).

thf('105',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','104'])).

thf('106',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['35','105'])).

thf('107',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('110',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('111',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['108','111'])).

thf('113',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','112'])).

thf('114',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('115',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('116',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( r1_tarski @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['109','110'])).

thf('120',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('121',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['113','122'])).

thf('124',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','123'])).

thf('125',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['13','124'])).

thf('126',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','123'])).

thf('127',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('128',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','112'])).

thf('130',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('132',plain,
    ( ( sk_C != sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('135',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','123'])).

thf('136',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('137',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['134','137'])).

thf('139',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','104'])).

thf('140',plain,(
    zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['133','140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['125','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4pZI4ezWMp
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:32:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 9.94/10.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.94/10.19  % Solved by: fo/fo7.sh
% 9.94/10.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.94/10.19  % done 6161 iterations in 9.732s
% 9.94/10.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.94/10.19  % SZS output start Refutation
% 9.94/10.19  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 9.94/10.19  thf(sk_C_type, type, sk_C: $i).
% 9.94/10.19  thf(sk_D_type, type, sk_D: $i).
% 9.94/10.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.94/10.19  thf(sk_A_type, type, sk_A: $i).
% 9.94/10.19  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.94/10.19  thf(sk_B_type, type, sk_B: $i).
% 9.94/10.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.94/10.19  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 9.94/10.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.94/10.19  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 9.94/10.19  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 9.94/10.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.94/10.19  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 9.94/10.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.94/10.19  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 9.94/10.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.94/10.19  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.94/10.19  thf(t38_funct_2, conjecture,
% 9.94/10.19    (![A:$i,B:$i,C:$i,D:$i]:
% 9.94/10.19     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 9.94/10.19         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.94/10.19       ( ( r1_tarski @ C @ A ) =>
% 9.94/10.19         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 9.94/10.19           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 9.94/10.19             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 9.94/10.19             ( m1_subset_1 @
% 9.94/10.19               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 9.94/10.19               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 9.94/10.19  thf(zf_stmt_0, negated_conjecture,
% 9.94/10.19    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 9.94/10.19        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 9.94/10.19            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.94/10.19          ( ( r1_tarski @ C @ A ) =>
% 9.94/10.19            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 9.94/10.19              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 9.94/10.19                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 9.94/10.19                ( m1_subset_1 @
% 9.94/10.19                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 9.94/10.19                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 9.94/10.19    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 9.94/10.19  thf('0', plain,
% 9.94/10.19      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 9.94/10.19        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 9.94/10.19             sk_B)
% 9.94/10.19        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 9.94/10.19             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.19  thf('1', plain,
% 9.94/10.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.19  thf(dt_k2_partfun1, axiom,
% 9.94/10.19    (![A:$i,B:$i,C:$i,D:$i]:
% 9.94/10.19     ( ( ( v1_funct_1 @ C ) & 
% 9.94/10.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.94/10.19       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 9.94/10.19         ( m1_subset_1 @
% 9.94/10.19           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 9.94/10.19           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 9.94/10.19  thf('2', plain,
% 9.94/10.19      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 9.94/10.19         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 9.94/10.19          | ~ (v1_funct_1 @ X39)
% 9.94/10.19          | (v1_funct_1 @ (k2_partfun1 @ X40 @ X41 @ X39 @ X42)))),
% 9.94/10.19      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 9.94/10.19  thf('3', plain,
% 9.94/10.19      (![X0 : $i]:
% 9.94/10.19         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 9.94/10.19          | ~ (v1_funct_1 @ sk_D))),
% 9.94/10.19      inference('sup-', [status(thm)], ['1', '2'])).
% 9.94/10.19  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.19  thf('5', plain,
% 9.94/10.19      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 9.94/10.19      inference('demod', [status(thm)], ['3', '4'])).
% 9.94/10.19  thf('6', plain,
% 9.94/10.19      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 9.94/10.19        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 9.94/10.19             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 9.94/10.19      inference('demod', [status(thm)], ['0', '5'])).
% 9.94/10.19  thf('7', plain,
% 9.94/10.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.19  thf(redefinition_k2_partfun1, axiom,
% 9.94/10.19    (![A:$i,B:$i,C:$i,D:$i]:
% 9.94/10.19     ( ( ( v1_funct_1 @ C ) & 
% 9.94/10.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.94/10.19       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 9.94/10.19  thf('8', plain,
% 9.94/10.19      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 9.94/10.19         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 9.94/10.19          | ~ (v1_funct_1 @ X43)
% 9.94/10.19          | ((k2_partfun1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 9.94/10.19      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 9.94/10.19  thf('9', plain,
% 9.94/10.19      (![X0 : $i]:
% 9.94/10.19         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 9.94/10.19          | ~ (v1_funct_1 @ sk_D))),
% 9.94/10.19      inference('sup-', [status(thm)], ['7', '8'])).
% 9.94/10.19  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.19  thf('11', plain,
% 9.94/10.19      (![X0 : $i]:
% 9.94/10.19         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 9.94/10.19      inference('demod', [status(thm)], ['9', '10'])).
% 9.94/10.19  thf('12', plain,
% 9.94/10.19      (![X0 : $i]:
% 9.94/10.19         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 9.94/10.19      inference('demod', [status(thm)], ['9', '10'])).
% 9.94/10.19  thf('13', plain,
% 9.94/10.19      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 9.94/10.19        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 9.94/10.19             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 9.94/10.19      inference('demod', [status(thm)], ['6', '11', '12'])).
% 9.94/10.19  thf(d10_xboole_0, axiom,
% 9.94/10.19    (![A:$i,B:$i]:
% 9.94/10.19     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.94/10.19  thf('14', plain,
% 9.94/10.19      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 9.94/10.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.94/10.19  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.94/10.19      inference('simplify', [status(thm)], ['14'])).
% 9.94/10.19  thf('16', plain, ((r1_tarski @ sk_C @ sk_A)),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.19  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 9.94/10.19  thf('17', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 9.94/10.19      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.94/10.19  thf(d1_funct_2, axiom,
% 9.94/10.19    (![A:$i,B:$i,C:$i]:
% 9.94/10.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.94/10.19       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 9.94/10.19           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 9.94/10.19             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 9.94/10.19         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 9.94/10.19           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 9.94/10.19             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 9.94/10.19  thf(zf_stmt_1, axiom,
% 9.94/10.19    (![B:$i,A:$i]:
% 9.94/10.19     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 9.94/10.19       ( zip_tseitin_0 @ B @ A ) ))).
% 9.94/10.19  thf('18', plain,
% 9.94/10.19      (![X31 : $i, X32 : $i]:
% 9.94/10.19         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.94/10.19  thf('19', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 9.94/10.19      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.94/10.19  thf('20', plain,
% 9.94/10.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.94/10.19         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 9.94/10.19      inference('sup+', [status(thm)], ['18', '19'])).
% 9.94/10.19  thf('21', plain,
% 9.94/10.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.19  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 9.94/10.19  thf(zf_stmt_3, axiom,
% 9.94/10.19    (![C:$i,B:$i,A:$i]:
% 9.94/10.19     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 9.94/10.19       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 9.94/10.19  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 9.94/10.19  thf(zf_stmt_5, axiom,
% 9.94/10.19    (![A:$i,B:$i,C:$i]:
% 9.94/10.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.94/10.19       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 9.94/10.19         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 9.94/10.19           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 9.94/10.19             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 9.94/10.19  thf('22', plain,
% 9.94/10.19      (![X36 : $i, X37 : $i, X38 : $i]:
% 9.94/10.19         (~ (zip_tseitin_0 @ X36 @ X37)
% 9.94/10.19          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 9.94/10.19          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 9.94/10.19  thf('23', plain,
% 9.94/10.19      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 9.94/10.19      inference('sup-', [status(thm)], ['21', '22'])).
% 9.94/10.19  thf('24', plain,
% 9.94/10.19      (![X0 : $i]:
% 9.94/10.19         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 9.94/10.19      inference('sup-', [status(thm)], ['20', '23'])).
% 9.94/10.19  thf('25', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.19  thf('26', plain,
% 9.94/10.19      (![X33 : $i, X34 : $i, X35 : $i]:
% 9.94/10.19         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 9.94/10.19          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 9.94/10.19          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_3])).
% 9.94/10.19  thf('27', plain,
% 9.94/10.19      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 9.94/10.19        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 9.94/10.19      inference('sup-', [status(thm)], ['25', '26'])).
% 9.94/10.19  thf('28', plain,
% 9.94/10.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.19  thf(redefinition_k1_relset_1, axiom,
% 9.94/10.19    (![A:$i,B:$i,C:$i]:
% 9.94/10.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.94/10.19       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 9.94/10.19  thf('29', plain,
% 9.94/10.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 9.94/10.19         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 9.94/10.19          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 9.94/10.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 9.94/10.19  thf('30', plain,
% 9.94/10.19      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 9.94/10.19      inference('sup-', [status(thm)], ['28', '29'])).
% 9.94/10.19  thf('31', plain,
% 9.94/10.19      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 9.94/10.19      inference('demod', [status(thm)], ['27', '30'])).
% 9.94/10.19  thf('32', plain,
% 9.94/10.19      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 9.94/10.19      inference('sup-', [status(thm)], ['24', '31'])).
% 9.94/10.19  thf('33', plain,
% 9.94/10.19      (![X0 : $i, X2 : $i]:
% 9.94/10.19         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 9.94/10.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.94/10.19  thf('34', plain,
% 9.94/10.19      (![X0 : $i]:
% 9.94/10.19         (((sk_A) = (k1_relat_1 @ sk_D))
% 9.94/10.19          | ~ (r1_tarski @ X0 @ sk_B)
% 9.94/10.19          | ((X0) = (sk_B)))),
% 9.94/10.19      inference('sup-', [status(thm)], ['32', '33'])).
% 9.94/10.19  thf('35', plain,
% 9.94/10.19      ((((k1_xboole_0) = (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 9.94/10.19      inference('sup-', [status(thm)], ['17', '34'])).
% 9.94/10.19  thf('36', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.19  thf('37', plain,
% 9.94/10.19      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 9.94/10.19      inference('split', [status(esa)], ['36'])).
% 9.94/10.19  thf('38', plain,
% 9.94/10.19      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('split', [status(esa)], ['36'])).
% 9.94/10.19  thf('39', plain,
% 9.94/10.19      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 9.94/10.19        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 9.94/10.19             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 9.94/10.19      inference('demod', [status(thm)], ['0', '5'])).
% 9.94/10.19  thf('40', plain,
% 9.94/10.19      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 9.94/10.19            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 9.94/10.19         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 9.94/10.19              sk_B)))
% 9.94/10.19         <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('sup-', [status(thm)], ['38', '39'])).
% 9.94/10.19  thf('41', plain,
% 9.94/10.19      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('split', [status(esa)], ['36'])).
% 9.94/10.19  thf('42', plain,
% 9.94/10.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.19  thf('43', plain,
% 9.94/10.19      (((m1_subset_1 @ sk_D @ 
% 9.94/10.19         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 9.94/10.19         <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('sup+', [status(thm)], ['41', '42'])).
% 9.94/10.19  thf(t113_zfmisc_1, axiom,
% 9.94/10.19    (![A:$i,B:$i]:
% 9.94/10.19     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 9.94/10.19       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 9.94/10.19  thf('44', plain,
% 9.94/10.19      (![X6 : $i, X7 : $i]:
% 9.94/10.19         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 9.94/10.19      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 9.94/10.19  thf('45', plain,
% 9.94/10.19      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 9.94/10.19      inference('simplify', [status(thm)], ['44'])).
% 9.94/10.19  thf('46', plain,
% 9.94/10.19      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 9.94/10.19         <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('demod', [status(thm)], ['43', '45'])).
% 9.94/10.19  thf(t3_subset, axiom,
% 9.94/10.19    (![A:$i,B:$i]:
% 9.94/10.19     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 9.94/10.19  thf('47', plain,
% 9.94/10.19      (![X8 : $i, X9 : $i]:
% 9.94/10.19         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 9.94/10.19      inference('cnf', [status(esa)], [t3_subset])).
% 9.94/10.19  thf('48', plain,
% 9.94/10.19      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('sup-', [status(thm)], ['46', '47'])).
% 9.94/10.19  thf(t3_xboole_1, axiom,
% 9.94/10.19    (![A:$i]:
% 9.94/10.19     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 9.94/10.19  thf('49', plain,
% 9.94/10.19      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 9.94/10.19      inference('cnf', [status(esa)], [t3_xboole_1])).
% 9.94/10.19  thf('50', plain,
% 9.94/10.19      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('sup-', [status(thm)], ['48', '49'])).
% 9.94/10.19  thf('51', plain,
% 9.94/10.19      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('split', [status(esa)], ['36'])).
% 9.94/10.19  thf('52', plain, ((r1_tarski @ sk_C @ sk_A)),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.19  thf('53', plain,
% 9.94/10.19      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('sup+', [status(thm)], ['51', '52'])).
% 9.94/10.19  thf('54', plain,
% 9.94/10.19      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 9.94/10.19      inference('cnf', [status(esa)], [t3_xboole_1])).
% 9.94/10.19  thf('55', plain,
% 9.94/10.19      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('sup-', [status(thm)], ['53', '54'])).
% 9.94/10.19  thf('56', plain,
% 9.94/10.19      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('sup-', [status(thm)], ['48', '49'])).
% 9.94/10.19  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.19  thf('58', plain,
% 9.94/10.19      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('sup+', [status(thm)], ['56', '57'])).
% 9.94/10.19  thf('59', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 9.94/10.19      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.94/10.19  thf('60', plain,
% 9.94/10.19      (![X8 : $i, X10 : $i]:
% 9.94/10.19         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 9.94/10.19      inference('cnf', [status(esa)], [t3_subset])).
% 9.94/10.19  thf('61', plain,
% 9.94/10.19      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 9.94/10.19      inference('sup-', [status(thm)], ['59', '60'])).
% 9.94/10.19  thf('62', plain,
% 9.94/10.19      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 9.94/10.19         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 9.94/10.19          | ~ (v1_funct_1 @ X43)
% 9.94/10.19          | ((k2_partfun1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 9.94/10.19      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 9.94/10.19  thf('63', plain,
% 9.94/10.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.94/10.19         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 9.94/10.19            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 9.94/10.19          | ~ (v1_funct_1 @ k1_xboole_0))),
% 9.94/10.19      inference('sup-', [status(thm)], ['61', '62'])).
% 9.94/10.19  thf(t88_relat_1, axiom,
% 9.94/10.19    (![A:$i,B:$i]:
% 9.94/10.19     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 9.94/10.19  thf('64', plain,
% 9.94/10.19      (![X13 : $i, X14 : $i]:
% 9.94/10.19         ((r1_tarski @ (k7_relat_1 @ X13 @ X14) @ X13) | ~ (v1_relat_1 @ X13))),
% 9.94/10.19      inference('cnf', [status(esa)], [t88_relat_1])).
% 9.94/10.19  thf('65', plain,
% 9.94/10.19      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 9.94/10.19      inference('cnf', [status(esa)], [t3_xboole_1])).
% 9.94/10.19  thf('66', plain,
% 9.94/10.19      (![X0 : $i]:
% 9.94/10.19         (~ (v1_relat_1 @ k1_xboole_0)
% 9.94/10.19          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 9.94/10.19      inference('sup-', [status(thm)], ['64', '65'])).
% 9.94/10.19  thf('67', plain,
% 9.94/10.19      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 9.94/10.19      inference('simplify', [status(thm)], ['44'])).
% 9.94/10.19  thf(fc6_relat_1, axiom,
% 9.94/10.19    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 9.94/10.19  thf('68', plain,
% 9.94/10.19      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 9.94/10.19      inference('cnf', [status(esa)], [fc6_relat_1])).
% 9.94/10.19  thf('69', plain, ((v1_relat_1 @ k1_xboole_0)),
% 9.94/10.19      inference('sup+', [status(thm)], ['67', '68'])).
% 9.94/10.19  thf('70', plain,
% 9.94/10.19      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 9.94/10.19      inference('demod', [status(thm)], ['66', '69'])).
% 9.94/10.19  thf('71', plain,
% 9.94/10.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.94/10.19         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 9.94/10.19          | ~ (v1_funct_1 @ k1_xboole_0))),
% 9.94/10.19      inference('demod', [status(thm)], ['63', '70'])).
% 9.94/10.19  thf('72', plain,
% 9.94/10.19      ((![X0 : $i, X1 : $i, X2 : $i]:
% 9.94/10.19          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 9.94/10.19         <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('sup-', [status(thm)], ['58', '71'])).
% 9.94/10.19  thf('73', plain,
% 9.94/10.19      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('sup-', [status(thm)], ['53', '54'])).
% 9.94/10.19  thf('74', plain,
% 9.94/10.19      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 9.94/10.19      inference('simplify', [status(thm)], ['44'])).
% 9.94/10.19  thf('75', plain,
% 9.94/10.19      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 9.94/10.19      inference('sup-', [status(thm)], ['59', '60'])).
% 9.94/10.19  thf('76', plain,
% 9.94/10.19      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('split', [status(esa)], ['36'])).
% 9.94/10.19  thf('77', plain,
% 9.94/10.19      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('sup-', [status(thm)], ['48', '49'])).
% 9.94/10.19  thf('78', plain,
% 9.94/10.19      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('sup-', [status(thm)], ['53', '54'])).
% 9.94/10.19  thf('79', plain,
% 9.94/10.19      ((![X0 : $i, X1 : $i, X2 : $i]:
% 9.94/10.19          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 9.94/10.19         <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('sup-', [status(thm)], ['58', '71'])).
% 9.94/10.19  thf('80', plain,
% 9.94/10.19      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.94/10.19      inference('sup-', [status(thm)], ['53', '54'])).
% 9.94/10.19  thf('81', plain,
% 9.94/10.19      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 9.94/10.19      inference('sup-', [status(thm)], ['59', '60'])).
% 9.94/10.19  thf('82', plain,
% 9.94/10.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 9.94/10.19         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 9.94/10.19          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 9.94/10.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 9.94/10.19  thf('83', plain,
% 9.94/10.19      (![X0 : $i, X1 : $i]:
% 9.94/10.19         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 9.94/10.19      inference('sup-', [status(thm)], ['81', '82'])).
% 9.94/10.19  thf('84', plain,
% 9.94/10.19      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 9.94/10.19      inference('demod', [status(thm)], ['66', '69'])).
% 9.94/10.19  thf('85', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 9.94/10.19      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.94/10.19  thf(t91_relat_1, axiom,
% 9.94/10.19    (![A:$i,B:$i]:
% 9.94/10.19     ( ( v1_relat_1 @ B ) =>
% 9.94/10.19       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 9.94/10.19         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 9.94/10.19  thf('86', plain,
% 9.94/10.19      (![X15 : $i, X16 : $i]:
% 9.94/10.19         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 9.94/10.19          | ((k1_relat_1 @ (k7_relat_1 @ X16 @ X15)) = (X15))
% 9.94/10.19          | ~ (v1_relat_1 @ X16))),
% 9.94/10.19      inference('cnf', [status(esa)], [t91_relat_1])).
% 9.94/10.19  thf('87', plain,
% 9.94/10.19      (![X0 : $i]:
% 9.94/10.19         (~ (v1_relat_1 @ X0)
% 9.94/10.19          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 9.94/10.19      inference('sup-', [status(thm)], ['85', '86'])).
% 9.94/10.19  thf('88', plain,
% 9.94/10.19      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 9.94/10.19        | ~ (v1_relat_1 @ k1_xboole_0))),
% 9.94/10.19      inference('sup+', [status(thm)], ['84', '87'])).
% 9.94/10.19  thf('89', plain, ((v1_relat_1 @ k1_xboole_0)),
% 9.94/10.19      inference('sup+', [status(thm)], ['67', '68'])).
% 9.94/10.19  thf('90', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.94/10.19      inference('demod', [status(thm)], ['88', '89'])).
% 9.94/10.19  thf('91', plain,
% 9.94/10.19      (![X0 : $i, X1 : $i]:
% 9.94/10.19         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 9.94/10.19      inference('demod', [status(thm)], ['83', '90'])).
% 9.94/10.19  thf('92', plain,
% 9.94/10.19      (![X33 : $i, X34 : $i, X35 : $i]:
% 9.94/10.19         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 9.94/10.19          | (v1_funct_2 @ X35 @ X33 @ X34)
% 9.94/10.19          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_3])).
% 9.94/10.19  thf('93', plain,
% 9.94/10.19      (![X0 : $i, X1 : $i]:
% 9.94/10.19         (((X1) != (k1_xboole_0))
% 9.94/10.19          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 9.94/10.19          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 9.94/10.19      inference('sup-', [status(thm)], ['91', '92'])).
% 9.94/10.19  thf('94', plain,
% 9.94/10.19      (![X0 : $i]:
% 9.94/10.19         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 9.94/10.19          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 9.94/10.19      inference('simplify', [status(thm)], ['93'])).
% 9.94/10.19  thf('95', plain,
% 9.94/10.19      (![X31 : $i, X32 : $i]:
% 9.94/10.19         ((zip_tseitin_0 @ X31 @ X32) | ((X32) != (k1_xboole_0)))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.94/10.19  thf('96', plain, (![X31 : $i]: (zip_tseitin_0 @ X31 @ k1_xboole_0)),
% 9.94/10.19      inference('simplify', [status(thm)], ['95'])).
% 9.94/10.19  thf('97', plain,
% 9.94/10.19      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 9.94/10.19      inference('sup-', [status(thm)], ['59', '60'])).
% 9.94/10.19  thf('98', plain,
% 9.94/10.19      (![X36 : $i, X37 : $i, X38 : $i]:
% 9.94/10.19         (~ (zip_tseitin_0 @ X36 @ X37)
% 9.94/10.19          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 9.94/10.19          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 9.94/10.19  thf('99', plain,
% 9.94/10.19      (![X0 : $i, X1 : $i]:
% 9.94/10.19         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 9.94/10.19      inference('sup-', [status(thm)], ['97', '98'])).
% 9.94/10.19  thf('100', plain,
% 9.94/10.19      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 9.94/10.19      inference('sup-', [status(thm)], ['96', '99'])).
% 9.94/10.19  thf('101', plain,
% 9.94/10.19      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 9.94/10.19      inference('demod', [status(thm)], ['94', '100'])).
% 9.94/10.19  thf('102', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 9.94/10.19      inference('demod', [status(thm)],
% 9.94/10.19                ['40', '50', '55', '72', '73', '74', '75', '76', '77', '78', 
% 9.94/10.19                 '79', '80', '101'])).
% 9.94/10.19  thf('103', plain,
% 9.94/10.19      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 9.94/10.19      inference('split', [status(esa)], ['36'])).
% 9.94/10.19  thf('104', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 9.94/10.19      inference('sat_resolution*', [status(thm)], ['102', '103'])).
% 9.94/10.19  thf('105', plain, (((sk_B) != (k1_xboole_0))),
% 9.94/10.19      inference('simpl_trail', [status(thm)], ['37', '104'])).
% 9.94/10.19  thf('106', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 9.94/10.19      inference('simplify_reflect-', [status(thm)], ['35', '105'])).
% 9.94/10.19  thf('107', plain,
% 9.94/10.19      (![X15 : $i, X16 : $i]:
% 9.94/10.19         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 9.94/10.19          | ((k1_relat_1 @ (k7_relat_1 @ X16 @ X15)) = (X15))
% 9.94/10.19          | ~ (v1_relat_1 @ X16))),
% 9.94/10.19      inference('cnf', [status(esa)], [t91_relat_1])).
% 9.94/10.19  thf('108', plain,
% 9.94/10.19      (![X0 : $i]:
% 9.94/10.19         (~ (r1_tarski @ X0 @ sk_A)
% 9.94/10.19          | ~ (v1_relat_1 @ sk_D)
% 9.94/10.19          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 9.94/10.19      inference('sup-', [status(thm)], ['106', '107'])).
% 9.94/10.19  thf('109', plain,
% 9.94/10.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.19  thf(cc1_relset_1, axiom,
% 9.94/10.19    (![A:$i,B:$i,C:$i]:
% 9.94/10.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.94/10.19       ( v1_relat_1 @ C ) ))).
% 9.94/10.19  thf('110', plain,
% 9.94/10.19      (![X17 : $i, X18 : $i, X19 : $i]:
% 9.94/10.19         ((v1_relat_1 @ X17)
% 9.94/10.19          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 9.94/10.19      inference('cnf', [status(esa)], [cc1_relset_1])).
% 9.94/10.19  thf('111', plain, ((v1_relat_1 @ sk_D)),
% 9.94/10.19      inference('sup-', [status(thm)], ['109', '110'])).
% 9.94/10.19  thf('112', plain,
% 9.94/10.19      (![X0 : $i]:
% 9.94/10.19         (~ (r1_tarski @ X0 @ sk_A)
% 9.94/10.19          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 9.94/10.19      inference('demod', [status(thm)], ['108', '111'])).
% 9.94/10.19  thf('113', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 9.94/10.19      inference('sup-', [status(thm)], ['16', '112'])).
% 9.94/10.19  thf('114', plain,
% 9.94/10.19      (![X13 : $i, X14 : $i]:
% 9.94/10.19         ((r1_tarski @ (k7_relat_1 @ X13 @ X14) @ X13) | ~ (v1_relat_1 @ X13))),
% 9.94/10.19      inference('cnf', [status(esa)], [t88_relat_1])).
% 9.94/10.19  thf('115', plain,
% 9.94/10.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.94/10.19  thf(t4_relset_1, axiom,
% 9.94/10.19    (![A:$i,B:$i,C:$i,D:$i]:
% 9.94/10.19     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 9.94/10.19       ( ( r1_tarski @ A @ D ) =>
% 9.94/10.19         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 9.94/10.19  thf('116', plain,
% 9.94/10.19      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 9.94/10.19         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 9.94/10.19          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 9.94/10.19          | ~ (r1_tarski @ X27 @ X30))),
% 9.94/10.19      inference('cnf', [status(esa)], [t4_relset_1])).
% 9.94/10.19  thf('117', plain,
% 9.94/10.19      (![X0 : $i]:
% 9.94/10.19         (~ (r1_tarski @ X0 @ sk_D)
% 9.94/10.19          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 9.94/10.19      inference('sup-', [status(thm)], ['115', '116'])).
% 9.94/10.19  thf('118', plain,
% 9.94/10.19      (![X0 : $i]:
% 9.94/10.19         (~ (v1_relat_1 @ sk_D)
% 9.94/10.19          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 9.94/10.19             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 9.94/10.19      inference('sup-', [status(thm)], ['114', '117'])).
% 9.94/10.19  thf('119', plain, ((v1_relat_1 @ sk_D)),
% 9.94/10.19      inference('sup-', [status(thm)], ['109', '110'])).
% 9.94/10.19  thf('120', plain,
% 9.94/10.19      (![X0 : $i]:
% 9.94/10.19         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 9.94/10.19          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 9.94/10.19      inference('demod', [status(thm)], ['118', '119'])).
% 9.94/10.19  thf(t13_relset_1, axiom,
% 9.94/10.19    (![A:$i,B:$i,C:$i,D:$i]:
% 9.94/10.19     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 9.94/10.19       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 9.94/10.19         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 9.94/10.19  thf('121', plain,
% 9.94/10.19      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 9.94/10.19         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 9.94/10.19          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 9.94/10.19          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 9.94/10.19      inference('cnf', [status(esa)], [t13_relset_1])).
% 9.94/10.19  thf('122', plain,
% 9.94/10.19      (![X0 : $i, X1 : $i]:
% 9.94/10.19         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 9.94/10.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 9.94/10.19          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 9.94/10.19      inference('sup-', [status(thm)], ['120', '121'])).
% 9.94/10.19  thf('123', plain,
% 9.94/10.19      (![X0 : $i]:
% 9.94/10.19         (~ (r1_tarski @ sk_C @ X0)
% 9.94/10.19          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 9.94/10.19             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B))))),
% 9.94/10.19      inference('sup-', [status(thm)], ['113', '122'])).
% 9.94/10.19  thf('124', plain,
% 9.94/10.19      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 9.94/10.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 9.94/10.19      inference('sup-', [status(thm)], ['15', '123'])).
% 9.94/10.19  thf('125', plain,
% 9.94/10.19      (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 9.94/10.19      inference('demod', [status(thm)], ['13', '124'])).
% 9.94/10.19  thf('126', plain,
% 9.94/10.19      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 9.94/10.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 9.94/10.19      inference('sup-', [status(thm)], ['15', '123'])).
% 9.94/10.19  thf('127', plain,
% 9.94/10.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 9.94/10.19         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 9.94/10.19          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 9.94/10.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 9.94/10.19  thf('128', plain,
% 9.94/10.19      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C))
% 9.94/10.19         = (k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)))),
% 9.94/10.19      inference('sup-', [status(thm)], ['126', '127'])).
% 9.94/10.19  thf('129', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 9.94/10.19      inference('sup-', [status(thm)], ['16', '112'])).
% 9.94/10.19  thf('130', plain,
% 9.94/10.19      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 9.94/10.19      inference('demod', [status(thm)], ['128', '129'])).
% 9.94/10.19  thf('131', plain,
% 9.94/10.19      (![X33 : $i, X34 : $i, X35 : $i]:
% 9.94/10.19         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 9.94/10.19          | (v1_funct_2 @ X35 @ X33 @ X34)
% 9.94/10.19          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_3])).
% 9.94/10.19  thf('132', plain,
% 9.94/10.19      ((((sk_C) != (sk_C))
% 9.94/10.19        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 9.94/10.19        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 9.94/10.19      inference('sup-', [status(thm)], ['130', '131'])).
% 9.94/10.19  thf('133', plain,
% 9.94/10.19      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 9.94/10.19        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C))),
% 9.94/10.19      inference('simplify', [status(thm)], ['132'])).
% 9.94/10.19  thf('134', plain,
% 9.94/10.19      (![X31 : $i, X32 : $i]:
% 9.94/10.19         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.94/10.19  thf('135', plain,
% 9.94/10.19      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 9.94/10.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 9.94/10.19      inference('sup-', [status(thm)], ['15', '123'])).
% 9.94/10.19  thf('136', plain,
% 9.94/10.19      (![X36 : $i, X37 : $i, X38 : $i]:
% 9.94/10.19         (~ (zip_tseitin_0 @ X36 @ X37)
% 9.94/10.19          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 9.94/10.19          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 9.94/10.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 9.94/10.19  thf('137', plain,
% 9.94/10.19      (((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 9.94/10.19        | ~ (zip_tseitin_0 @ sk_B @ sk_C))),
% 9.94/10.19      inference('sup-', [status(thm)], ['135', '136'])).
% 9.94/10.19  thf('138', plain,
% 9.94/10.19      ((((sk_B) = (k1_xboole_0))
% 9.94/10.19        | (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C))),
% 9.94/10.19      inference('sup-', [status(thm)], ['134', '137'])).
% 9.94/10.19  thf('139', plain, (((sk_B) != (k1_xboole_0))),
% 9.94/10.19      inference('simpl_trail', [status(thm)], ['37', '104'])).
% 9.94/10.19  thf('140', plain,
% 9.94/10.19      ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)),
% 9.94/10.19      inference('simplify_reflect-', [status(thm)], ['138', '139'])).
% 9.94/10.19  thf('141', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 9.94/10.19      inference('demod', [status(thm)], ['133', '140'])).
% 9.94/10.19  thf('142', plain, ($false), inference('demod', [status(thm)], ['125', '141'])).
% 9.94/10.19  
% 9.94/10.19  % SZS output end Refutation
% 9.94/10.19  
% 10.06/10.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
