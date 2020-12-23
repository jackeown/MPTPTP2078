%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yfO1LP0sl7

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:38 EST 2020

% Result     : Theorem 14.08s
% Output     : Refutation 14.08s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 837 expanded)
%              Number of leaves         :   42 ( 258 expanded)
%              Depth                    :   20
%              Number of atoms          : 1422 (13952 expanded)
%              Number of equality atoms :  113 ( 860 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X39 @ X40 @ X38 @ X41 ) ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ( ( k2_partfun1 @ X43 @ X44 @ X42 @ X45 )
        = ( k7_relat_1 @ X42 @ X45 ) ) ) ),
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

thf('15',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('16',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('37',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('38',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('52',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
      | ( k1_xboole_0 = sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('61',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('62',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ( ( k2_partfun1 @ X43 @ X44 @ X42 @ X45 )
        = ( k7_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(t111_relat_1,axiom,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('64',plain,(
    ! [X18: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('68',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('69',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('70',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('71',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('72',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('73',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('74',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('75',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('76',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X18: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf('79',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('80',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('84',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('85',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','86'])).

thf('88',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('92',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('94',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['90','96'])).

thf('98',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','50','57','66','67','68','69','70','71','72','73','74','97'])).

thf('99',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('100',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['35','100'])).

thf('102',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['33','101'])).

thf('103',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('107',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['104','107'])).

thf('109',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X39 @ X40 @ X38 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('116',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('117',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('119',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('122',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['120','123'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('125',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X46 ) @ X47 )
      | ( v1_funct_2 @ X46 @ ( k1_relat_1 @ X46 ) @ X47 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('128',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('130',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['126','127','130'])).

thf('132',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['109','131'])).

thf('133',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','132'])).

thf('134',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','108'])).

thf('135',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['120','123'])).

thf('136',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X46 ) @ X47 )
      | ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X46 ) @ X47 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('139',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('140',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['134','140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['133','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yfO1LP0sl7
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:24:03 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 14.08/14.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.08/14.26  % Solved by: fo/fo7.sh
% 14.08/14.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.08/14.26  % done 10821 iterations in 13.802s
% 14.08/14.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.08/14.26  % SZS output start Refutation
% 14.08/14.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 14.08/14.26  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 14.08/14.26  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 14.08/14.26  thf(sk_B_type, type, sk_B: $i).
% 14.08/14.26  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 14.08/14.26  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 14.08/14.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 14.08/14.26  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 14.08/14.26  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 14.08/14.26  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 14.08/14.26  thf(sk_A_type, type, sk_A: $i).
% 14.08/14.26  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 14.08/14.26  thf(sk_C_type, type, sk_C: $i).
% 14.08/14.26  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 14.08/14.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.08/14.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 14.08/14.26  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 14.08/14.26  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 14.08/14.26  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 14.08/14.26  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 14.08/14.26  thf(sk_D_type, type, sk_D: $i).
% 14.08/14.26  thf(t38_funct_2, conjecture,
% 14.08/14.26    (![A:$i,B:$i,C:$i,D:$i]:
% 14.08/14.26     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 14.08/14.26         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 14.08/14.26       ( ( r1_tarski @ C @ A ) =>
% 14.08/14.26         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 14.08/14.26           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 14.08/14.26             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 14.08/14.26             ( m1_subset_1 @
% 14.08/14.26               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 14.08/14.26               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 14.08/14.26  thf(zf_stmt_0, negated_conjecture,
% 14.08/14.26    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 14.08/14.26        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 14.08/14.26            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 14.08/14.26          ( ( r1_tarski @ C @ A ) =>
% 14.08/14.26            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 14.08/14.26              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 14.08/14.26                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 14.08/14.26                ( m1_subset_1 @
% 14.08/14.26                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 14.08/14.26                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 14.08/14.26    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 14.08/14.26  thf('0', plain,
% 14.08/14.26      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 14.08/14.26        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 14.08/14.26             sk_B)
% 14.08/14.26        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 14.08/14.26             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 14.08/14.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.26  thf('1', plain,
% 14.08/14.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.08/14.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.26  thf(dt_k2_partfun1, axiom,
% 14.08/14.26    (![A:$i,B:$i,C:$i,D:$i]:
% 14.08/14.26     ( ( ( v1_funct_1 @ C ) & 
% 14.08/14.26         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 14.08/14.26       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 14.08/14.26         ( m1_subset_1 @
% 14.08/14.26           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 14.08/14.26           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 14.08/14.26  thf('2', plain,
% 14.08/14.26      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 14.08/14.26         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 14.08/14.26          | ~ (v1_funct_1 @ X38)
% 14.08/14.26          | (v1_funct_1 @ (k2_partfun1 @ X39 @ X40 @ X38 @ X41)))),
% 14.08/14.26      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 14.08/14.26  thf('3', plain,
% 14.08/14.26      (![X0 : $i]:
% 14.08/14.26         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 14.08/14.26          | ~ (v1_funct_1 @ sk_D))),
% 14.08/14.26      inference('sup-', [status(thm)], ['1', '2'])).
% 14.08/14.26  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 14.08/14.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.26  thf('5', plain,
% 14.08/14.26      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 14.08/14.26      inference('demod', [status(thm)], ['3', '4'])).
% 14.08/14.26  thf('6', plain,
% 14.08/14.26      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 14.08/14.26        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 14.08/14.26             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 14.08/14.26      inference('demod', [status(thm)], ['0', '5'])).
% 14.08/14.26  thf('7', plain,
% 14.08/14.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.08/14.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.26  thf(redefinition_k2_partfun1, axiom,
% 14.08/14.26    (![A:$i,B:$i,C:$i,D:$i]:
% 14.08/14.26     ( ( ( v1_funct_1 @ C ) & 
% 14.08/14.26         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 14.08/14.26       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 14.08/14.26  thf('8', plain,
% 14.08/14.26      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 14.08/14.26         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 14.08/14.26          | ~ (v1_funct_1 @ X42)
% 14.08/14.26          | ((k2_partfun1 @ X43 @ X44 @ X42 @ X45) = (k7_relat_1 @ X42 @ X45)))),
% 14.08/14.26      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 14.08/14.26  thf('9', plain,
% 14.08/14.26      (![X0 : $i]:
% 14.08/14.26         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 14.08/14.26          | ~ (v1_funct_1 @ sk_D))),
% 14.08/14.26      inference('sup-', [status(thm)], ['7', '8'])).
% 14.08/14.26  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 14.08/14.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.26  thf('11', plain,
% 14.08/14.26      (![X0 : $i]:
% 14.08/14.26         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 14.08/14.26      inference('demod', [status(thm)], ['9', '10'])).
% 14.08/14.26  thf('12', plain,
% 14.08/14.26      (![X0 : $i]:
% 14.08/14.26         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 14.08/14.26      inference('demod', [status(thm)], ['9', '10'])).
% 14.08/14.26  thf('13', plain,
% 14.08/14.26      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 14.08/14.26        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 14.08/14.26             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 14.08/14.26      inference('demod', [status(thm)], ['6', '11', '12'])).
% 14.08/14.26  thf('14', plain, ((r1_tarski @ sk_C @ sk_A)),
% 14.08/14.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.26  thf(d1_funct_2, axiom,
% 14.08/14.26    (![A:$i,B:$i,C:$i]:
% 14.08/14.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.08/14.26       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 14.08/14.26           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 14.08/14.26             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 14.08/14.26         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 14.08/14.26           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 14.08/14.26             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 14.08/14.26  thf(zf_stmt_1, axiom,
% 14.08/14.26    (![B:$i,A:$i]:
% 14.08/14.26     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 14.08/14.26       ( zip_tseitin_0 @ B @ A ) ))).
% 14.08/14.26  thf('15', plain,
% 14.08/14.26      (![X30 : $i, X31 : $i]:
% 14.08/14.26         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 14.08/14.26      inference('cnf', [status(esa)], [zf_stmt_1])).
% 14.08/14.26  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 14.08/14.26  thf('16', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 14.08/14.26      inference('cnf', [status(esa)], [t2_xboole_1])).
% 14.08/14.26  thf('17', plain,
% 14.08/14.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.08/14.26         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 14.08/14.26      inference('sup+', [status(thm)], ['15', '16'])).
% 14.08/14.26  thf('18', plain,
% 14.08/14.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.08/14.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.26  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 14.08/14.26  thf(zf_stmt_3, axiom,
% 14.08/14.26    (![C:$i,B:$i,A:$i]:
% 14.08/14.26     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 14.08/14.26       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 14.08/14.26  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 14.08/14.26  thf(zf_stmt_5, axiom,
% 14.08/14.26    (![A:$i,B:$i,C:$i]:
% 14.08/14.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.08/14.26       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 14.08/14.26         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 14.08/14.26           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 14.08/14.26             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 14.08/14.26  thf('19', plain,
% 14.08/14.26      (![X35 : $i, X36 : $i, X37 : $i]:
% 14.08/14.26         (~ (zip_tseitin_0 @ X35 @ X36)
% 14.08/14.26          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 14.08/14.26          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 14.08/14.26      inference('cnf', [status(esa)], [zf_stmt_5])).
% 14.08/14.26  thf('20', plain,
% 14.08/14.26      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 14.08/14.26      inference('sup-', [status(thm)], ['18', '19'])).
% 14.08/14.26  thf('21', plain,
% 14.08/14.26      (![X0 : $i]:
% 14.08/14.26         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 14.08/14.26      inference('sup-', [status(thm)], ['17', '20'])).
% 14.08/14.26  thf('22', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 14.08/14.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.26  thf('23', plain,
% 14.08/14.26      (![X32 : $i, X33 : $i, X34 : $i]:
% 14.08/14.26         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 14.08/14.26          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 14.08/14.26          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 14.08/14.26      inference('cnf', [status(esa)], [zf_stmt_3])).
% 14.08/14.26  thf('24', plain,
% 14.08/14.26      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 14.08/14.26        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 14.08/14.26      inference('sup-', [status(thm)], ['22', '23'])).
% 14.08/14.26  thf('25', plain,
% 14.08/14.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.08/14.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.26  thf(redefinition_k1_relset_1, axiom,
% 14.08/14.26    (![A:$i,B:$i,C:$i]:
% 14.08/14.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.08/14.26       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 14.08/14.26  thf('26', plain,
% 14.08/14.26      (![X27 : $i, X28 : $i, X29 : $i]:
% 14.08/14.26         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 14.08/14.26          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 14.08/14.26      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 14.08/14.26  thf('27', plain,
% 14.08/14.26      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 14.08/14.26      inference('sup-', [status(thm)], ['25', '26'])).
% 14.08/14.26  thf('28', plain,
% 14.08/14.26      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 14.08/14.26      inference('demod', [status(thm)], ['24', '27'])).
% 14.08/14.26  thf('29', plain,
% 14.08/14.26      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 14.08/14.26      inference('sup-', [status(thm)], ['21', '28'])).
% 14.08/14.26  thf('30', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 14.08/14.26      inference('cnf', [status(esa)], [t2_xboole_1])).
% 14.08/14.26  thf(d10_xboole_0, axiom,
% 14.08/14.26    (![A:$i,B:$i]:
% 14.08/14.26     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 14.08/14.26  thf('31', plain,
% 14.08/14.26      (![X0 : $i, X2 : $i]:
% 14.08/14.26         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 14.08/14.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.08/14.26  thf('32', plain,
% 14.08/14.26      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 14.08/14.26      inference('sup-', [status(thm)], ['30', '31'])).
% 14.08/14.26  thf('33', plain,
% 14.08/14.26      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((sk_B) = (k1_xboole_0)))),
% 14.08/14.26      inference('sup-', [status(thm)], ['29', '32'])).
% 14.08/14.26  thf('34', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 14.08/14.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.26  thf('35', plain,
% 14.08/14.26      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 14.08/14.26      inference('split', [status(esa)], ['34'])).
% 14.08/14.26  thf('36', plain,
% 14.08/14.26      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.26      inference('split', [status(esa)], ['34'])).
% 14.08/14.26  thf('37', plain,
% 14.08/14.26      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 14.08/14.26        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 14.08/14.26             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 14.08/14.26      inference('demod', [status(thm)], ['0', '5'])).
% 14.08/14.26  thf('38', plain,
% 14.08/14.26      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 14.08/14.26            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 14.08/14.26         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 14.08/14.26              sk_B)))
% 14.08/14.26         <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.26      inference('sup-', [status(thm)], ['36', '37'])).
% 14.08/14.26  thf(t113_zfmisc_1, axiom,
% 14.08/14.26    (![A:$i,B:$i]:
% 14.08/14.26     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 14.08/14.26       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 14.08/14.26  thf('39', plain,
% 14.08/14.26      (![X5 : $i, X6 : $i]:
% 14.08/14.26         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 14.08/14.26      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 14.08/14.26  thf('40', plain,
% 14.08/14.26      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 14.08/14.26      inference('simplify', [status(thm)], ['39'])).
% 14.08/14.26  thf('41', plain,
% 14.08/14.26      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.26      inference('split', [status(esa)], ['34'])).
% 14.08/14.26  thf('42', plain,
% 14.08/14.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.08/14.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.26  thf('43', plain,
% 14.08/14.26      (((m1_subset_1 @ sk_D @ 
% 14.08/14.26         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 14.08/14.26         <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.26      inference('sup+', [status(thm)], ['41', '42'])).
% 14.08/14.26  thf('44', plain,
% 14.08/14.26      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 14.08/14.26         <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.26      inference('sup+', [status(thm)], ['40', '43'])).
% 14.08/14.26  thf(t3_subset, axiom,
% 14.08/14.26    (![A:$i,B:$i]:
% 14.08/14.26     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 14.08/14.26  thf('45', plain,
% 14.08/14.26      (![X8 : $i, X9 : $i]:
% 14.08/14.26         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 14.08/14.26      inference('cnf', [status(esa)], [t3_subset])).
% 14.08/14.26  thf('46', plain,
% 14.08/14.26      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.26      inference('sup-', [status(thm)], ['44', '45'])).
% 14.08/14.26  thf('47', plain,
% 14.08/14.26      (![X0 : $i, X2 : $i]:
% 14.08/14.26         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 14.08/14.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.08/14.26  thf('48', plain,
% 14.08/14.26      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 14.08/14.26         <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.26      inference('sup-', [status(thm)], ['46', '47'])).
% 14.08/14.26  thf('49', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 14.08/14.26      inference('cnf', [status(esa)], [t2_xboole_1])).
% 14.08/14.26  thf('50', plain,
% 14.08/14.26      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.26      inference('demod', [status(thm)], ['48', '49'])).
% 14.08/14.26  thf('51', plain,
% 14.08/14.26      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.26      inference('split', [status(esa)], ['34'])).
% 14.08/14.26  thf('52', plain, ((r1_tarski @ sk_C @ sk_A)),
% 14.08/14.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.26  thf('53', plain,
% 14.08/14.26      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.26      inference('sup+', [status(thm)], ['51', '52'])).
% 14.08/14.27  thf('54', plain,
% 14.08/14.27      (![X0 : $i, X2 : $i]:
% 14.08/14.27         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 14.08/14.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.08/14.27  thf('55', plain,
% 14.08/14.27      (((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C))))
% 14.08/14.27         <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.27      inference('sup-', [status(thm)], ['53', '54'])).
% 14.08/14.27  thf('56', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 14.08/14.27      inference('cnf', [status(esa)], [t2_xboole_1])).
% 14.08/14.27  thf('57', plain,
% 14.08/14.27      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.27      inference('demod', [status(thm)], ['55', '56'])).
% 14.08/14.27  thf('58', plain,
% 14.08/14.27      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.27      inference('demod', [status(thm)], ['48', '49'])).
% 14.08/14.27  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 14.08/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.27  thf('60', plain,
% 14.08/14.27      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.27      inference('sup+', [status(thm)], ['58', '59'])).
% 14.08/14.27  thf(t4_subset_1, axiom,
% 14.08/14.27    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 14.08/14.27  thf('61', plain,
% 14.08/14.27      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 14.08/14.27      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.08/14.27  thf('62', plain,
% 14.08/14.27      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 14.08/14.27         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 14.08/14.27          | ~ (v1_funct_1 @ X42)
% 14.08/14.27          | ((k2_partfun1 @ X43 @ X44 @ X42 @ X45) = (k7_relat_1 @ X42 @ X45)))),
% 14.08/14.27      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 14.08/14.27  thf('63', plain,
% 14.08/14.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.08/14.27         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 14.08/14.27            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 14.08/14.27          | ~ (v1_funct_1 @ k1_xboole_0))),
% 14.08/14.27      inference('sup-', [status(thm)], ['61', '62'])).
% 14.08/14.27  thf(t111_relat_1, axiom,
% 14.08/14.27    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 14.08/14.27  thf('64', plain,
% 14.08/14.27      (![X18 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X18) = (k1_xboole_0))),
% 14.08/14.27      inference('cnf', [status(esa)], [t111_relat_1])).
% 14.08/14.27  thf('65', plain,
% 14.08/14.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.08/14.27         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 14.08/14.27          | ~ (v1_funct_1 @ k1_xboole_0))),
% 14.08/14.27      inference('demod', [status(thm)], ['63', '64'])).
% 14.08/14.27  thf('66', plain,
% 14.08/14.27      ((![X0 : $i, X1 : $i, X2 : $i]:
% 14.08/14.27          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 14.08/14.27         <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.27      inference('sup-', [status(thm)], ['60', '65'])).
% 14.08/14.27  thf('67', plain,
% 14.08/14.27      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.27      inference('demod', [status(thm)], ['55', '56'])).
% 14.08/14.27  thf('68', plain,
% 14.08/14.27      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 14.08/14.27      inference('simplify', [status(thm)], ['39'])).
% 14.08/14.27  thf('69', plain,
% 14.08/14.27      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 14.08/14.27      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.08/14.27  thf('70', plain,
% 14.08/14.27      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.27      inference('split', [status(esa)], ['34'])).
% 14.08/14.27  thf('71', plain,
% 14.08/14.27      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.27      inference('demod', [status(thm)], ['48', '49'])).
% 14.08/14.27  thf('72', plain,
% 14.08/14.27      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.27      inference('demod', [status(thm)], ['55', '56'])).
% 14.08/14.27  thf('73', plain,
% 14.08/14.27      ((![X0 : $i, X1 : $i, X2 : $i]:
% 14.08/14.27          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 14.08/14.27         <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.27      inference('sup-', [status(thm)], ['60', '65'])).
% 14.08/14.27  thf('74', plain,
% 14.08/14.27      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 14.08/14.27      inference('demod', [status(thm)], ['55', '56'])).
% 14.08/14.27  thf('75', plain,
% 14.08/14.27      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 14.08/14.27      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.08/14.27  thf('76', plain,
% 14.08/14.27      (![X27 : $i, X28 : $i, X29 : $i]:
% 14.08/14.27         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 14.08/14.27          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 14.08/14.27      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 14.08/14.27  thf('77', plain,
% 14.08/14.27      (![X0 : $i, X1 : $i]:
% 14.08/14.27         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 14.08/14.27      inference('sup-', [status(thm)], ['75', '76'])).
% 14.08/14.27  thf('78', plain,
% 14.08/14.27      (![X18 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X18) = (k1_xboole_0))),
% 14.08/14.27      inference('cnf', [status(esa)], [t111_relat_1])).
% 14.08/14.27  thf('79', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 14.08/14.27      inference('cnf', [status(esa)], [t2_xboole_1])).
% 14.08/14.27  thf(t91_relat_1, axiom,
% 14.08/14.27    (![A:$i,B:$i]:
% 14.08/14.27     ( ( v1_relat_1 @ B ) =>
% 14.08/14.27       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 14.08/14.27         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 14.08/14.27  thf('80', plain,
% 14.08/14.27      (![X19 : $i, X20 : $i]:
% 14.08/14.27         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 14.08/14.27          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 14.08/14.27          | ~ (v1_relat_1 @ X20))),
% 14.08/14.27      inference('cnf', [status(esa)], [t91_relat_1])).
% 14.08/14.27  thf('81', plain,
% 14.08/14.27      (![X0 : $i]:
% 14.08/14.27         (~ (v1_relat_1 @ X0)
% 14.08/14.27          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 14.08/14.27      inference('sup-', [status(thm)], ['79', '80'])).
% 14.08/14.27  thf('82', plain,
% 14.08/14.27      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 14.08/14.27        | ~ (v1_relat_1 @ k1_xboole_0))),
% 14.08/14.27      inference('sup+', [status(thm)], ['78', '81'])).
% 14.08/14.27  thf('83', plain,
% 14.08/14.27      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 14.08/14.27      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.08/14.27  thf(cc1_relset_1, axiom,
% 14.08/14.27    (![A:$i,B:$i,C:$i]:
% 14.08/14.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.08/14.27       ( v1_relat_1 @ C ) ))).
% 14.08/14.27  thf('84', plain,
% 14.08/14.27      (![X21 : $i, X22 : $i, X23 : $i]:
% 14.08/14.27         ((v1_relat_1 @ X21)
% 14.08/14.27          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 14.08/14.27      inference('cnf', [status(esa)], [cc1_relset_1])).
% 14.08/14.27  thf('85', plain, ((v1_relat_1 @ k1_xboole_0)),
% 14.08/14.27      inference('sup-', [status(thm)], ['83', '84'])).
% 14.08/14.27  thf('86', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.08/14.27      inference('demod', [status(thm)], ['82', '85'])).
% 14.08/14.27  thf('87', plain,
% 14.08/14.27      (![X0 : $i, X1 : $i]:
% 14.08/14.27         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 14.08/14.27      inference('demod', [status(thm)], ['77', '86'])).
% 14.08/14.27  thf('88', plain,
% 14.08/14.27      (![X32 : $i, X33 : $i, X34 : $i]:
% 14.08/14.27         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 14.08/14.27          | (v1_funct_2 @ X34 @ X32 @ X33)
% 14.08/14.27          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 14.08/14.27      inference('cnf', [status(esa)], [zf_stmt_3])).
% 14.08/14.27  thf('89', plain,
% 14.08/14.27      (![X0 : $i, X1 : $i]:
% 14.08/14.27         (((X1) != (k1_xboole_0))
% 14.08/14.27          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 14.08/14.27          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 14.08/14.27      inference('sup-', [status(thm)], ['87', '88'])).
% 14.08/14.27  thf('90', plain,
% 14.08/14.27      (![X0 : $i]:
% 14.08/14.27         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 14.08/14.27          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 14.08/14.27      inference('simplify', [status(thm)], ['89'])).
% 14.08/14.27  thf('91', plain,
% 14.08/14.27      (![X30 : $i, X31 : $i]:
% 14.08/14.27         ((zip_tseitin_0 @ X30 @ X31) | ((X31) != (k1_xboole_0)))),
% 14.08/14.27      inference('cnf', [status(esa)], [zf_stmt_1])).
% 14.08/14.27  thf('92', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 14.08/14.27      inference('simplify', [status(thm)], ['91'])).
% 14.08/14.27  thf('93', plain,
% 14.08/14.27      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 14.08/14.27      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.08/14.27  thf('94', plain,
% 14.08/14.27      (![X35 : $i, X36 : $i, X37 : $i]:
% 14.08/14.27         (~ (zip_tseitin_0 @ X35 @ X36)
% 14.08/14.27          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 14.08/14.27          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 14.08/14.27      inference('cnf', [status(esa)], [zf_stmt_5])).
% 14.08/14.27  thf('95', plain,
% 14.08/14.27      (![X0 : $i, X1 : $i]:
% 14.08/14.27         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 14.08/14.27      inference('sup-', [status(thm)], ['93', '94'])).
% 14.08/14.27  thf('96', plain,
% 14.08/14.27      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 14.08/14.27      inference('sup-', [status(thm)], ['92', '95'])).
% 14.08/14.27  thf('97', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 14.08/14.27      inference('demod', [status(thm)], ['90', '96'])).
% 14.08/14.27  thf('98', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 14.08/14.27      inference('demod', [status(thm)],
% 14.08/14.27                ['38', '50', '57', '66', '67', '68', '69', '70', '71', '72', 
% 14.08/14.27                 '73', '74', '97'])).
% 14.08/14.27  thf('99', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 14.08/14.27      inference('split', [status(esa)], ['34'])).
% 14.08/14.27  thf('100', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 14.08/14.27      inference('sat_resolution*', [status(thm)], ['98', '99'])).
% 14.08/14.27  thf('101', plain, (((sk_B) != (k1_xboole_0))),
% 14.08/14.27      inference('simpl_trail', [status(thm)], ['35', '100'])).
% 14.08/14.27  thf('102', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 14.08/14.27      inference('simplify_reflect-', [status(thm)], ['33', '101'])).
% 14.08/14.27  thf('103', plain,
% 14.08/14.27      (![X19 : $i, X20 : $i]:
% 14.08/14.27         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 14.08/14.27          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 14.08/14.27          | ~ (v1_relat_1 @ X20))),
% 14.08/14.27      inference('cnf', [status(esa)], [t91_relat_1])).
% 14.08/14.27  thf('104', plain,
% 14.08/14.27      (![X0 : $i]:
% 14.08/14.27         (~ (r1_tarski @ X0 @ sk_A)
% 14.08/14.27          | ~ (v1_relat_1 @ sk_D)
% 14.08/14.27          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 14.08/14.27      inference('sup-', [status(thm)], ['102', '103'])).
% 14.08/14.27  thf('105', plain,
% 14.08/14.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.08/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.27  thf('106', plain,
% 14.08/14.27      (![X21 : $i, X22 : $i, X23 : $i]:
% 14.08/14.27         ((v1_relat_1 @ X21)
% 14.08/14.27          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 14.08/14.27      inference('cnf', [status(esa)], [cc1_relset_1])).
% 14.08/14.27  thf('107', plain, ((v1_relat_1 @ sk_D)),
% 14.08/14.27      inference('sup-', [status(thm)], ['105', '106'])).
% 14.08/14.27  thf('108', plain,
% 14.08/14.27      (![X0 : $i]:
% 14.08/14.27         (~ (r1_tarski @ X0 @ sk_A)
% 14.08/14.27          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 14.08/14.27      inference('demod', [status(thm)], ['104', '107'])).
% 14.08/14.27  thf('109', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 14.08/14.27      inference('sup-', [status(thm)], ['14', '108'])).
% 14.08/14.27  thf('110', plain,
% 14.08/14.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.08/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.27  thf('111', plain,
% 14.08/14.27      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 14.08/14.27         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 14.08/14.27          | ~ (v1_funct_1 @ X38)
% 14.08/14.27          | (m1_subset_1 @ (k2_partfun1 @ X39 @ X40 @ X38 @ X41) @ 
% 14.08/14.27             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 14.08/14.27      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 14.08/14.27  thf('112', plain,
% 14.08/14.27      (![X0 : $i]:
% 14.08/14.27         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 14.08/14.27           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 14.08/14.27          | ~ (v1_funct_1 @ sk_D))),
% 14.08/14.27      inference('sup-', [status(thm)], ['110', '111'])).
% 14.08/14.27  thf('113', plain, ((v1_funct_1 @ sk_D)),
% 14.08/14.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.08/14.27  thf('114', plain,
% 14.08/14.27      (![X0 : $i]:
% 14.08/14.27         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 14.08/14.27          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.08/14.27      inference('demod', [status(thm)], ['112', '113'])).
% 14.08/14.27  thf('115', plain,
% 14.08/14.27      (![X0 : $i]:
% 14.08/14.27         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 14.08/14.27      inference('demod', [status(thm)], ['9', '10'])).
% 14.08/14.27  thf('116', plain,
% 14.08/14.27      (![X0 : $i]:
% 14.08/14.27         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 14.08/14.27          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.08/14.27      inference('demod', [status(thm)], ['114', '115'])).
% 14.08/14.27  thf(cc2_relset_1, axiom,
% 14.08/14.27    (![A:$i,B:$i,C:$i]:
% 14.08/14.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.08/14.27       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 14.08/14.27  thf('117', plain,
% 14.08/14.27      (![X24 : $i, X25 : $i, X26 : $i]:
% 14.08/14.27         ((v5_relat_1 @ X24 @ X26)
% 14.08/14.27          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 14.08/14.27      inference('cnf', [status(esa)], [cc2_relset_1])).
% 14.08/14.27  thf('118', plain,
% 14.08/14.27      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 14.08/14.27      inference('sup-', [status(thm)], ['116', '117'])).
% 14.08/14.27  thf(d19_relat_1, axiom,
% 14.08/14.27    (![A:$i,B:$i]:
% 14.08/14.27     ( ( v1_relat_1 @ B ) =>
% 14.08/14.27       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 14.08/14.27  thf('119', plain,
% 14.08/14.27      (![X14 : $i, X15 : $i]:
% 14.08/14.27         (~ (v5_relat_1 @ X14 @ X15)
% 14.08/14.27          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 14.08/14.27          | ~ (v1_relat_1 @ X14))),
% 14.08/14.27      inference('cnf', [status(esa)], [d19_relat_1])).
% 14.08/14.27  thf('120', plain,
% 14.08/14.27      (![X0 : $i]:
% 14.08/14.27         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 14.08/14.27          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 14.08/14.27      inference('sup-', [status(thm)], ['118', '119'])).
% 14.08/14.27  thf('121', plain,
% 14.08/14.27      (![X0 : $i]:
% 14.08/14.27         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 14.08/14.27          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.08/14.27      inference('demod', [status(thm)], ['114', '115'])).
% 14.08/14.27  thf('122', plain,
% 14.08/14.27      (![X21 : $i, X22 : $i, X23 : $i]:
% 14.08/14.27         ((v1_relat_1 @ X21)
% 14.08/14.27          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 14.08/14.27      inference('cnf', [status(esa)], [cc1_relset_1])).
% 14.08/14.27  thf('123', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 14.08/14.27      inference('sup-', [status(thm)], ['121', '122'])).
% 14.08/14.27  thf('124', plain,
% 14.08/14.27      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 14.08/14.27      inference('demod', [status(thm)], ['120', '123'])).
% 14.08/14.27  thf(t4_funct_2, axiom,
% 14.08/14.27    (![A:$i,B:$i]:
% 14.08/14.27     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 14.08/14.27       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 14.08/14.27         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 14.08/14.27           ( m1_subset_1 @
% 14.08/14.27             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 14.08/14.27  thf('125', plain,
% 14.08/14.27      (![X46 : $i, X47 : $i]:
% 14.08/14.27         (~ (r1_tarski @ (k2_relat_1 @ X46) @ X47)
% 14.08/14.27          | (v1_funct_2 @ X46 @ (k1_relat_1 @ X46) @ X47)
% 14.08/14.27          | ~ (v1_funct_1 @ X46)
% 14.08/14.27          | ~ (v1_relat_1 @ X46))),
% 14.08/14.27      inference('cnf', [status(esa)], [t4_funct_2])).
% 14.08/14.27  thf('126', plain,
% 14.08/14.27      (![X0 : $i]:
% 14.08/14.27         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 14.08/14.27          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 14.08/14.27          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 14.08/14.27             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 14.08/14.27      inference('sup-', [status(thm)], ['124', '125'])).
% 14.08/14.27  thf('127', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 14.08/14.27      inference('sup-', [status(thm)], ['121', '122'])).
% 14.08/14.27  thf('128', plain,
% 14.08/14.27      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 14.08/14.27      inference('demod', [status(thm)], ['3', '4'])).
% 14.08/14.27  thf('129', plain,
% 14.08/14.27      (![X0 : $i]:
% 14.08/14.27         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 14.08/14.27      inference('demod', [status(thm)], ['9', '10'])).
% 14.08/14.27  thf('130', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 14.08/14.27      inference('demod', [status(thm)], ['128', '129'])).
% 14.08/14.27  thf('131', plain,
% 14.08/14.27      (![X0 : $i]:
% 14.08/14.27         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 14.08/14.27          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 14.08/14.27      inference('demod', [status(thm)], ['126', '127', '130'])).
% 14.08/14.27  thf('132', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 14.08/14.27      inference('sup+', [status(thm)], ['109', '131'])).
% 14.08/14.27  thf('133', plain,
% 14.08/14.27      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 14.08/14.27          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 14.08/14.27      inference('demod', [status(thm)], ['13', '132'])).
% 14.08/14.27  thf('134', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 14.08/14.27      inference('sup-', [status(thm)], ['14', '108'])).
% 14.08/14.27  thf('135', plain,
% 14.08/14.27      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 14.08/14.27      inference('demod', [status(thm)], ['120', '123'])).
% 14.08/14.27  thf('136', plain,
% 14.08/14.27      (![X46 : $i, X47 : $i]:
% 14.08/14.27         (~ (r1_tarski @ (k2_relat_1 @ X46) @ X47)
% 14.08/14.27          | (m1_subset_1 @ X46 @ 
% 14.08/14.27             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X46) @ X47)))
% 14.08/14.27          | ~ (v1_funct_1 @ X46)
% 14.08/14.27          | ~ (v1_relat_1 @ X46))),
% 14.08/14.27      inference('cnf', [status(esa)], [t4_funct_2])).
% 14.08/14.27  thf('137', plain,
% 14.08/14.27      (![X0 : $i]:
% 14.08/14.27         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 14.08/14.27          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 14.08/14.27          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 14.08/14.27             (k1_zfmisc_1 @ 
% 14.08/14.27              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 14.08/14.27      inference('sup-', [status(thm)], ['135', '136'])).
% 14.08/14.27  thf('138', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 14.08/14.27      inference('sup-', [status(thm)], ['121', '122'])).
% 14.08/14.27  thf('139', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 14.08/14.27      inference('demod', [status(thm)], ['128', '129'])).
% 14.08/14.27  thf('140', plain,
% 14.08/14.27      (![X0 : $i]:
% 14.08/14.27         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 14.08/14.27          (k1_zfmisc_1 @ 
% 14.08/14.27           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 14.08/14.27      inference('demod', [status(thm)], ['137', '138', '139'])).
% 14.08/14.27  thf('141', plain,
% 14.08/14.27      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 14.08/14.27        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 14.08/14.27      inference('sup+', [status(thm)], ['134', '140'])).
% 14.08/14.27  thf('142', plain, ($false), inference('demod', [status(thm)], ['133', '141'])).
% 14.08/14.27  
% 14.08/14.27  % SZS output end Refutation
% 14.08/14.27  
% 14.08/14.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
