%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TJQSOHqyC0

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:40 EST 2020

% Result     : Theorem 52.27s
% Output     : Refutation 52.27s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 799 expanded)
%              Number of leaves         :   43 ( 248 expanded)
%              Depth                    :   19
%              Number of atoms          : 1387 (13714 expanded)
%              Number of equality atoms :  114 ( 822 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('16',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
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

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('31',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['32'])).

thf('34',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('35',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_B ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('37',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['29','37'])).

thf('39',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('52',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf('55',plain,
    ( ( ~ ( m1_subset_1 @ ( k7_relat_1 @ k1_xboole_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('57',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
      | ( k1_xboole_0 = sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('62',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('64',plain,(
    ! [X24: $i] :
      ( ( ( k7_relat_1 @ X24 @ ( k1_relat_1 @ X24 ) )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('65',plain,
    ( ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('66',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('67',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('68',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('71',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('72',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('73',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('74',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('75',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','68'])).

thf('76',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('77',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('78',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('86',plain,(
    ! [X36: $i] :
      ( zip_tseitin_0 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('88',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['84','90'])).

thf('92',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['55','62','69','70','71','72','73','74','75','76','91'])).

thf('93',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('94',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['41','94'])).

thf('96',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['39','95'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('97',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('101',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X45 @ X46 @ X44 @ X47 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('110',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('111',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v5_relat_1 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('113',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v5_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('116',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['114','117'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('119',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X52 ) @ X53 )
      | ( v1_funct_2 @ X52 @ ( k1_relat_1 @ X52 ) @ X53 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('122',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('124',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['120','121','124'])).

thf('126',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['103','125'])).

thf('127',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','126'])).

thf('128',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','102'])).

thf('129',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['114','117'])).

thf('130',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X52 ) @ X53 )
      | ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X52 ) @ X53 ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('133',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('134',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['128','134'])).

thf('136',plain,(
    $false ),
    inference(demod,[status(thm)],['127','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TJQSOHqyC0
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:27:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 52.27/52.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 52.27/52.53  % Solved by: fo/fo7.sh
% 52.27/52.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 52.27/52.53  % done 25502 iterations in 52.057s
% 52.27/52.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 52.27/52.53  % SZS output start Refutation
% 52.27/52.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 52.27/52.53  thf(sk_D_type, type, sk_D: $i).
% 52.27/52.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 52.27/52.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 52.27/52.53  thf(sk_B_type, type, sk_B: $i).
% 52.27/52.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 52.27/52.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 52.27/52.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 52.27/52.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 52.27/52.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 52.27/52.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 52.27/52.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 52.27/52.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 52.27/52.53  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 52.27/52.53  thf(sk_A_type, type, sk_A: $i).
% 52.27/52.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 52.27/52.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 52.27/52.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 52.27/52.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 52.27/52.53  thf(sk_C_type, type, sk_C: $i).
% 52.27/52.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 52.27/52.53  thf(t38_funct_2, conjecture,
% 52.27/52.53    (![A:$i,B:$i,C:$i,D:$i]:
% 52.27/52.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 52.27/52.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 52.27/52.53       ( ( r1_tarski @ C @ A ) =>
% 52.27/52.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 52.27/52.53           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 52.27/52.53             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 52.27/52.53             ( m1_subset_1 @
% 52.27/52.53               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 52.27/52.53               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 52.27/52.53  thf(zf_stmt_0, negated_conjecture,
% 52.27/52.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 52.27/52.53        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 52.27/52.53            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 52.27/52.53          ( ( r1_tarski @ C @ A ) =>
% 52.27/52.53            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 52.27/52.53              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 52.27/52.53                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 52.27/52.53                ( m1_subset_1 @
% 52.27/52.53                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 52.27/52.53                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 52.27/52.53    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 52.27/52.53  thf('0', plain,
% 52.27/52.53      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 52.27/52.53        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 52.27/52.53             sk_B)
% 52.27/52.53        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 52.27/52.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.27/52.53  thf('1', plain,
% 52.27/52.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.27/52.53  thf(dt_k2_partfun1, axiom,
% 52.27/52.53    (![A:$i,B:$i,C:$i,D:$i]:
% 52.27/52.53     ( ( ( v1_funct_1 @ C ) & 
% 52.27/52.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 52.27/52.53       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 52.27/52.53         ( m1_subset_1 @
% 52.27/52.53           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 52.27/52.53           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 52.27/52.53  thf('2', plain,
% 52.27/52.53      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 52.27/52.53         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 52.27/52.53          | ~ (v1_funct_1 @ X44)
% 52.27/52.53          | (v1_funct_1 @ (k2_partfun1 @ X45 @ X46 @ X44 @ X47)))),
% 52.27/52.53      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 52.27/52.53  thf('3', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 52.27/52.53          | ~ (v1_funct_1 @ sk_D))),
% 52.27/52.53      inference('sup-', [status(thm)], ['1', '2'])).
% 52.27/52.53  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.27/52.53  thf('5', plain,
% 52.27/52.53      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 52.27/52.53      inference('demod', [status(thm)], ['3', '4'])).
% 52.27/52.53  thf('6', plain,
% 52.27/52.53      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 52.27/52.53        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 52.27/52.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 52.27/52.53      inference('demod', [status(thm)], ['0', '5'])).
% 52.27/52.53  thf('7', plain,
% 52.27/52.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.27/52.53  thf(redefinition_k2_partfun1, axiom,
% 52.27/52.53    (![A:$i,B:$i,C:$i,D:$i]:
% 52.27/52.53     ( ( ( v1_funct_1 @ C ) & 
% 52.27/52.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 52.27/52.53       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 52.27/52.53  thf('8', plain,
% 52.27/52.53      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 52.27/52.53         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 52.27/52.53          | ~ (v1_funct_1 @ X48)
% 52.27/52.53          | ((k2_partfun1 @ X49 @ X50 @ X48 @ X51) = (k7_relat_1 @ X48 @ X51)))),
% 52.27/52.53      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 52.27/52.53  thf('9', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 52.27/52.53          | ~ (v1_funct_1 @ sk_D))),
% 52.27/52.53      inference('sup-', [status(thm)], ['7', '8'])).
% 52.27/52.53  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.27/52.53  thf('11', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 52.27/52.53      inference('demod', [status(thm)], ['9', '10'])).
% 52.27/52.53  thf('12', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 52.27/52.53      inference('demod', [status(thm)], ['9', '10'])).
% 52.27/52.53  thf('13', plain,
% 52.27/52.53      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 52.27/52.53        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 52.27/52.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 52.27/52.53      inference('demod', [status(thm)], ['6', '11', '12'])).
% 52.27/52.53  thf('14', plain, ((r1_tarski @ sk_C @ sk_A)),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.27/52.53  thf(d1_funct_2, axiom,
% 52.27/52.53    (![A:$i,B:$i,C:$i]:
% 52.27/52.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 52.27/52.53       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 52.27/52.53           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 52.27/52.53             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 52.27/52.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 52.27/52.53           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 52.27/52.53             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 52.27/52.53  thf(zf_stmt_1, axiom,
% 52.27/52.53    (![B:$i,A:$i]:
% 52.27/52.53     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 52.27/52.53       ( zip_tseitin_0 @ B @ A ) ))).
% 52.27/52.53  thf('15', plain,
% 52.27/52.53      (![X36 : $i, X37 : $i]:
% 52.27/52.53         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 52.27/52.53  thf(t60_relat_1, axiom,
% 52.27/52.53    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 52.27/52.53     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 52.27/52.53  thf('16', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 52.27/52.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 52.27/52.53  thf('17', plain,
% 52.27/52.53      (![X0 : $i, X1 : $i]:
% 52.27/52.53         (((k1_relat_1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X1))),
% 52.27/52.53      inference('sup+', [status(thm)], ['15', '16'])).
% 52.27/52.53  thf('18', plain,
% 52.27/52.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.27/52.53  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 52.27/52.53  thf(zf_stmt_3, axiom,
% 52.27/52.53    (![C:$i,B:$i,A:$i]:
% 52.27/52.53     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 52.27/52.53       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 52.27/52.53  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 52.27/52.53  thf(zf_stmt_5, axiom,
% 52.27/52.53    (![A:$i,B:$i,C:$i]:
% 52.27/52.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 52.27/52.53       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 52.27/52.53         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 52.27/52.53           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 52.27/52.53             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 52.27/52.53  thf('19', plain,
% 52.27/52.53      (![X41 : $i, X42 : $i, X43 : $i]:
% 52.27/52.53         (~ (zip_tseitin_0 @ X41 @ X42)
% 52.27/52.53          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 52.27/52.53          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 52.27/52.53  thf('20', plain,
% 52.27/52.53      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 52.27/52.53      inference('sup-', [status(thm)], ['18', '19'])).
% 52.27/52.53  thf('21', plain,
% 52.27/52.53      ((((k1_relat_1 @ sk_B) = (k1_xboole_0))
% 52.27/52.53        | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 52.27/52.53      inference('sup-', [status(thm)], ['17', '20'])).
% 52.27/52.53  thf('22', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.27/52.53  thf('23', plain,
% 52.27/52.53      (![X38 : $i, X39 : $i, X40 : $i]:
% 52.27/52.53         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 52.27/52.53          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 52.27/52.53          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 52.27/52.53  thf('24', plain,
% 52.27/52.53      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 52.27/52.53        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 52.27/52.53      inference('sup-', [status(thm)], ['22', '23'])).
% 52.27/52.53  thf('25', plain,
% 52.27/52.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.27/52.53  thf(redefinition_k1_relset_1, axiom,
% 52.27/52.53    (![A:$i,B:$i,C:$i]:
% 52.27/52.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 52.27/52.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 52.27/52.53  thf('26', plain,
% 52.27/52.53      (![X33 : $i, X34 : $i, X35 : $i]:
% 52.27/52.53         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 52.27/52.53          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 52.27/52.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 52.27/52.53  thf('27', plain,
% 52.27/52.53      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 52.27/52.53      inference('sup-', [status(thm)], ['25', '26'])).
% 52.27/52.53  thf('28', plain,
% 52.27/52.53      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 52.27/52.53      inference('demod', [status(thm)], ['24', '27'])).
% 52.27/52.53  thf('29', plain,
% 52.27/52.53      ((((k1_relat_1 @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 52.27/52.53      inference('sup-', [status(thm)], ['21', '28'])).
% 52.27/52.53  thf('30', plain,
% 52.27/52.53      (![X0 : $i, X1 : $i]:
% 52.27/52.53         (((k1_relat_1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X1))),
% 52.27/52.53      inference('sup+', [status(thm)], ['15', '16'])).
% 52.27/52.53  thf('31', plain,
% 52.27/52.53      (![X36 : $i, X37 : $i]:
% 52.27/52.53         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 52.27/52.53  thf('32', plain,
% 52.27/52.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.27/52.53         (((X1) = (k1_relat_1 @ X0))
% 52.27/52.53          | (zip_tseitin_0 @ X0 @ X3)
% 52.27/52.53          | (zip_tseitin_0 @ X1 @ X2))),
% 52.27/52.53      inference('sup+', [status(thm)], ['30', '31'])).
% 52.27/52.53  thf('33', plain,
% 52.27/52.53      (![X0 : $i, X1 : $i]:
% 52.27/52.53         ((zip_tseitin_0 @ X1 @ X0) | ((X1) = (k1_relat_1 @ X1)))),
% 52.27/52.53      inference('eq_fact', [status(thm)], ['32'])).
% 52.27/52.53  thf('34', plain,
% 52.27/52.53      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 52.27/52.53      inference('sup-', [status(thm)], ['18', '19'])).
% 52.27/52.53  thf('35', plain,
% 52.27/52.53      ((((sk_B) = (k1_relat_1 @ sk_B)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 52.27/52.53      inference('sup-', [status(thm)], ['33', '34'])).
% 52.27/52.53  thf('36', plain,
% 52.27/52.53      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 52.27/52.53      inference('demod', [status(thm)], ['24', '27'])).
% 52.27/52.53  thf('37', plain,
% 52.27/52.53      ((((sk_B) = (k1_relat_1 @ sk_B)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 52.27/52.53      inference('sup-', [status(thm)], ['35', '36'])).
% 52.27/52.53  thf('38', plain,
% 52.27/52.53      ((((sk_B) = (k1_xboole_0))
% 52.27/52.53        | ((sk_A) = (k1_relat_1 @ sk_D))
% 52.27/52.53        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 52.27/52.53      inference('sup+', [status(thm)], ['29', '37'])).
% 52.27/52.53  thf('39', plain,
% 52.27/52.53      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((sk_B) = (k1_xboole_0)))),
% 52.27/52.53      inference('simplify', [status(thm)], ['38'])).
% 52.27/52.53  thf('40', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.27/52.53  thf('41', plain,
% 52.27/52.53      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 52.27/52.53      inference('split', [status(esa)], ['40'])).
% 52.27/52.53  thf(t113_zfmisc_1, axiom,
% 52.27/52.53    (![A:$i,B:$i]:
% 52.27/52.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 52.27/52.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 52.27/52.53  thf('42', plain,
% 52.27/52.53      (![X8 : $i, X9 : $i]:
% 52.27/52.53         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 52.27/52.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 52.27/52.53  thf('43', plain,
% 52.27/52.53      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 52.27/52.53      inference('simplify', [status(thm)], ['42'])).
% 52.27/52.53  thf('44', plain,
% 52.27/52.53      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.27/52.53      inference('split', [status(esa)], ['40'])).
% 52.27/52.53  thf('45', plain,
% 52.27/52.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.27/52.53  thf('46', plain,
% 52.27/52.53      (((m1_subset_1 @ sk_D @ 
% 52.27/52.53         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 52.27/52.53         <= ((((sk_A) = (k1_xboole_0))))),
% 52.27/52.53      inference('sup+', [status(thm)], ['44', '45'])).
% 52.27/52.53  thf('47', plain,
% 52.27/52.53      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 52.27/52.53         <= ((((sk_A) = (k1_xboole_0))))),
% 52.27/52.53      inference('sup+', [status(thm)], ['43', '46'])).
% 52.27/52.53  thf(t3_subset, axiom,
% 52.27/52.53    (![A:$i,B:$i]:
% 52.27/52.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 52.27/52.53  thf('48', plain,
% 52.27/52.53      (![X11 : $i, X12 : $i]:
% 52.27/52.53         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 52.27/52.53      inference('cnf', [status(esa)], [t3_subset])).
% 52.27/52.53  thf('49', plain,
% 52.27/52.53      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 52.27/52.53      inference('sup-', [status(thm)], ['47', '48'])).
% 52.27/52.53  thf(d10_xboole_0, axiom,
% 52.27/52.53    (![A:$i,B:$i]:
% 52.27/52.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 52.27/52.53  thf('50', plain,
% 52.27/52.53      (![X0 : $i, X2 : $i]:
% 52.27/52.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 52.27/52.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 52.27/52.53  thf('51', plain,
% 52.27/52.53      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 52.27/52.53         <= ((((sk_A) = (k1_xboole_0))))),
% 52.27/52.53      inference('sup-', [status(thm)], ['49', '50'])).
% 52.27/52.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 52.27/52.53  thf('52', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 52.27/52.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 52.27/52.53  thf('53', plain,
% 52.27/52.53      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.27/52.53      inference('demod', [status(thm)], ['51', '52'])).
% 52.27/52.53  thf('54', plain,
% 52.27/52.53      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 52.27/52.53        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 52.27/52.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 52.27/52.53      inference('demod', [status(thm)], ['6', '11', '12'])).
% 52.27/52.53  thf('55', plain,
% 52.27/52.53      (((~ (m1_subset_1 @ (k7_relat_1 @ k1_xboole_0 @ sk_C) @ 
% 52.27/52.53            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 52.27/52.53         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)))
% 52.27/52.53         <= ((((sk_A) = (k1_xboole_0))))),
% 52.27/52.53      inference('sup-', [status(thm)], ['53', '54'])).
% 52.27/52.53  thf('56', plain,
% 52.27/52.53      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.27/52.53      inference('split', [status(esa)], ['40'])).
% 52.27/52.53  thf('57', plain, ((r1_tarski @ sk_C @ sk_A)),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.27/52.53  thf('58', plain,
% 52.27/52.53      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 52.27/52.53      inference('sup+', [status(thm)], ['56', '57'])).
% 52.27/52.53  thf('59', plain,
% 52.27/52.53      (![X0 : $i, X2 : $i]:
% 52.27/52.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 52.27/52.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 52.27/52.53  thf('60', plain,
% 52.27/52.53      (((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C))))
% 52.27/52.53         <= ((((sk_A) = (k1_xboole_0))))),
% 52.27/52.53      inference('sup-', [status(thm)], ['58', '59'])).
% 52.27/52.53  thf('61', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 52.27/52.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 52.27/52.53  thf('62', plain,
% 52.27/52.53      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.27/52.53      inference('demod', [status(thm)], ['60', '61'])).
% 52.27/52.53  thf('63', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 52.27/52.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 52.27/52.53  thf(t98_relat_1, axiom,
% 52.27/52.53    (![A:$i]:
% 52.27/52.53     ( ( v1_relat_1 @ A ) =>
% 52.27/52.53       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 52.27/52.53  thf('64', plain,
% 52.27/52.53      (![X24 : $i]:
% 52.27/52.53         (((k7_relat_1 @ X24 @ (k1_relat_1 @ X24)) = (X24))
% 52.27/52.53          | ~ (v1_relat_1 @ X24))),
% 52.27/52.53      inference('cnf', [status(esa)], [t98_relat_1])).
% 52.27/52.53  thf('65', plain,
% 52.27/52.53      ((((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 52.27/52.53        | ~ (v1_relat_1 @ k1_xboole_0))),
% 52.27/52.53      inference('sup+', [status(thm)], ['63', '64'])).
% 52.27/52.53  thf(t4_subset_1, axiom,
% 52.27/52.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 52.27/52.53  thf('66', plain,
% 52.27/52.53      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 52.27/52.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 52.27/52.53  thf(cc1_relset_1, axiom,
% 52.27/52.53    (![A:$i,B:$i,C:$i]:
% 52.27/52.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 52.27/52.53       ( v1_relat_1 @ C ) ))).
% 52.27/52.53  thf('67', plain,
% 52.27/52.53      (![X27 : $i, X28 : $i, X29 : $i]:
% 52.27/52.53         ((v1_relat_1 @ X27)
% 52.27/52.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 52.27/52.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 52.27/52.53  thf('68', plain, ((v1_relat_1 @ k1_xboole_0)),
% 52.27/52.53      inference('sup-', [status(thm)], ['66', '67'])).
% 52.27/52.53  thf('69', plain,
% 52.27/52.53      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 52.27/52.53      inference('demod', [status(thm)], ['65', '68'])).
% 52.27/52.53  thf('70', plain,
% 52.27/52.53      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.27/52.53      inference('demod', [status(thm)], ['60', '61'])).
% 52.27/52.53  thf('71', plain,
% 52.27/52.53      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 52.27/52.53      inference('simplify', [status(thm)], ['42'])).
% 52.27/52.53  thf('72', plain,
% 52.27/52.53      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 52.27/52.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 52.27/52.53  thf('73', plain,
% 52.27/52.53      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.27/52.53      inference('demod', [status(thm)], ['51', '52'])).
% 52.27/52.53  thf('74', plain,
% 52.27/52.53      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.27/52.53      inference('demod', [status(thm)], ['60', '61'])).
% 52.27/52.53  thf('75', plain,
% 52.27/52.53      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 52.27/52.53      inference('demod', [status(thm)], ['65', '68'])).
% 52.27/52.53  thf('76', plain,
% 52.27/52.53      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 52.27/52.53      inference('demod', [status(thm)], ['60', '61'])).
% 52.27/52.53  thf('77', plain,
% 52.27/52.53      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 52.27/52.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 52.27/52.53  thf('78', plain,
% 52.27/52.53      (![X33 : $i, X34 : $i, X35 : $i]:
% 52.27/52.53         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 52.27/52.53          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 52.27/52.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 52.27/52.53  thf('79', plain,
% 52.27/52.53      (![X0 : $i, X1 : $i]:
% 52.27/52.53         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 52.27/52.53      inference('sup-', [status(thm)], ['77', '78'])).
% 52.27/52.53  thf('80', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 52.27/52.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 52.27/52.53  thf('81', plain,
% 52.27/52.53      (![X0 : $i, X1 : $i]:
% 52.27/52.53         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 52.27/52.53      inference('demod', [status(thm)], ['79', '80'])).
% 52.27/52.53  thf('82', plain,
% 52.27/52.53      (![X38 : $i, X39 : $i, X40 : $i]:
% 52.27/52.53         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 52.27/52.53          | (v1_funct_2 @ X40 @ X38 @ X39)
% 52.27/52.53          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 52.27/52.53  thf('83', plain,
% 52.27/52.53      (![X0 : $i, X1 : $i]:
% 52.27/52.53         (((X1) != (k1_xboole_0))
% 52.27/52.53          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 52.27/52.53          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 52.27/52.53      inference('sup-', [status(thm)], ['81', '82'])).
% 52.27/52.53  thf('84', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 52.27/52.53          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 52.27/52.53      inference('simplify', [status(thm)], ['83'])).
% 52.27/52.53  thf('85', plain,
% 52.27/52.53      (![X36 : $i, X37 : $i]:
% 52.27/52.53         ((zip_tseitin_0 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 52.27/52.53  thf('86', plain, (![X36 : $i]: (zip_tseitin_0 @ X36 @ k1_xboole_0)),
% 52.27/52.53      inference('simplify', [status(thm)], ['85'])).
% 52.27/52.53  thf('87', plain,
% 52.27/52.53      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 52.27/52.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 52.27/52.53  thf('88', plain,
% 52.27/52.53      (![X41 : $i, X42 : $i, X43 : $i]:
% 52.27/52.53         (~ (zip_tseitin_0 @ X41 @ X42)
% 52.27/52.53          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 52.27/52.53          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 52.27/52.53  thf('89', plain,
% 52.27/52.53      (![X0 : $i, X1 : $i]:
% 52.27/52.53         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 52.27/52.53      inference('sup-', [status(thm)], ['87', '88'])).
% 52.27/52.53  thf('90', plain,
% 52.27/52.53      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 52.27/52.53      inference('sup-', [status(thm)], ['86', '89'])).
% 52.27/52.53  thf('91', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 52.27/52.53      inference('demod', [status(thm)], ['84', '90'])).
% 52.27/52.53  thf('92', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 52.27/52.53      inference('demod', [status(thm)],
% 52.27/52.53                ['55', '62', '69', '70', '71', '72', '73', '74', '75', '76', 
% 52.27/52.53                 '91'])).
% 52.27/52.53  thf('93', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 52.27/52.53      inference('split', [status(esa)], ['40'])).
% 52.27/52.53  thf('94', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 52.27/52.53      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 52.27/52.53  thf('95', plain, (((sk_B) != (k1_xboole_0))),
% 52.27/52.53      inference('simpl_trail', [status(thm)], ['41', '94'])).
% 52.27/52.53  thf('96', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 52.27/52.53      inference('simplify_reflect-', [status(thm)], ['39', '95'])).
% 52.27/52.53  thf(t91_relat_1, axiom,
% 52.27/52.53    (![A:$i,B:$i]:
% 52.27/52.53     ( ( v1_relat_1 @ B ) =>
% 52.27/52.53       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 52.27/52.53         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 52.27/52.53  thf('97', plain,
% 52.27/52.53      (![X22 : $i, X23 : $i]:
% 52.27/52.53         (~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 52.27/52.53          | ((k1_relat_1 @ (k7_relat_1 @ X23 @ X22)) = (X22))
% 52.27/52.53          | ~ (v1_relat_1 @ X23))),
% 52.27/52.53      inference('cnf', [status(esa)], [t91_relat_1])).
% 52.27/52.53  thf('98', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         (~ (r1_tarski @ X0 @ sk_A)
% 52.27/52.53          | ~ (v1_relat_1 @ sk_D)
% 52.27/52.53          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 52.27/52.53      inference('sup-', [status(thm)], ['96', '97'])).
% 52.27/52.53  thf('99', plain,
% 52.27/52.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.27/52.53  thf('100', plain,
% 52.27/52.53      (![X27 : $i, X28 : $i, X29 : $i]:
% 52.27/52.53         ((v1_relat_1 @ X27)
% 52.27/52.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 52.27/52.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 52.27/52.53  thf('101', plain, ((v1_relat_1 @ sk_D)),
% 52.27/52.53      inference('sup-', [status(thm)], ['99', '100'])).
% 52.27/52.53  thf('102', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         (~ (r1_tarski @ X0 @ sk_A)
% 52.27/52.53          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 52.27/52.53      inference('demod', [status(thm)], ['98', '101'])).
% 52.27/52.53  thf('103', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 52.27/52.53      inference('sup-', [status(thm)], ['14', '102'])).
% 52.27/52.53  thf('104', plain,
% 52.27/52.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.27/52.53  thf('105', plain,
% 52.27/52.53      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 52.27/52.53         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 52.27/52.53          | ~ (v1_funct_1 @ X44)
% 52.27/52.53          | (m1_subset_1 @ (k2_partfun1 @ X45 @ X46 @ X44 @ X47) @ 
% 52.27/52.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 52.27/52.53      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 52.27/52.53  thf('106', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 52.27/52.53           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 52.27/52.53          | ~ (v1_funct_1 @ sk_D))),
% 52.27/52.53      inference('sup-', [status(thm)], ['104', '105'])).
% 52.27/52.53  thf('107', plain, ((v1_funct_1 @ sk_D)),
% 52.27/52.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.27/52.53  thf('108', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 52.27/52.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.27/52.53      inference('demod', [status(thm)], ['106', '107'])).
% 52.27/52.53  thf('109', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 52.27/52.53      inference('demod', [status(thm)], ['9', '10'])).
% 52.27/52.53  thf('110', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 52.27/52.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.27/52.53      inference('demod', [status(thm)], ['108', '109'])).
% 52.27/52.53  thf(cc2_relset_1, axiom,
% 52.27/52.53    (![A:$i,B:$i,C:$i]:
% 52.27/52.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 52.27/52.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 52.27/52.53  thf('111', plain,
% 52.27/52.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 52.27/52.53         ((v5_relat_1 @ X30 @ X32)
% 52.27/52.53          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 52.27/52.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 52.27/52.53  thf('112', plain,
% 52.27/52.53      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 52.27/52.53      inference('sup-', [status(thm)], ['110', '111'])).
% 52.27/52.53  thf(d19_relat_1, axiom,
% 52.27/52.53    (![A:$i,B:$i]:
% 52.27/52.53     ( ( v1_relat_1 @ B ) =>
% 52.27/52.53       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 52.27/52.53  thf('113', plain,
% 52.27/52.53      (![X17 : $i, X18 : $i]:
% 52.27/52.53         (~ (v5_relat_1 @ X17 @ X18)
% 52.27/52.53          | (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 52.27/52.53          | ~ (v1_relat_1 @ X17))),
% 52.27/52.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 52.27/52.53  thf('114', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 52.27/52.53          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 52.27/52.53      inference('sup-', [status(thm)], ['112', '113'])).
% 52.27/52.53  thf('115', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 52.27/52.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 52.27/52.53      inference('demod', [status(thm)], ['108', '109'])).
% 52.27/52.53  thf('116', plain,
% 52.27/52.53      (![X27 : $i, X28 : $i, X29 : $i]:
% 52.27/52.53         ((v1_relat_1 @ X27)
% 52.27/52.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 52.27/52.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 52.27/52.53  thf('117', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 52.27/52.53      inference('sup-', [status(thm)], ['115', '116'])).
% 52.27/52.53  thf('118', plain,
% 52.27/52.53      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 52.27/52.53      inference('demod', [status(thm)], ['114', '117'])).
% 52.27/52.53  thf(t4_funct_2, axiom,
% 52.27/52.53    (![A:$i,B:$i]:
% 52.27/52.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 52.27/52.53       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 52.27/52.53         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 52.27/52.53           ( m1_subset_1 @
% 52.27/52.53             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 52.27/52.53  thf('119', plain,
% 52.27/52.53      (![X52 : $i, X53 : $i]:
% 52.27/52.53         (~ (r1_tarski @ (k2_relat_1 @ X52) @ X53)
% 52.27/52.53          | (v1_funct_2 @ X52 @ (k1_relat_1 @ X52) @ X53)
% 52.27/52.53          | ~ (v1_funct_1 @ X52)
% 52.27/52.53          | ~ (v1_relat_1 @ X52))),
% 52.27/52.53      inference('cnf', [status(esa)], [t4_funct_2])).
% 52.27/52.53  thf('120', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 52.27/52.53          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 52.27/52.53          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 52.27/52.53             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 52.27/52.53      inference('sup-', [status(thm)], ['118', '119'])).
% 52.27/52.53  thf('121', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 52.27/52.53      inference('sup-', [status(thm)], ['115', '116'])).
% 52.27/52.53  thf('122', plain,
% 52.27/52.53      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 52.27/52.53      inference('demod', [status(thm)], ['3', '4'])).
% 52.27/52.53  thf('123', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 52.27/52.53      inference('demod', [status(thm)], ['9', '10'])).
% 52.27/52.53  thf('124', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 52.27/52.53      inference('demod', [status(thm)], ['122', '123'])).
% 52.27/52.53  thf('125', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 52.27/52.53          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 52.27/52.53      inference('demod', [status(thm)], ['120', '121', '124'])).
% 52.27/52.53  thf('126', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 52.27/52.53      inference('sup+', [status(thm)], ['103', '125'])).
% 52.27/52.53  thf('127', plain,
% 52.27/52.53      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 52.27/52.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 52.27/52.53      inference('demod', [status(thm)], ['13', '126'])).
% 52.27/52.53  thf('128', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 52.27/52.53      inference('sup-', [status(thm)], ['14', '102'])).
% 52.27/52.53  thf('129', plain,
% 52.27/52.53      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 52.27/52.53      inference('demod', [status(thm)], ['114', '117'])).
% 52.27/52.53  thf('130', plain,
% 52.27/52.53      (![X52 : $i, X53 : $i]:
% 52.27/52.53         (~ (r1_tarski @ (k2_relat_1 @ X52) @ X53)
% 52.27/52.53          | (m1_subset_1 @ X52 @ 
% 52.27/52.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X52) @ X53)))
% 52.27/52.53          | ~ (v1_funct_1 @ X52)
% 52.27/52.53          | ~ (v1_relat_1 @ X52))),
% 52.27/52.53      inference('cnf', [status(esa)], [t4_funct_2])).
% 52.27/52.53  thf('131', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 52.27/52.53          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 52.27/52.53          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 52.27/52.53             (k1_zfmisc_1 @ 
% 52.27/52.53              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 52.27/52.53      inference('sup-', [status(thm)], ['129', '130'])).
% 52.27/52.53  thf('132', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 52.27/52.53      inference('sup-', [status(thm)], ['115', '116'])).
% 52.27/52.53  thf('133', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 52.27/52.53      inference('demod', [status(thm)], ['122', '123'])).
% 52.27/52.53  thf('134', plain,
% 52.27/52.53      (![X0 : $i]:
% 52.27/52.53         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 52.27/52.53          (k1_zfmisc_1 @ 
% 52.27/52.53           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 52.27/52.53      inference('demod', [status(thm)], ['131', '132', '133'])).
% 52.27/52.53  thf('135', plain,
% 52.27/52.53      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 52.27/52.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 52.27/52.53      inference('sup+', [status(thm)], ['128', '134'])).
% 52.27/52.53  thf('136', plain, ($false), inference('demod', [status(thm)], ['127', '135'])).
% 52.27/52.53  
% 52.27/52.53  % SZS output end Refutation
% 52.27/52.53  
% 52.34/52.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
