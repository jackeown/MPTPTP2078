%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7klEiYpjcg

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:38 EST 2020

% Result     : Theorem 27.68s
% Output     : Refutation 27.68s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 947 expanded)
%              Number of leaves         :   42 ( 296 expanded)
%              Depth                    :   20
%              Number of atoms          : 1486 (14156 expanded)
%              Number of equality atoms :  114 ( 854 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X41 @ X42 @ X40 @ X43 ) ) ) ),
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
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ( ( k2_partfun1 @ X45 @ X46 @ X44 @ X47 )
        = ( k7_relat_1 @ X44 @ X47 ) ) ) ),
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
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf('14',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
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
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('16',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
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
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('38',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','43'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
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
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 )
      | ( k1_xboole_0 = sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,
    ( ( k1_xboole_0 = sk_C_1 )
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

thf('61',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('62',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ( ( k2_partfun1 @ X45 @ X46 @ X44 @ X47 )
        = ( k7_relat_1 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('70',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('71',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['65','72'])).

thf('74',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','73'])).

thf('75',plain,
    ( ( k1_xboole_0 = sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('76',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('77',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('79',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('80',plain,
    ( ( k1_xboole_0 = sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('81',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','73'])).

thf('82',plain,
    ( ( k1_xboole_0 = sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('83',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('84',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('87',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('88',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('92',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','92'])).

thf('94',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X33 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('98',plain,(
    ! [X32: $i] :
      ( zip_tseitin_0 @ X32 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('100',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['96','102'])).

thf('104',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','50','57','74','75','76','77','78','79','80','81','82','103'])).

thf('105',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('106',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['104','105'])).

thf('107',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['35','106'])).

thf('108',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['33','107'])).

thf('109',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['110','113'])).

thf('115',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['14','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('117',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v5_relat_1 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('118',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['116','117'])).

thf(fc22_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v5_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('119',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) @ X22 )
      | ~ ( v5_relat_1 @ X20 @ X22 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc22_relat_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['111','112'])).

thf('122',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['120','121'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('123',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X41 @ X42 @ X40 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('131',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['124','133'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('135',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X48 ) @ X49 )
      | ( v1_funct_2 @ X48 @ ( k1_relat_1 @ X48 ) @ X49 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('138',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('140',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['136','137','140'])).

thf('142',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B ),
    inference('sup+',[status(thm)],['115','141'])).

thf('143',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','142'])).

thf('144',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['14','114'])).

thf('145',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['124','133'])).

thf('146',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X48 ) @ X49 )
      | ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X48 ) @ X49 ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('149',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('150',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['144','150'])).

thf('152',plain,(
    $false ),
    inference(demod,[status(thm)],['143','151'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7klEiYpjcg
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:07:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 27.68/27.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 27.68/27.95  % Solved by: fo/fo7.sh
% 27.68/27.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 27.68/27.95  % done 15942 iterations in 27.479s
% 27.68/27.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 27.68/27.95  % SZS output start Refutation
% 27.68/27.95  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 27.68/27.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 27.68/27.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 27.68/27.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 27.68/27.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 27.68/27.95  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 27.68/27.95  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 27.68/27.95  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 27.68/27.95  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 27.68/27.95  thf(sk_A_type, type, sk_A: $i).
% 27.68/27.95  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 27.68/27.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 27.68/27.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 27.68/27.95  thf(sk_B_type, type, sk_B: $i).
% 27.68/27.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 27.68/27.95  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 27.68/27.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 27.68/27.95  thf(sk_D_type, type, sk_D: $i).
% 27.68/27.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 27.68/27.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 27.68/27.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 27.68/27.95  thf(t38_funct_2, conjecture,
% 27.68/27.95    (![A:$i,B:$i,C:$i,D:$i]:
% 27.68/27.95     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 27.68/27.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 27.68/27.95       ( ( r1_tarski @ C @ A ) =>
% 27.68/27.95         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 27.68/27.95           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 27.68/27.95             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 27.68/27.95             ( m1_subset_1 @
% 27.68/27.95               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 27.68/27.95               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 27.68/27.95  thf(zf_stmt_0, negated_conjecture,
% 27.68/27.95    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 27.68/27.95        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 27.68/27.95            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 27.68/27.95          ( ( r1_tarski @ C @ A ) =>
% 27.68/27.95            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 27.68/27.95              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 27.68/27.95                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 27.68/27.95                ( m1_subset_1 @
% 27.68/27.95                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 27.68/27.95                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 27.68/27.95    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 27.68/27.95  thf('0', plain,
% 27.68/27.95      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1))
% 27.68/27.95        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ 
% 27.68/27.95             sk_C_1 @ sk_B)
% 27.68/27.95        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ 
% 27.68/27.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B))))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf('1', plain,
% 27.68/27.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf(dt_k2_partfun1, axiom,
% 27.68/27.95    (![A:$i,B:$i,C:$i,D:$i]:
% 27.68/27.95     ( ( ( v1_funct_1 @ C ) & 
% 27.68/27.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 27.68/27.95       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 27.68/27.95         ( m1_subset_1 @
% 27.68/27.95           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 27.68/27.95           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 27.68/27.95  thf('2', plain,
% 27.68/27.95      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 27.68/27.95         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 27.68/27.95          | ~ (v1_funct_1 @ X40)
% 27.68/27.95          | (v1_funct_1 @ (k2_partfun1 @ X41 @ X42 @ X40 @ X43)))),
% 27.68/27.95      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 27.68/27.95  thf('3', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 27.68/27.95          | ~ (v1_funct_1 @ sk_D))),
% 27.68/27.95      inference('sup-', [status(thm)], ['1', '2'])).
% 27.68/27.95  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf('5', plain,
% 27.68/27.95      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 27.68/27.95      inference('demod', [status(thm)], ['3', '4'])).
% 27.68/27.95  thf('6', plain,
% 27.68/27.95      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ sk_C_1 @ 
% 27.68/27.95           sk_B)
% 27.68/27.95        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ 
% 27.68/27.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B))))),
% 27.68/27.95      inference('demod', [status(thm)], ['0', '5'])).
% 27.68/27.95  thf('7', plain,
% 27.68/27.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf(redefinition_k2_partfun1, axiom,
% 27.68/27.95    (![A:$i,B:$i,C:$i,D:$i]:
% 27.68/27.95     ( ( ( v1_funct_1 @ C ) & 
% 27.68/27.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 27.68/27.95       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 27.68/27.95  thf('8', plain,
% 27.68/27.95      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 27.68/27.95         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 27.68/27.95          | ~ (v1_funct_1 @ X44)
% 27.68/27.95          | ((k2_partfun1 @ X45 @ X46 @ X44 @ X47) = (k7_relat_1 @ X44 @ X47)))),
% 27.68/27.95      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 27.68/27.95  thf('9', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 27.68/27.95          | ~ (v1_funct_1 @ sk_D))),
% 27.68/27.95      inference('sup-', [status(thm)], ['7', '8'])).
% 27.68/27.95  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf('11', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 27.68/27.95      inference('demod', [status(thm)], ['9', '10'])).
% 27.68/27.95  thf('12', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 27.68/27.95      inference('demod', [status(thm)], ['9', '10'])).
% 27.68/27.95  thf('13', plain,
% 27.68/27.95      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C_1) @ sk_C_1 @ sk_B)
% 27.68/27.95        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C_1) @ 
% 27.68/27.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B))))),
% 27.68/27.95      inference('demod', [status(thm)], ['6', '11', '12'])).
% 27.68/27.95  thf('14', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf(d1_funct_2, axiom,
% 27.68/27.95    (![A:$i,B:$i,C:$i]:
% 27.68/27.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 27.68/27.95       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 27.68/27.95           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 27.68/27.95             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 27.68/27.95         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 27.68/27.95           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 27.68/27.95             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 27.68/27.95  thf(zf_stmt_1, axiom,
% 27.68/27.95    (![B:$i,A:$i]:
% 27.68/27.95     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 27.68/27.95       ( zip_tseitin_0 @ B @ A ) ))).
% 27.68/27.95  thf('15', plain,
% 27.68/27.95      (![X32 : $i, X33 : $i]:
% 27.68/27.95         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 27.68/27.95  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 27.68/27.95  thf('16', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 27.68/27.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 27.68/27.95  thf('17', plain,
% 27.68/27.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.68/27.95         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 27.68/27.95      inference('sup+', [status(thm)], ['15', '16'])).
% 27.68/27.95  thf('18', plain,
% 27.68/27.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 27.68/27.95  thf(zf_stmt_3, axiom,
% 27.68/27.95    (![C:$i,B:$i,A:$i]:
% 27.68/27.95     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 27.68/27.95       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 27.68/27.95  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 27.68/27.95  thf(zf_stmt_5, axiom,
% 27.68/27.95    (![A:$i,B:$i,C:$i]:
% 27.68/27.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 27.68/27.95       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 27.68/27.95         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 27.68/27.95           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 27.68/27.95             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 27.68/27.95  thf('19', plain,
% 27.68/27.95      (![X37 : $i, X38 : $i, X39 : $i]:
% 27.68/27.95         (~ (zip_tseitin_0 @ X37 @ X38)
% 27.68/27.95          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 27.68/27.95          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 27.68/27.95  thf('20', plain,
% 27.68/27.95      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 27.68/27.95      inference('sup-', [status(thm)], ['18', '19'])).
% 27.68/27.95  thf('21', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 27.68/27.95      inference('sup-', [status(thm)], ['17', '20'])).
% 27.68/27.95  thf('22', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf('23', plain,
% 27.68/27.95      (![X34 : $i, X35 : $i, X36 : $i]:
% 27.68/27.95         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 27.68/27.95          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 27.68/27.95          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 27.68/27.95  thf('24', plain,
% 27.68/27.95      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 27.68/27.95        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 27.68/27.95      inference('sup-', [status(thm)], ['22', '23'])).
% 27.68/27.95  thf('25', plain,
% 27.68/27.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf(redefinition_k1_relset_1, axiom,
% 27.68/27.95    (![A:$i,B:$i,C:$i]:
% 27.68/27.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 27.68/27.95       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 27.68/27.95  thf('26', plain,
% 27.68/27.95      (![X29 : $i, X30 : $i, X31 : $i]:
% 27.68/27.95         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 27.68/27.95          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 27.68/27.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 27.68/27.95  thf('27', plain,
% 27.68/27.95      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 27.68/27.95      inference('sup-', [status(thm)], ['25', '26'])).
% 27.68/27.95  thf('28', plain,
% 27.68/27.95      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 27.68/27.95      inference('demod', [status(thm)], ['24', '27'])).
% 27.68/27.95  thf('29', plain,
% 27.68/27.95      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 27.68/27.95      inference('sup-', [status(thm)], ['21', '28'])).
% 27.68/27.95  thf('30', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 27.68/27.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 27.68/27.95  thf(d10_xboole_0, axiom,
% 27.68/27.95    (![A:$i,B:$i]:
% 27.68/27.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 27.68/27.95  thf('31', plain,
% 27.68/27.95      (![X4 : $i, X6 : $i]:
% 27.68/27.95         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 27.68/27.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.68/27.95  thf('32', plain,
% 27.68/27.95      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 27.68/27.95      inference('sup-', [status(thm)], ['30', '31'])).
% 27.68/27.95  thf('33', plain,
% 27.68/27.95      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((sk_B) = (k1_xboole_0)))),
% 27.68/27.95      inference('sup-', [status(thm)], ['29', '32'])).
% 27.68/27.95  thf('34', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf('35', plain,
% 27.68/27.95      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 27.68/27.95      inference('split', [status(esa)], ['34'])).
% 27.68/27.95  thf('36', plain,
% 27.68/27.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('split', [status(esa)], ['34'])).
% 27.68/27.95  thf('37', plain,
% 27.68/27.95      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ sk_C_1 @ 
% 27.68/27.95           sk_B)
% 27.68/27.95        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ 
% 27.68/27.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B))))),
% 27.68/27.95      inference('demod', [status(thm)], ['0', '5'])).
% 27.68/27.95  thf('38', plain,
% 27.68/27.95      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C_1) @ 
% 27.68/27.95            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))
% 27.68/27.95         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ 
% 27.68/27.95              sk_C_1 @ sk_B)))
% 27.68/27.95         <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('sup-', [status(thm)], ['36', '37'])).
% 27.68/27.95  thf('39', plain,
% 27.68/27.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('split', [status(esa)], ['34'])).
% 27.68/27.95  thf('40', plain,
% 27.68/27.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf('41', plain,
% 27.68/27.95      (((m1_subset_1 @ sk_D @ 
% 27.68/27.95         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 27.68/27.95         <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('sup+', [status(thm)], ['39', '40'])).
% 27.68/27.95  thf(t113_zfmisc_1, axiom,
% 27.68/27.95    (![A:$i,B:$i]:
% 27.68/27.95     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 27.68/27.95       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 27.68/27.95  thf('42', plain,
% 27.68/27.95      (![X9 : $i, X10 : $i]:
% 27.68/27.95         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 27.68/27.95      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 27.68/27.95  thf('43', plain,
% 27.68/27.95      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 27.68/27.95      inference('simplify', [status(thm)], ['42'])).
% 27.68/27.95  thf('44', plain,
% 27.68/27.95      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 27.68/27.95         <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('demod', [status(thm)], ['41', '43'])).
% 27.68/27.95  thf(t3_subset, axiom,
% 27.68/27.95    (![A:$i,B:$i]:
% 27.68/27.95     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 27.68/27.95  thf('45', plain,
% 27.68/27.95      (![X11 : $i, X12 : $i]:
% 27.68/27.95         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 27.68/27.95      inference('cnf', [status(esa)], [t3_subset])).
% 27.68/27.95  thf('46', plain,
% 27.68/27.95      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('sup-', [status(thm)], ['44', '45'])).
% 27.68/27.95  thf('47', plain,
% 27.68/27.95      (![X4 : $i, X6 : $i]:
% 27.68/27.95         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 27.68/27.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.68/27.95  thf('48', plain,
% 27.68/27.95      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 27.68/27.95         <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('sup-', [status(thm)], ['46', '47'])).
% 27.68/27.95  thf('49', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 27.68/27.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 27.68/27.95  thf('50', plain,
% 27.68/27.95      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('demod', [status(thm)], ['48', '49'])).
% 27.68/27.95  thf('51', plain,
% 27.68/27.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('split', [status(esa)], ['34'])).
% 27.68/27.95  thf('52', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf('53', plain,
% 27.68/27.95      (((r1_tarski @ sk_C_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('sup+', [status(thm)], ['51', '52'])).
% 27.68/27.95  thf('54', plain,
% 27.68/27.95      (![X4 : $i, X6 : $i]:
% 27.68/27.95         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 27.68/27.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.68/27.95  thf('55', plain,
% 27.68/27.95      (((~ (r1_tarski @ k1_xboole_0 @ sk_C_1) | ((k1_xboole_0) = (sk_C_1))))
% 27.68/27.95         <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('sup-', [status(thm)], ['53', '54'])).
% 27.68/27.95  thf('56', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 27.68/27.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 27.68/27.95  thf('57', plain,
% 27.68/27.95      ((((k1_xboole_0) = (sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('demod', [status(thm)], ['55', '56'])).
% 27.68/27.95  thf('58', plain,
% 27.68/27.95      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('demod', [status(thm)], ['48', '49'])).
% 27.68/27.95  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf('60', plain,
% 27.68/27.95      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('sup+', [status(thm)], ['58', '59'])).
% 27.68/27.95  thf('61', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 27.68/27.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 27.68/27.95  thf('62', plain,
% 27.68/27.95      (![X11 : $i, X13 : $i]:
% 27.68/27.95         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 27.68/27.95      inference('cnf', [status(esa)], [t3_subset])).
% 27.68/27.95  thf('63', plain,
% 27.68/27.95      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 27.68/27.95      inference('sup-', [status(thm)], ['61', '62'])).
% 27.68/27.95  thf('64', plain,
% 27.68/27.95      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 27.68/27.95         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 27.68/27.95          | ~ (v1_funct_1 @ X44)
% 27.68/27.95          | ((k2_partfun1 @ X45 @ X46 @ X44 @ X47) = (k7_relat_1 @ X44 @ X47)))),
% 27.68/27.95      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 27.68/27.95  thf('65', plain,
% 27.68/27.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.68/27.95         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 27.68/27.95            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 27.68/27.95          | ~ (v1_funct_1 @ k1_xboole_0))),
% 27.68/27.95      inference('sup-', [status(thm)], ['63', '64'])).
% 27.68/27.95  thf(t88_relat_1, axiom,
% 27.68/27.95    (![A:$i,B:$i]:
% 27.68/27.95     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 27.68/27.95  thf('66', plain,
% 27.68/27.95      (![X16 : $i, X17 : $i]:
% 27.68/27.95         ((r1_tarski @ (k7_relat_1 @ X16 @ X17) @ X16) | ~ (v1_relat_1 @ X16))),
% 27.68/27.95      inference('cnf', [status(esa)], [t88_relat_1])).
% 27.68/27.95  thf('67', plain,
% 27.68/27.95      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 27.68/27.95      inference('sup-', [status(thm)], ['30', '31'])).
% 27.68/27.95  thf('68', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         (~ (v1_relat_1 @ k1_xboole_0)
% 27.68/27.95          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 27.68/27.95      inference('sup-', [status(thm)], ['66', '67'])).
% 27.68/27.95  thf('69', plain,
% 27.68/27.95      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 27.68/27.95      inference('sup-', [status(thm)], ['61', '62'])).
% 27.68/27.95  thf(cc1_relset_1, axiom,
% 27.68/27.95    (![A:$i,B:$i,C:$i]:
% 27.68/27.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 27.68/27.95       ( v1_relat_1 @ C ) ))).
% 27.68/27.95  thf('70', plain,
% 27.68/27.95      (![X23 : $i, X24 : $i, X25 : $i]:
% 27.68/27.95         ((v1_relat_1 @ X23)
% 27.68/27.95          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 27.68/27.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 27.68/27.95  thf('71', plain, ((v1_relat_1 @ k1_xboole_0)),
% 27.68/27.95      inference('sup-', [status(thm)], ['69', '70'])).
% 27.68/27.95  thf('72', plain,
% 27.68/27.95      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 27.68/27.95      inference('demod', [status(thm)], ['68', '71'])).
% 27.68/27.95  thf('73', plain,
% 27.68/27.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.68/27.95         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 27.68/27.95          | ~ (v1_funct_1 @ k1_xboole_0))),
% 27.68/27.95      inference('demod', [status(thm)], ['65', '72'])).
% 27.68/27.95  thf('74', plain,
% 27.68/27.95      ((![X0 : $i, X1 : $i, X2 : $i]:
% 27.68/27.95          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 27.68/27.95         <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('sup-', [status(thm)], ['60', '73'])).
% 27.68/27.95  thf('75', plain,
% 27.68/27.95      ((((k1_xboole_0) = (sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('demod', [status(thm)], ['55', '56'])).
% 27.68/27.95  thf('76', plain,
% 27.68/27.95      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 27.68/27.95      inference('simplify', [status(thm)], ['42'])).
% 27.68/27.95  thf('77', plain,
% 27.68/27.95      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 27.68/27.95      inference('sup-', [status(thm)], ['61', '62'])).
% 27.68/27.95  thf('78', plain,
% 27.68/27.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('split', [status(esa)], ['34'])).
% 27.68/27.95  thf('79', plain,
% 27.68/27.95      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('demod', [status(thm)], ['48', '49'])).
% 27.68/27.95  thf('80', plain,
% 27.68/27.95      ((((k1_xboole_0) = (sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('demod', [status(thm)], ['55', '56'])).
% 27.68/27.95  thf('81', plain,
% 27.68/27.95      ((![X0 : $i, X1 : $i, X2 : $i]:
% 27.68/27.95          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 27.68/27.95         <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('sup-', [status(thm)], ['60', '73'])).
% 27.68/27.95  thf('82', plain,
% 27.68/27.95      ((((k1_xboole_0) = (sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 27.68/27.95      inference('demod', [status(thm)], ['55', '56'])).
% 27.68/27.95  thf('83', plain,
% 27.68/27.95      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 27.68/27.95      inference('sup-', [status(thm)], ['61', '62'])).
% 27.68/27.95  thf('84', plain,
% 27.68/27.95      (![X29 : $i, X30 : $i, X31 : $i]:
% 27.68/27.95         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 27.68/27.95          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 27.68/27.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 27.68/27.95  thf('85', plain,
% 27.68/27.95      (![X0 : $i, X1 : $i]:
% 27.68/27.95         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 27.68/27.95      inference('sup-', [status(thm)], ['83', '84'])).
% 27.68/27.95  thf('86', plain,
% 27.68/27.95      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 27.68/27.95      inference('demod', [status(thm)], ['68', '71'])).
% 27.68/27.95  thf('87', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 27.68/27.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 27.68/27.95  thf(t91_relat_1, axiom,
% 27.68/27.95    (![A:$i,B:$i]:
% 27.68/27.95     ( ( v1_relat_1 @ B ) =>
% 27.68/27.95       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 27.68/27.95         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 27.68/27.95  thf('88', plain,
% 27.68/27.95      (![X18 : $i, X19 : $i]:
% 27.68/27.95         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 27.68/27.95          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 27.68/27.95          | ~ (v1_relat_1 @ X19))),
% 27.68/27.95      inference('cnf', [status(esa)], [t91_relat_1])).
% 27.68/27.95  thf('89', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         (~ (v1_relat_1 @ X0)
% 27.68/27.95          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 27.68/27.95      inference('sup-', [status(thm)], ['87', '88'])).
% 27.68/27.95  thf('90', plain,
% 27.68/27.95      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 27.68/27.95        | ~ (v1_relat_1 @ k1_xboole_0))),
% 27.68/27.95      inference('sup+', [status(thm)], ['86', '89'])).
% 27.68/27.95  thf('91', plain, ((v1_relat_1 @ k1_xboole_0)),
% 27.68/27.95      inference('sup-', [status(thm)], ['69', '70'])).
% 27.68/27.95  thf('92', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 27.68/27.95      inference('demod', [status(thm)], ['90', '91'])).
% 27.68/27.95  thf('93', plain,
% 27.68/27.95      (![X0 : $i, X1 : $i]:
% 27.68/27.95         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 27.68/27.95      inference('demod', [status(thm)], ['85', '92'])).
% 27.68/27.95  thf('94', plain,
% 27.68/27.95      (![X34 : $i, X35 : $i, X36 : $i]:
% 27.68/27.95         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 27.68/27.95          | (v1_funct_2 @ X36 @ X34 @ X35)
% 27.68/27.95          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 27.68/27.95  thf('95', plain,
% 27.68/27.95      (![X0 : $i, X1 : $i]:
% 27.68/27.95         (((X1) != (k1_xboole_0))
% 27.68/27.95          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 27.68/27.95          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 27.68/27.95      inference('sup-', [status(thm)], ['93', '94'])).
% 27.68/27.95  thf('96', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 27.68/27.95          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 27.68/27.95      inference('simplify', [status(thm)], ['95'])).
% 27.68/27.95  thf('97', plain,
% 27.68/27.95      (![X32 : $i, X33 : $i]:
% 27.68/27.95         ((zip_tseitin_0 @ X32 @ X33) | ((X33) != (k1_xboole_0)))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 27.68/27.95  thf('98', plain, (![X32 : $i]: (zip_tseitin_0 @ X32 @ k1_xboole_0)),
% 27.68/27.95      inference('simplify', [status(thm)], ['97'])).
% 27.68/27.95  thf('99', plain,
% 27.68/27.95      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 27.68/27.95      inference('sup-', [status(thm)], ['61', '62'])).
% 27.68/27.95  thf('100', plain,
% 27.68/27.95      (![X37 : $i, X38 : $i, X39 : $i]:
% 27.68/27.95         (~ (zip_tseitin_0 @ X37 @ X38)
% 27.68/27.95          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 27.68/27.95          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 27.68/27.95  thf('101', plain,
% 27.68/27.95      (![X0 : $i, X1 : $i]:
% 27.68/27.95         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 27.68/27.95      inference('sup-', [status(thm)], ['99', '100'])).
% 27.68/27.95  thf('102', plain,
% 27.68/27.95      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 27.68/27.95      inference('sup-', [status(thm)], ['98', '101'])).
% 27.68/27.95  thf('103', plain,
% 27.68/27.95      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 27.68/27.95      inference('demod', [status(thm)], ['96', '102'])).
% 27.68/27.95  thf('104', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 27.68/27.95      inference('demod', [status(thm)],
% 27.68/27.95                ['38', '50', '57', '74', '75', '76', '77', '78', '79', '80', 
% 27.68/27.95                 '81', '82', '103'])).
% 27.68/27.95  thf('105', plain,
% 27.68/27.95      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 27.68/27.95      inference('split', [status(esa)], ['34'])).
% 27.68/27.95  thf('106', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 27.68/27.95      inference('sat_resolution*', [status(thm)], ['104', '105'])).
% 27.68/27.95  thf('107', plain, (((sk_B) != (k1_xboole_0))),
% 27.68/27.95      inference('simpl_trail', [status(thm)], ['35', '106'])).
% 27.68/27.95  thf('108', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 27.68/27.95      inference('simplify_reflect-', [status(thm)], ['33', '107'])).
% 27.68/27.95  thf('109', plain,
% 27.68/27.95      (![X18 : $i, X19 : $i]:
% 27.68/27.95         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 27.68/27.95          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 27.68/27.95          | ~ (v1_relat_1 @ X19))),
% 27.68/27.95      inference('cnf', [status(esa)], [t91_relat_1])).
% 27.68/27.95  thf('110', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         (~ (r1_tarski @ X0 @ sk_A)
% 27.68/27.95          | ~ (v1_relat_1 @ sk_D)
% 27.68/27.95          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 27.68/27.95      inference('sup-', [status(thm)], ['108', '109'])).
% 27.68/27.95  thf('111', plain,
% 27.68/27.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf('112', plain,
% 27.68/27.95      (![X23 : $i, X24 : $i, X25 : $i]:
% 27.68/27.95         ((v1_relat_1 @ X23)
% 27.68/27.95          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 27.68/27.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 27.68/27.95  thf('113', plain, ((v1_relat_1 @ sk_D)),
% 27.68/27.95      inference('sup-', [status(thm)], ['111', '112'])).
% 27.68/27.95  thf('114', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         (~ (r1_tarski @ X0 @ sk_A)
% 27.68/27.95          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 27.68/27.95      inference('demod', [status(thm)], ['110', '113'])).
% 27.68/27.95  thf('115', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C_1)) = (sk_C_1))),
% 27.68/27.95      inference('sup-', [status(thm)], ['14', '114'])).
% 27.68/27.95  thf('116', plain,
% 27.68/27.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf(cc2_relset_1, axiom,
% 27.68/27.95    (![A:$i,B:$i,C:$i]:
% 27.68/27.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 27.68/27.95       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 27.68/27.95  thf('117', plain,
% 27.68/27.95      (![X26 : $i, X27 : $i, X28 : $i]:
% 27.68/27.95         ((v5_relat_1 @ X26 @ X28)
% 27.68/27.95          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 27.68/27.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 27.68/27.95  thf('118', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 27.68/27.95      inference('sup-', [status(thm)], ['116', '117'])).
% 27.68/27.95  thf(fc22_relat_1, axiom,
% 27.68/27.95    (![A:$i,B:$i,C:$i]:
% 27.68/27.95     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ B ) ) =>
% 27.68/27.95       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 27.68/27.95         ( v5_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 27.68/27.95  thf('119', plain,
% 27.68/27.95      (![X20 : $i, X21 : $i, X22 : $i]:
% 27.68/27.95         ((v5_relat_1 @ (k7_relat_1 @ X20 @ X21) @ X22)
% 27.68/27.95          | ~ (v5_relat_1 @ X20 @ X22)
% 27.68/27.95          | ~ (v1_relat_1 @ X20))),
% 27.68/27.95      inference('cnf', [status(esa)], [fc22_relat_1])).
% 27.68/27.95  thf('120', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         (~ (v1_relat_1 @ sk_D)
% 27.68/27.95          | (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B))),
% 27.68/27.95      inference('sup-', [status(thm)], ['118', '119'])).
% 27.68/27.95  thf('121', plain, ((v1_relat_1 @ sk_D)),
% 27.68/27.95      inference('sup-', [status(thm)], ['111', '112'])).
% 27.68/27.95  thf('122', plain,
% 27.68/27.95      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 27.68/27.95      inference('demod', [status(thm)], ['120', '121'])).
% 27.68/27.95  thf(d19_relat_1, axiom,
% 27.68/27.95    (![A:$i,B:$i]:
% 27.68/27.95     ( ( v1_relat_1 @ B ) =>
% 27.68/27.95       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 27.68/27.95  thf('123', plain,
% 27.68/27.95      (![X14 : $i, X15 : $i]:
% 27.68/27.95         (~ (v5_relat_1 @ X14 @ X15)
% 27.68/27.95          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 27.68/27.95          | ~ (v1_relat_1 @ X14))),
% 27.68/27.95      inference('cnf', [status(esa)], [d19_relat_1])).
% 27.68/27.95  thf('124', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 27.68/27.95          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 27.68/27.95      inference('sup-', [status(thm)], ['122', '123'])).
% 27.68/27.95  thf('125', plain,
% 27.68/27.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf('126', plain,
% 27.68/27.95      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 27.68/27.95         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 27.68/27.95          | ~ (v1_funct_1 @ X40)
% 27.68/27.95          | (m1_subset_1 @ (k2_partfun1 @ X41 @ X42 @ X40 @ X43) @ 
% 27.68/27.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 27.68/27.95      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 27.68/27.95  thf('127', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 27.68/27.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 27.68/27.95          | ~ (v1_funct_1 @ sk_D))),
% 27.68/27.95      inference('sup-', [status(thm)], ['125', '126'])).
% 27.68/27.95  thf('128', plain, ((v1_funct_1 @ sk_D)),
% 27.68/27.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.68/27.95  thf('129', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 27.68/27.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.68/27.95      inference('demod', [status(thm)], ['127', '128'])).
% 27.68/27.95  thf('130', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 27.68/27.95      inference('demod', [status(thm)], ['9', '10'])).
% 27.68/27.95  thf('131', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 27.68/27.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 27.68/27.95      inference('demod', [status(thm)], ['129', '130'])).
% 27.68/27.95  thf('132', plain,
% 27.68/27.95      (![X23 : $i, X24 : $i, X25 : $i]:
% 27.68/27.95         ((v1_relat_1 @ X23)
% 27.68/27.95          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 27.68/27.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 27.68/27.95  thf('133', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 27.68/27.95      inference('sup-', [status(thm)], ['131', '132'])).
% 27.68/27.95  thf('134', plain,
% 27.68/27.95      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 27.68/27.95      inference('demod', [status(thm)], ['124', '133'])).
% 27.68/27.95  thf(t4_funct_2, axiom,
% 27.68/27.95    (![A:$i,B:$i]:
% 27.68/27.95     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 27.68/27.95       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 27.68/27.95         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 27.68/27.95           ( m1_subset_1 @
% 27.68/27.95             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 27.68/27.95  thf('135', plain,
% 27.68/27.95      (![X48 : $i, X49 : $i]:
% 27.68/27.95         (~ (r1_tarski @ (k2_relat_1 @ X48) @ X49)
% 27.68/27.95          | (v1_funct_2 @ X48 @ (k1_relat_1 @ X48) @ X49)
% 27.68/27.95          | ~ (v1_funct_1 @ X48)
% 27.68/27.95          | ~ (v1_relat_1 @ X48))),
% 27.68/27.95      inference('cnf', [status(esa)], [t4_funct_2])).
% 27.68/27.95  thf('136', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 27.68/27.95          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 27.68/27.95          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 27.68/27.95             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 27.68/27.95      inference('sup-', [status(thm)], ['134', '135'])).
% 27.68/27.95  thf('137', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 27.68/27.95      inference('sup-', [status(thm)], ['131', '132'])).
% 27.68/27.95  thf('138', plain,
% 27.68/27.95      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 27.68/27.95      inference('demod', [status(thm)], ['3', '4'])).
% 27.68/27.95  thf('139', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 27.68/27.95      inference('demod', [status(thm)], ['9', '10'])).
% 27.68/27.95  thf('140', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 27.68/27.95      inference('demod', [status(thm)], ['138', '139'])).
% 27.68/27.95  thf('141', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 27.68/27.95          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 27.68/27.95      inference('demod', [status(thm)], ['136', '137', '140'])).
% 27.68/27.95  thf('142', plain,
% 27.68/27.95      ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C_1) @ sk_C_1 @ sk_B)),
% 27.68/27.95      inference('sup+', [status(thm)], ['115', '141'])).
% 27.68/27.95  thf('143', plain,
% 27.68/27.95      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C_1) @ 
% 27.68/27.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 27.68/27.95      inference('demod', [status(thm)], ['13', '142'])).
% 27.68/27.95  thf('144', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C_1)) = (sk_C_1))),
% 27.68/27.95      inference('sup-', [status(thm)], ['14', '114'])).
% 27.68/27.95  thf('145', plain,
% 27.68/27.95      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 27.68/27.95      inference('demod', [status(thm)], ['124', '133'])).
% 27.68/27.95  thf('146', plain,
% 27.68/27.95      (![X48 : $i, X49 : $i]:
% 27.68/27.95         (~ (r1_tarski @ (k2_relat_1 @ X48) @ X49)
% 27.68/27.95          | (m1_subset_1 @ X48 @ 
% 27.68/27.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X48) @ X49)))
% 27.68/27.95          | ~ (v1_funct_1 @ X48)
% 27.68/27.95          | ~ (v1_relat_1 @ X48))),
% 27.68/27.95      inference('cnf', [status(esa)], [t4_funct_2])).
% 27.68/27.95  thf('147', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 27.68/27.95          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 27.68/27.95          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 27.68/27.95             (k1_zfmisc_1 @ 
% 27.68/27.95              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 27.68/27.95      inference('sup-', [status(thm)], ['145', '146'])).
% 27.68/27.95  thf('148', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 27.68/27.95      inference('sup-', [status(thm)], ['131', '132'])).
% 27.68/27.95  thf('149', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 27.68/27.95      inference('demod', [status(thm)], ['138', '139'])).
% 27.68/27.95  thf('150', plain,
% 27.68/27.95      (![X0 : $i]:
% 27.68/27.95         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 27.68/27.95          (k1_zfmisc_1 @ 
% 27.68/27.95           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 27.68/27.95      inference('demod', [status(thm)], ['147', '148', '149'])).
% 27.68/27.95  thf('151', plain,
% 27.68/27.95      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C_1) @ 
% 27.68/27.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 27.68/27.95      inference('sup+', [status(thm)], ['144', '150'])).
% 27.68/27.95  thf('152', plain, ($false), inference('demod', [status(thm)], ['143', '151'])).
% 27.68/27.95  
% 27.68/27.95  % SZS output end Refutation
% 27.68/27.95  
% 27.68/27.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
