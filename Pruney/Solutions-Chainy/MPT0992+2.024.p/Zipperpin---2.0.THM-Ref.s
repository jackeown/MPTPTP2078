%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aVu3nyOUzG

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:37 EST 2020

% Result     : Theorem 15.31s
% Output     : Refutation 15.31s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 979 expanded)
%              Number of leaves         :   41 ( 306 expanded)
%              Depth                    :   20
%              Number of atoms          : 1469 (14806 expanded)
%              Number of equality atoms :  115 ( 884 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X44 @ X45 @ X43 @ X46 )
        = ( k7_relat_1 @ X43 @ X46 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X18 @ X19 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('88',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = X2 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','93'])).

thf('95',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('99',plain,(
    ! [X31: $i] :
      ( zip_tseitin_0 @ X31 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('101',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['97','103'])).

thf('105',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','50','57','74','75','76','77','78','79','80','81','82','104'])).

thf('106',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('107',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['105','106'])).

thf('108',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['35','107'])).

thf('109',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['33','108'])).

thf('110',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('114',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['111','114'])).

thf('116',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['14','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X40 @ X41 @ X39 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('123',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('124',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('126',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('129',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['127','130'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('132',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X47 ) @ X48 )
      | ( v1_funct_2 @ X47 @ ( k1_relat_1 @ X47 ) @ X48 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('135',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('137',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['133','134','137'])).

thf('139',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ sk_C_1 @ sk_B ),
    inference('sup+',[status(thm)],['116','138'])).

thf('140',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','139'])).

thf('141',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['14','115'])).

thf('142',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['127','130'])).

thf('143',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X47 ) @ X48 )
      | ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ X48 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('146',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('147',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['141','147'])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['140','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aVu3nyOUzG
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:24:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 15.31/15.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 15.31/15.52  % Solved by: fo/fo7.sh
% 15.31/15.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.31/15.52  % done 11648 iterations in 15.036s
% 15.31/15.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 15.31/15.52  % SZS output start Refutation
% 15.31/15.52  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 15.31/15.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 15.31/15.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 15.31/15.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 15.31/15.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 15.31/15.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.31/15.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 15.31/15.52  thf(sk_A_type, type, sk_A: $i).
% 15.31/15.52  thf(sk_D_type, type, sk_D: $i).
% 15.31/15.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 15.31/15.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.31/15.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 15.31/15.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 15.31/15.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 15.31/15.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.31/15.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 15.31/15.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 15.31/15.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 15.31/15.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 15.31/15.52  thf(sk_B_type, type, sk_B: $i).
% 15.31/15.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.31/15.52  thf(t38_funct_2, conjecture,
% 15.31/15.52    (![A:$i,B:$i,C:$i,D:$i]:
% 15.31/15.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 15.31/15.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.31/15.52       ( ( r1_tarski @ C @ A ) =>
% 15.31/15.52         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 15.31/15.52           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 15.31/15.52             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 15.31/15.52             ( m1_subset_1 @
% 15.31/15.52               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 15.31/15.52               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 15.31/15.52  thf(zf_stmt_0, negated_conjecture,
% 15.31/15.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 15.31/15.52        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 15.31/15.52            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.31/15.52          ( ( r1_tarski @ C @ A ) =>
% 15.31/15.52            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 15.31/15.52              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 15.31/15.52                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 15.31/15.52                ( m1_subset_1 @
% 15.31/15.52                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 15.31/15.52                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 15.31/15.52    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 15.31/15.52  thf('0', plain,
% 15.31/15.52      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1))
% 15.31/15.52        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ 
% 15.31/15.52             sk_C_1 @ sk_B)
% 15.31/15.52        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ 
% 15.31/15.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B))))),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf('1', plain,
% 15.31/15.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf(dt_k2_partfun1, axiom,
% 15.31/15.52    (![A:$i,B:$i,C:$i,D:$i]:
% 15.31/15.52     ( ( ( v1_funct_1 @ C ) & 
% 15.31/15.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.31/15.52       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 15.31/15.52         ( m1_subset_1 @
% 15.31/15.52           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 15.31/15.52           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 15.31/15.52  thf('2', plain,
% 15.31/15.52      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 15.31/15.52         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 15.31/15.52          | ~ (v1_funct_1 @ X39)
% 15.31/15.52          | (v1_funct_1 @ (k2_partfun1 @ X40 @ X41 @ X39 @ X42)))),
% 15.31/15.52      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 15.31/15.52  thf('3', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 15.31/15.52          | ~ (v1_funct_1 @ sk_D))),
% 15.31/15.52      inference('sup-', [status(thm)], ['1', '2'])).
% 15.31/15.52  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf('5', plain,
% 15.31/15.52      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 15.31/15.52      inference('demod', [status(thm)], ['3', '4'])).
% 15.31/15.52  thf('6', plain,
% 15.31/15.52      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ sk_C_1 @ 
% 15.31/15.52           sk_B)
% 15.31/15.52        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ 
% 15.31/15.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B))))),
% 15.31/15.52      inference('demod', [status(thm)], ['0', '5'])).
% 15.31/15.52  thf('7', plain,
% 15.31/15.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf(redefinition_k2_partfun1, axiom,
% 15.31/15.52    (![A:$i,B:$i,C:$i,D:$i]:
% 15.31/15.52     ( ( ( v1_funct_1 @ C ) & 
% 15.31/15.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.31/15.52       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 15.31/15.52  thf('8', plain,
% 15.31/15.52      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 15.31/15.52         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 15.31/15.52          | ~ (v1_funct_1 @ X43)
% 15.31/15.52          | ((k2_partfun1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 15.31/15.52      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 15.31/15.52  thf('9', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 15.31/15.52          | ~ (v1_funct_1 @ sk_D))),
% 15.31/15.52      inference('sup-', [status(thm)], ['7', '8'])).
% 15.31/15.52  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf('11', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 15.31/15.52      inference('demod', [status(thm)], ['9', '10'])).
% 15.31/15.52  thf('12', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 15.31/15.52      inference('demod', [status(thm)], ['9', '10'])).
% 15.31/15.52  thf('13', plain,
% 15.31/15.52      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C_1) @ sk_C_1 @ sk_B)
% 15.31/15.52        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C_1) @ 
% 15.31/15.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B))))),
% 15.31/15.52      inference('demod', [status(thm)], ['6', '11', '12'])).
% 15.31/15.52  thf('14', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf(d1_funct_2, axiom,
% 15.31/15.52    (![A:$i,B:$i,C:$i]:
% 15.31/15.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.31/15.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.31/15.52           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 15.31/15.52             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 15.31/15.52         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.31/15.52           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 15.31/15.52             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 15.31/15.52  thf(zf_stmt_1, axiom,
% 15.31/15.52    (![B:$i,A:$i]:
% 15.31/15.52     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.31/15.52       ( zip_tseitin_0 @ B @ A ) ))).
% 15.31/15.52  thf('15', plain,
% 15.31/15.52      (![X31 : $i, X32 : $i]:
% 15.31/15.52         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.31/15.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 15.31/15.52  thf('16', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 15.31/15.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.31/15.52  thf('17', plain,
% 15.31/15.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.31/15.52         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 15.31/15.52      inference('sup+', [status(thm)], ['15', '16'])).
% 15.31/15.52  thf('18', plain,
% 15.31/15.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 15.31/15.52  thf(zf_stmt_3, axiom,
% 15.31/15.52    (![C:$i,B:$i,A:$i]:
% 15.31/15.52     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 15.31/15.52       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 15.31/15.52  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 15.31/15.52  thf(zf_stmt_5, axiom,
% 15.31/15.52    (![A:$i,B:$i,C:$i]:
% 15.31/15.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.31/15.52       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 15.31/15.52         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.31/15.52           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 15.31/15.52             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 15.31/15.52  thf('19', plain,
% 15.31/15.52      (![X36 : $i, X37 : $i, X38 : $i]:
% 15.31/15.52         (~ (zip_tseitin_0 @ X36 @ X37)
% 15.31/15.52          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 15.31/15.52          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.31/15.52  thf('20', plain,
% 15.31/15.52      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 15.31/15.52      inference('sup-', [status(thm)], ['18', '19'])).
% 15.31/15.52  thf('21', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 15.31/15.52      inference('sup-', [status(thm)], ['17', '20'])).
% 15.31/15.52  thf('22', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf('23', plain,
% 15.31/15.52      (![X33 : $i, X34 : $i, X35 : $i]:
% 15.31/15.52         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 15.31/15.52          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 15.31/15.52          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.31/15.52  thf('24', plain,
% 15.31/15.52      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 15.31/15.52        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 15.31/15.52      inference('sup-', [status(thm)], ['22', '23'])).
% 15.31/15.52  thf('25', plain,
% 15.31/15.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf(redefinition_k1_relset_1, axiom,
% 15.31/15.52    (![A:$i,B:$i,C:$i]:
% 15.31/15.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.31/15.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 15.31/15.52  thf('26', plain,
% 15.31/15.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 15.31/15.52         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 15.31/15.52          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 15.31/15.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.31/15.52  thf('27', plain,
% 15.31/15.52      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 15.31/15.52      inference('sup-', [status(thm)], ['25', '26'])).
% 15.31/15.52  thf('28', plain,
% 15.31/15.52      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.31/15.52      inference('demod', [status(thm)], ['24', '27'])).
% 15.31/15.52  thf('29', plain,
% 15.31/15.52      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.31/15.52      inference('sup-', [status(thm)], ['21', '28'])).
% 15.31/15.52  thf('30', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 15.31/15.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.31/15.52  thf(d10_xboole_0, axiom,
% 15.31/15.52    (![A:$i,B:$i]:
% 15.31/15.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 15.31/15.52  thf('31', plain,
% 15.31/15.52      (![X4 : $i, X6 : $i]:
% 15.31/15.52         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 15.31/15.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.31/15.52  thf('32', plain,
% 15.31/15.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 15.31/15.52      inference('sup-', [status(thm)], ['30', '31'])).
% 15.31/15.52  thf('33', plain,
% 15.31/15.52      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((sk_B) = (k1_xboole_0)))),
% 15.31/15.52      inference('sup-', [status(thm)], ['29', '32'])).
% 15.31/15.52  thf('34', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf('35', plain,
% 15.31/15.52      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.31/15.52      inference('split', [status(esa)], ['34'])).
% 15.31/15.52  thf('36', plain,
% 15.31/15.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('split', [status(esa)], ['34'])).
% 15.31/15.52  thf('37', plain,
% 15.31/15.52      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ sk_C_1 @ 
% 15.31/15.52           sk_B)
% 15.31/15.52        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ 
% 15.31/15.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B))))),
% 15.31/15.52      inference('demod', [status(thm)], ['0', '5'])).
% 15.31/15.52  thf('38', plain,
% 15.31/15.52      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C_1) @ 
% 15.31/15.52            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))
% 15.31/15.52         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ 
% 15.31/15.52              sk_C_1 @ sk_B)))
% 15.31/15.52         <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('sup-', [status(thm)], ['36', '37'])).
% 15.31/15.52  thf('39', plain,
% 15.31/15.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('split', [status(esa)], ['34'])).
% 15.31/15.52  thf('40', plain,
% 15.31/15.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf('41', plain,
% 15.31/15.52      (((m1_subset_1 @ sk_D @ 
% 15.31/15.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 15.31/15.52         <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('sup+', [status(thm)], ['39', '40'])).
% 15.31/15.52  thf(t113_zfmisc_1, axiom,
% 15.31/15.52    (![A:$i,B:$i]:
% 15.31/15.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 15.31/15.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 15.31/15.52  thf('42', plain,
% 15.31/15.52      (![X9 : $i, X10 : $i]:
% 15.31/15.52         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 15.31/15.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 15.31/15.52  thf('43', plain,
% 15.31/15.52      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 15.31/15.52      inference('simplify', [status(thm)], ['42'])).
% 15.31/15.52  thf('44', plain,
% 15.31/15.52      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 15.31/15.52         <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('demod', [status(thm)], ['41', '43'])).
% 15.31/15.52  thf(t3_subset, axiom,
% 15.31/15.52    (![A:$i,B:$i]:
% 15.31/15.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 15.31/15.52  thf('45', plain,
% 15.31/15.52      (![X11 : $i, X12 : $i]:
% 15.31/15.52         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 15.31/15.52      inference('cnf', [status(esa)], [t3_subset])).
% 15.31/15.52  thf('46', plain,
% 15.31/15.52      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('sup-', [status(thm)], ['44', '45'])).
% 15.31/15.52  thf('47', plain,
% 15.31/15.52      (![X4 : $i, X6 : $i]:
% 15.31/15.52         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 15.31/15.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.31/15.52  thf('48', plain,
% 15.31/15.52      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 15.31/15.52         <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('sup-', [status(thm)], ['46', '47'])).
% 15.31/15.52  thf('49', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 15.31/15.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.31/15.52  thf('50', plain,
% 15.31/15.52      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('demod', [status(thm)], ['48', '49'])).
% 15.31/15.52  thf('51', plain,
% 15.31/15.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('split', [status(esa)], ['34'])).
% 15.31/15.52  thf('52', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf('53', plain,
% 15.31/15.52      (((r1_tarski @ sk_C_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('sup+', [status(thm)], ['51', '52'])).
% 15.31/15.52  thf('54', plain,
% 15.31/15.52      (![X4 : $i, X6 : $i]:
% 15.31/15.52         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 15.31/15.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.31/15.52  thf('55', plain,
% 15.31/15.52      (((~ (r1_tarski @ k1_xboole_0 @ sk_C_1) | ((k1_xboole_0) = (sk_C_1))))
% 15.31/15.52         <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('sup-', [status(thm)], ['53', '54'])).
% 15.31/15.52  thf('56', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 15.31/15.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.31/15.52  thf('57', plain,
% 15.31/15.52      ((((k1_xboole_0) = (sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('demod', [status(thm)], ['55', '56'])).
% 15.31/15.52  thf('58', plain,
% 15.31/15.52      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('demod', [status(thm)], ['48', '49'])).
% 15.31/15.52  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf('60', plain,
% 15.31/15.52      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('sup+', [status(thm)], ['58', '59'])).
% 15.31/15.52  thf('61', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 15.31/15.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.31/15.52  thf('62', plain,
% 15.31/15.52      (![X11 : $i, X13 : $i]:
% 15.31/15.52         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 15.31/15.52      inference('cnf', [status(esa)], [t3_subset])).
% 15.31/15.52  thf('63', plain,
% 15.31/15.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 15.31/15.52      inference('sup-', [status(thm)], ['61', '62'])).
% 15.31/15.52  thf('64', plain,
% 15.31/15.52      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 15.31/15.52         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 15.31/15.52          | ~ (v1_funct_1 @ X43)
% 15.31/15.52          | ((k2_partfun1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 15.31/15.52      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 15.31/15.52  thf('65', plain,
% 15.31/15.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.31/15.52         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 15.31/15.52            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 15.31/15.52          | ~ (v1_funct_1 @ k1_xboole_0))),
% 15.31/15.52      inference('sup-', [status(thm)], ['63', '64'])).
% 15.31/15.52  thf(t88_relat_1, axiom,
% 15.31/15.52    (![A:$i,B:$i]:
% 15.31/15.52     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 15.31/15.52  thf('66', plain,
% 15.31/15.52      (![X18 : $i, X19 : $i]:
% 15.31/15.52         ((r1_tarski @ (k7_relat_1 @ X18 @ X19) @ X18) | ~ (v1_relat_1 @ X18))),
% 15.31/15.52      inference('cnf', [status(esa)], [t88_relat_1])).
% 15.31/15.52  thf('67', plain,
% 15.31/15.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 15.31/15.52      inference('sup-', [status(thm)], ['30', '31'])).
% 15.31/15.52  thf('68', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         (~ (v1_relat_1 @ k1_xboole_0)
% 15.31/15.52          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 15.31/15.52      inference('sup-', [status(thm)], ['66', '67'])).
% 15.31/15.52  thf('69', plain,
% 15.31/15.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 15.31/15.52      inference('sup-', [status(thm)], ['61', '62'])).
% 15.31/15.52  thf(cc1_relset_1, axiom,
% 15.31/15.52    (![A:$i,B:$i,C:$i]:
% 15.31/15.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.31/15.52       ( v1_relat_1 @ C ) ))).
% 15.31/15.52  thf('70', plain,
% 15.31/15.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 15.31/15.52         ((v1_relat_1 @ X22)
% 15.31/15.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 15.31/15.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.31/15.52  thf('71', plain, ((v1_relat_1 @ k1_xboole_0)),
% 15.31/15.52      inference('sup-', [status(thm)], ['69', '70'])).
% 15.31/15.52  thf('72', plain,
% 15.31/15.52      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.31/15.52      inference('demod', [status(thm)], ['68', '71'])).
% 15.31/15.52  thf('73', plain,
% 15.31/15.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.31/15.52         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 15.31/15.52          | ~ (v1_funct_1 @ k1_xboole_0))),
% 15.31/15.52      inference('demod', [status(thm)], ['65', '72'])).
% 15.31/15.52  thf('74', plain,
% 15.31/15.52      ((![X0 : $i, X1 : $i, X2 : $i]:
% 15.31/15.52          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 15.31/15.52         <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('sup-', [status(thm)], ['60', '73'])).
% 15.31/15.52  thf('75', plain,
% 15.31/15.52      ((((k1_xboole_0) = (sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('demod', [status(thm)], ['55', '56'])).
% 15.31/15.52  thf('76', plain,
% 15.31/15.52      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 15.31/15.52      inference('simplify', [status(thm)], ['42'])).
% 15.31/15.52  thf('77', plain,
% 15.31/15.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 15.31/15.52      inference('sup-', [status(thm)], ['61', '62'])).
% 15.31/15.52  thf('78', plain,
% 15.31/15.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('split', [status(esa)], ['34'])).
% 15.31/15.52  thf('79', plain,
% 15.31/15.52      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('demod', [status(thm)], ['48', '49'])).
% 15.31/15.52  thf('80', plain,
% 15.31/15.52      ((((k1_xboole_0) = (sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('demod', [status(thm)], ['55', '56'])).
% 15.31/15.52  thf('81', plain,
% 15.31/15.52      ((![X0 : $i, X1 : $i, X2 : $i]:
% 15.31/15.52          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 15.31/15.52         <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('sup-', [status(thm)], ['60', '73'])).
% 15.31/15.52  thf('82', plain,
% 15.31/15.52      ((((k1_xboole_0) = (sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.31/15.52      inference('demod', [status(thm)], ['55', '56'])).
% 15.31/15.52  thf('83', plain,
% 15.31/15.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 15.31/15.52      inference('sup-', [status(thm)], ['61', '62'])).
% 15.31/15.52  thf('84', plain,
% 15.31/15.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 15.31/15.52         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 15.31/15.52          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 15.31/15.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.31/15.52  thf('85', plain,
% 15.31/15.52      (![X0 : $i, X1 : $i]:
% 15.31/15.52         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 15.31/15.52      inference('sup-', [status(thm)], ['83', '84'])).
% 15.31/15.52  thf('86', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 15.31/15.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.31/15.52  thf('87', plain,
% 15.31/15.52      (![X0 : $i, X1 : $i]:
% 15.31/15.52         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 15.31/15.52      inference('sup-', [status(thm)], ['83', '84'])).
% 15.31/15.52  thf(t91_relat_1, axiom,
% 15.31/15.52    (![A:$i,B:$i]:
% 15.31/15.52     ( ( v1_relat_1 @ B ) =>
% 15.31/15.52       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 15.31/15.52         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 15.31/15.52  thf('88', plain,
% 15.31/15.52      (![X20 : $i, X21 : $i]:
% 15.31/15.52         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 15.31/15.52          | ((k1_relat_1 @ (k7_relat_1 @ X21 @ X20)) = (X20))
% 15.31/15.52          | ~ (v1_relat_1 @ X21))),
% 15.31/15.52      inference('cnf', [status(esa)], [t91_relat_1])).
% 15.31/15.52  thf('89', plain,
% 15.31/15.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.31/15.52         (~ (r1_tarski @ X2 @ (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))
% 15.31/15.52          | ~ (v1_relat_1 @ k1_xboole_0)
% 15.31/15.52          | ((k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ X2)) = (X2)))),
% 15.31/15.52      inference('sup-', [status(thm)], ['87', '88'])).
% 15.31/15.52  thf('90', plain, ((v1_relat_1 @ k1_xboole_0)),
% 15.31/15.52      inference('sup-', [status(thm)], ['69', '70'])).
% 15.31/15.52  thf('91', plain,
% 15.31/15.52      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.31/15.52      inference('demod', [status(thm)], ['68', '71'])).
% 15.31/15.52  thf('92', plain,
% 15.31/15.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.31/15.52         (~ (r1_tarski @ X2 @ (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))
% 15.31/15.52          | ((k1_relat_1 @ k1_xboole_0) = (X2)))),
% 15.31/15.52      inference('demod', [status(thm)], ['89', '90', '91'])).
% 15.31/15.52  thf('93', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 15.31/15.52      inference('sup-', [status(thm)], ['86', '92'])).
% 15.31/15.52  thf('94', plain,
% 15.31/15.52      (![X0 : $i, X1 : $i]:
% 15.31/15.52         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 15.31/15.52      inference('demod', [status(thm)], ['85', '93'])).
% 15.31/15.52  thf('95', plain,
% 15.31/15.52      (![X33 : $i, X34 : $i, X35 : $i]:
% 15.31/15.52         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 15.31/15.52          | (v1_funct_2 @ X35 @ X33 @ X34)
% 15.31/15.52          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.31/15.52  thf('96', plain,
% 15.31/15.52      (![X0 : $i, X1 : $i]:
% 15.31/15.52         (((X1) != (k1_xboole_0))
% 15.31/15.52          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 15.31/15.52          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 15.31/15.52      inference('sup-', [status(thm)], ['94', '95'])).
% 15.31/15.52  thf('97', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 15.31/15.52          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 15.31/15.52      inference('simplify', [status(thm)], ['96'])).
% 15.31/15.52  thf('98', plain,
% 15.31/15.52      (![X31 : $i, X32 : $i]:
% 15.31/15.52         ((zip_tseitin_0 @ X31 @ X32) | ((X32) != (k1_xboole_0)))),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.31/15.52  thf('99', plain, (![X31 : $i]: (zip_tseitin_0 @ X31 @ k1_xboole_0)),
% 15.31/15.52      inference('simplify', [status(thm)], ['98'])).
% 15.31/15.52  thf('100', plain,
% 15.31/15.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 15.31/15.52      inference('sup-', [status(thm)], ['61', '62'])).
% 15.31/15.52  thf('101', plain,
% 15.31/15.52      (![X36 : $i, X37 : $i, X38 : $i]:
% 15.31/15.52         (~ (zip_tseitin_0 @ X36 @ X37)
% 15.31/15.52          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 15.31/15.52          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.31/15.52  thf('102', plain,
% 15.31/15.52      (![X0 : $i, X1 : $i]:
% 15.31/15.52         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 15.31/15.52      inference('sup-', [status(thm)], ['100', '101'])).
% 15.31/15.52  thf('103', plain,
% 15.31/15.52      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 15.31/15.52      inference('sup-', [status(thm)], ['99', '102'])).
% 15.31/15.52  thf('104', plain,
% 15.31/15.52      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 15.31/15.52      inference('demod', [status(thm)], ['97', '103'])).
% 15.31/15.52  thf('105', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 15.31/15.52      inference('demod', [status(thm)],
% 15.31/15.52                ['38', '50', '57', '74', '75', '76', '77', '78', '79', '80', 
% 15.31/15.52                 '81', '82', '104'])).
% 15.31/15.52  thf('106', plain,
% 15.31/15.52      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 15.31/15.52      inference('split', [status(esa)], ['34'])).
% 15.31/15.52  thf('107', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 15.31/15.52      inference('sat_resolution*', [status(thm)], ['105', '106'])).
% 15.31/15.52  thf('108', plain, (((sk_B) != (k1_xboole_0))),
% 15.31/15.52      inference('simpl_trail', [status(thm)], ['35', '107'])).
% 15.31/15.52  thf('109', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 15.31/15.52      inference('simplify_reflect-', [status(thm)], ['33', '108'])).
% 15.31/15.52  thf('110', plain,
% 15.31/15.52      (![X20 : $i, X21 : $i]:
% 15.31/15.52         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 15.31/15.52          | ((k1_relat_1 @ (k7_relat_1 @ X21 @ X20)) = (X20))
% 15.31/15.52          | ~ (v1_relat_1 @ X21))),
% 15.31/15.52      inference('cnf', [status(esa)], [t91_relat_1])).
% 15.31/15.52  thf('111', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         (~ (r1_tarski @ X0 @ sk_A)
% 15.31/15.52          | ~ (v1_relat_1 @ sk_D)
% 15.31/15.52          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 15.31/15.52      inference('sup-', [status(thm)], ['109', '110'])).
% 15.31/15.52  thf('112', plain,
% 15.31/15.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf('113', plain,
% 15.31/15.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 15.31/15.52         ((v1_relat_1 @ X22)
% 15.31/15.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 15.31/15.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.31/15.52  thf('114', plain, ((v1_relat_1 @ sk_D)),
% 15.31/15.52      inference('sup-', [status(thm)], ['112', '113'])).
% 15.31/15.52  thf('115', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         (~ (r1_tarski @ X0 @ sk_A)
% 15.31/15.52          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 15.31/15.52      inference('demod', [status(thm)], ['111', '114'])).
% 15.31/15.52  thf('116', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C_1)) = (sk_C_1))),
% 15.31/15.52      inference('sup-', [status(thm)], ['14', '115'])).
% 15.31/15.52  thf('117', plain,
% 15.31/15.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf('118', plain,
% 15.31/15.52      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 15.31/15.52         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 15.31/15.52          | ~ (v1_funct_1 @ X39)
% 15.31/15.52          | (m1_subset_1 @ (k2_partfun1 @ X40 @ X41 @ X39 @ X42) @ 
% 15.31/15.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 15.31/15.52      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 15.31/15.52  thf('119', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 15.31/15.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 15.31/15.52          | ~ (v1_funct_1 @ sk_D))),
% 15.31/15.52      inference('sup-', [status(thm)], ['117', '118'])).
% 15.31/15.52  thf('120', plain, ((v1_funct_1 @ sk_D)),
% 15.31/15.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.52  thf('121', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 15.31/15.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.31/15.52      inference('demod', [status(thm)], ['119', '120'])).
% 15.31/15.52  thf('122', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 15.31/15.52      inference('demod', [status(thm)], ['9', '10'])).
% 15.31/15.52  thf('123', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.31/15.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.31/15.52      inference('demod', [status(thm)], ['121', '122'])).
% 15.31/15.52  thf(cc2_relset_1, axiom,
% 15.31/15.52    (![A:$i,B:$i,C:$i]:
% 15.31/15.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.31/15.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 15.31/15.52  thf('124', plain,
% 15.31/15.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 15.31/15.52         ((v5_relat_1 @ X25 @ X27)
% 15.31/15.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 15.31/15.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 15.31/15.52  thf('125', plain,
% 15.31/15.52      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 15.31/15.52      inference('sup-', [status(thm)], ['123', '124'])).
% 15.31/15.52  thf(d19_relat_1, axiom,
% 15.31/15.52    (![A:$i,B:$i]:
% 15.31/15.52     ( ( v1_relat_1 @ B ) =>
% 15.31/15.52       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 15.31/15.52  thf('126', plain,
% 15.31/15.52      (![X14 : $i, X15 : $i]:
% 15.31/15.52         (~ (v5_relat_1 @ X14 @ X15)
% 15.31/15.52          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 15.31/15.52          | ~ (v1_relat_1 @ X14))),
% 15.31/15.52      inference('cnf', [status(esa)], [d19_relat_1])).
% 15.31/15.52  thf('127', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 15.31/15.52          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 15.31/15.52      inference('sup-', [status(thm)], ['125', '126'])).
% 15.31/15.52  thf('128', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.31/15.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.31/15.52      inference('demod', [status(thm)], ['121', '122'])).
% 15.31/15.52  thf('129', plain,
% 15.31/15.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 15.31/15.52         ((v1_relat_1 @ X22)
% 15.31/15.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 15.31/15.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.31/15.52  thf('130', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 15.31/15.52      inference('sup-', [status(thm)], ['128', '129'])).
% 15.31/15.52  thf('131', plain,
% 15.31/15.52      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 15.31/15.52      inference('demod', [status(thm)], ['127', '130'])).
% 15.31/15.52  thf(t4_funct_2, axiom,
% 15.31/15.52    (![A:$i,B:$i]:
% 15.31/15.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 15.31/15.52       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 15.31/15.52         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 15.31/15.52           ( m1_subset_1 @
% 15.31/15.52             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 15.31/15.52  thf('132', plain,
% 15.31/15.52      (![X47 : $i, X48 : $i]:
% 15.31/15.52         (~ (r1_tarski @ (k2_relat_1 @ X47) @ X48)
% 15.31/15.52          | (v1_funct_2 @ X47 @ (k1_relat_1 @ X47) @ X48)
% 15.31/15.52          | ~ (v1_funct_1 @ X47)
% 15.31/15.52          | ~ (v1_relat_1 @ X47))),
% 15.31/15.52      inference('cnf', [status(esa)], [t4_funct_2])).
% 15.31/15.52  thf('133', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 15.31/15.52          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 15.31/15.52          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.31/15.52             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 15.31/15.52      inference('sup-', [status(thm)], ['131', '132'])).
% 15.31/15.52  thf('134', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 15.31/15.52      inference('sup-', [status(thm)], ['128', '129'])).
% 15.31/15.52  thf('135', plain,
% 15.31/15.52      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 15.31/15.52      inference('demod', [status(thm)], ['3', '4'])).
% 15.31/15.52  thf('136', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 15.31/15.52      inference('demod', [status(thm)], ['9', '10'])).
% 15.31/15.52  thf('137', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 15.31/15.52      inference('demod', [status(thm)], ['135', '136'])).
% 15.31/15.52  thf('138', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.31/15.52          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 15.31/15.52      inference('demod', [status(thm)], ['133', '134', '137'])).
% 15.31/15.52  thf('139', plain,
% 15.31/15.52      ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C_1) @ sk_C_1 @ sk_B)),
% 15.31/15.52      inference('sup+', [status(thm)], ['116', '138'])).
% 15.31/15.52  thf('140', plain,
% 15.31/15.52      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C_1) @ 
% 15.31/15.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 15.31/15.52      inference('demod', [status(thm)], ['13', '139'])).
% 15.31/15.52  thf('141', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C_1)) = (sk_C_1))),
% 15.31/15.52      inference('sup-', [status(thm)], ['14', '115'])).
% 15.31/15.52  thf('142', plain,
% 15.31/15.52      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 15.31/15.52      inference('demod', [status(thm)], ['127', '130'])).
% 15.31/15.52  thf('143', plain,
% 15.31/15.52      (![X47 : $i, X48 : $i]:
% 15.31/15.52         (~ (r1_tarski @ (k2_relat_1 @ X47) @ X48)
% 15.31/15.52          | (m1_subset_1 @ X47 @ 
% 15.31/15.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ X48)))
% 15.31/15.52          | ~ (v1_funct_1 @ X47)
% 15.31/15.52          | ~ (v1_relat_1 @ X47))),
% 15.31/15.52      inference('cnf', [status(esa)], [t4_funct_2])).
% 15.31/15.52  thf('144', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 15.31/15.52          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 15.31/15.52          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.31/15.52             (k1_zfmisc_1 @ 
% 15.31/15.52              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 15.31/15.52      inference('sup-', [status(thm)], ['142', '143'])).
% 15.31/15.52  thf('145', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 15.31/15.52      inference('sup-', [status(thm)], ['128', '129'])).
% 15.31/15.52  thf('146', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 15.31/15.52      inference('demod', [status(thm)], ['135', '136'])).
% 15.31/15.52  thf('147', plain,
% 15.31/15.52      (![X0 : $i]:
% 15.31/15.52         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 15.31/15.52          (k1_zfmisc_1 @ 
% 15.31/15.52           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 15.31/15.52      inference('demod', [status(thm)], ['144', '145', '146'])).
% 15.31/15.52  thf('148', plain,
% 15.31/15.52      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C_1) @ 
% 15.31/15.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 15.31/15.52      inference('sup+', [status(thm)], ['141', '147'])).
% 15.31/15.52  thf('149', plain, ($false), inference('demod', [status(thm)], ['140', '148'])).
% 15.31/15.52  
% 15.31/15.52  % SZS output end Refutation
% 15.31/15.52  
% 15.31/15.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
