%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5eW3ym8gx2

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:42 EST 2020

% Result     : Theorem 38.76s
% Output     : Refutation 38.76s
% Verified   : 
% Statistics : Number of formulae       :  208 (1950 expanded)
%              Number of leaves         :   40 ( 595 expanded)
%              Depth                    :   27
%              Number of atoms          : 1592 (26988 expanded)
%              Number of equality atoms :  140 (1818 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('34',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('38',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('39',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35 != k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ( X37 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('44',plain,(
    ! [X36: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X36 @ k1_xboole_0 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('46',plain,(
    ! [X36: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X36 @ k1_xboole_0 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('50',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X9 @ X10 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('53',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('58',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('66',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','70'])).

thf('72',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('75',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('76',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('80',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X18 ) ) )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('81',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('85',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('87',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('90',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
      | ( k1_xboole_0 = sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('92',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('94',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('97',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ( ( k2_partfun1 @ X43 @ X44 @ X42 @ X45 )
        = ( k7_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('103',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('104',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('105',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('106',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('107',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('108',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','66'])).

thf('110',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('115',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['112','115'])).

thf('117',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['76','85','92','101','102','103','104','105','106','107','108','116'])).

thf('118',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('119',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['117','118'])).

thf('120',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['73','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['71','120'])).

thf('122',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','121'])).

thf('123',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('128',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['125','128'])).

thf('130',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','129'])).

thf('131',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X9 @ X10 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('132',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('133',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( r1_tarski @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['131','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['126','127'])).

thf('137',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('138',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['130','139'])).

thf('141',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','140'])).

thf('142',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['13','141'])).

thf('143',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','140'])).

thf('144',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('145',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','129'])).

thf('147',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('149',plain,
    ( ( sk_C != sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','140'])).

thf('152',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('153',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('158',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ( zip_tseitin_0 @ sk_B @ X1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X1 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('161',plain,
    ( ! [X1: $i] :
        ( zip_tseitin_0 @ sk_B @ X1 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['159','160'])).

thf('162',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['117','118'])).

thf('163',plain,(
    ! [X1: $i] :
      ( zip_tseitin_0 @ sk_B @ X1 ) ),
    inference(simpl_trail,[status(thm)],['161','162'])).

thf('164',plain,(
    zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['153','163'])).

thf('165',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['150','164'])).

thf('166',plain,(
    $false ),
    inference(demod,[status(thm)],['142','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5eW3ym8gx2
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 38.76/38.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 38.76/38.95  % Solved by: fo/fo7.sh
% 38.76/38.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 38.76/38.95  % done 32644 iterations in 38.484s
% 38.76/38.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 38.76/38.95  % SZS output start Refutation
% 38.76/38.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 38.76/38.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 38.76/38.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 38.76/38.95  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 38.76/38.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 38.76/38.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 38.76/38.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 38.76/38.95  thf(sk_A_type, type, sk_A: $i).
% 38.76/38.95  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 38.76/38.95  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 38.76/38.95  thf(sk_B_type, type, sk_B: $i).
% 38.76/38.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 38.76/38.95  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 38.76/38.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 38.76/38.95  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 38.76/38.95  thf(sk_C_type, type, sk_C: $i).
% 38.76/38.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 38.76/38.95  thf(sk_D_type, type, sk_D: $i).
% 38.76/38.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 38.76/38.95  thf(t38_funct_2, conjecture,
% 38.76/38.95    (![A:$i,B:$i,C:$i,D:$i]:
% 38.76/38.95     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 38.76/38.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 38.76/38.95       ( ( r1_tarski @ C @ A ) =>
% 38.76/38.95         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 38.76/38.95           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 38.76/38.95             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 38.76/38.95             ( m1_subset_1 @
% 38.76/38.95               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 38.76/38.95               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 38.76/38.95  thf(zf_stmt_0, negated_conjecture,
% 38.76/38.95    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 38.76/38.95        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 38.76/38.95            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 38.76/38.95          ( ( r1_tarski @ C @ A ) =>
% 38.76/38.95            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 38.76/38.95              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 38.76/38.95                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 38.76/38.95                ( m1_subset_1 @
% 38.76/38.95                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 38.76/38.95                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 38.76/38.95    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 38.76/38.95  thf('0', plain,
% 38.76/38.95      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 38.76/38.95        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 38.76/38.95             sk_B)
% 38.76/38.95        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 38.76/38.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.76/38.95  thf('1', plain,
% 38.76/38.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.76/38.95  thf(dt_k2_partfun1, axiom,
% 38.76/38.95    (![A:$i,B:$i,C:$i,D:$i]:
% 38.76/38.95     ( ( ( v1_funct_1 @ C ) & 
% 38.76/38.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 38.76/38.95       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 38.76/38.95         ( m1_subset_1 @
% 38.76/38.95           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 38.76/38.95           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 38.76/38.95  thf('2', plain,
% 38.76/38.95      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 38.76/38.95         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 38.76/38.95          | ~ (v1_funct_1 @ X38)
% 38.76/38.95          | (v1_funct_1 @ (k2_partfun1 @ X39 @ X40 @ X38 @ X41)))),
% 38.76/38.95      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 38.76/38.95  thf('3', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 38.76/38.95          | ~ (v1_funct_1 @ sk_D))),
% 38.76/38.95      inference('sup-', [status(thm)], ['1', '2'])).
% 38.76/38.95  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.76/38.95  thf('5', plain,
% 38.76/38.95      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 38.76/38.95      inference('demod', [status(thm)], ['3', '4'])).
% 38.76/38.95  thf('6', plain,
% 38.76/38.95      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 38.76/38.95        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 38.76/38.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 38.76/38.95      inference('demod', [status(thm)], ['0', '5'])).
% 38.76/38.95  thf('7', plain,
% 38.76/38.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.76/38.95  thf(redefinition_k2_partfun1, axiom,
% 38.76/38.95    (![A:$i,B:$i,C:$i,D:$i]:
% 38.76/38.95     ( ( ( v1_funct_1 @ C ) & 
% 38.76/38.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 38.76/38.95       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 38.76/38.95  thf('8', plain,
% 38.76/38.95      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 38.76/38.95         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 38.76/38.95          | ~ (v1_funct_1 @ X42)
% 38.76/38.95          | ((k2_partfun1 @ X43 @ X44 @ X42 @ X45) = (k7_relat_1 @ X42 @ X45)))),
% 38.76/38.95      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 38.76/38.95  thf('9', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 38.76/38.95          | ~ (v1_funct_1 @ sk_D))),
% 38.76/38.95      inference('sup-', [status(thm)], ['7', '8'])).
% 38.76/38.95  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.76/38.95  thf('11', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 38.76/38.95      inference('demod', [status(thm)], ['9', '10'])).
% 38.76/38.95  thf('12', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 38.76/38.95      inference('demod', [status(thm)], ['9', '10'])).
% 38.76/38.95  thf('13', plain,
% 38.76/38.95      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 38.76/38.95        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 38.76/38.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 38.76/38.95      inference('demod', [status(thm)], ['6', '11', '12'])).
% 38.76/38.95  thf(d10_xboole_0, axiom,
% 38.76/38.95    (![A:$i,B:$i]:
% 38.76/38.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 38.76/38.95  thf('14', plain,
% 38.76/38.95      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 38.76/38.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 38.76/38.95  thf('15', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 38.76/38.95      inference('simplify', [status(thm)], ['14'])).
% 38.76/38.95  thf('16', plain, ((r1_tarski @ sk_C @ sk_A)),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.76/38.95  thf(d1_funct_2, axiom,
% 38.76/38.95    (![A:$i,B:$i,C:$i]:
% 38.76/38.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 38.76/38.95       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 38.76/38.95           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 38.76/38.95             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 38.76/38.95         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 38.76/38.95           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 38.76/38.95             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 38.76/38.95  thf(zf_stmt_1, axiom,
% 38.76/38.95    (![B:$i,A:$i]:
% 38.76/38.95     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 38.76/38.95       ( zip_tseitin_0 @ B @ A ) ))).
% 38.76/38.95  thf('17', plain,
% 38.76/38.95      (![X30 : $i, X31 : $i]:
% 38.76/38.95         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 38.76/38.95  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 38.76/38.95  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 38.76/38.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 38.76/38.95  thf('19', plain,
% 38.76/38.95      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 38.76/38.95      inference('sup+', [status(thm)], ['17', '18'])).
% 38.76/38.95  thf('20', plain,
% 38.76/38.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.76/38.95  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 38.76/38.95  thf(zf_stmt_3, axiom,
% 38.76/38.95    (![C:$i,B:$i,A:$i]:
% 38.76/38.95     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 38.76/38.95       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 38.76/38.95  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 38.76/38.95  thf(zf_stmt_5, axiom,
% 38.76/38.95    (![A:$i,B:$i,C:$i]:
% 38.76/38.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 38.76/38.95       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 38.76/38.95         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 38.76/38.95           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 38.76/38.95             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 38.76/38.95  thf('21', plain,
% 38.76/38.95      (![X35 : $i, X36 : $i, X37 : $i]:
% 38.76/38.95         (~ (zip_tseitin_0 @ X35 @ X36)
% 38.76/38.95          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 38.76/38.95          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 38.76/38.95  thf('22', plain,
% 38.76/38.95      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 38.76/38.95      inference('sup-', [status(thm)], ['20', '21'])).
% 38.76/38.95  thf('23', plain,
% 38.76/38.95      (((v1_xboole_0 @ sk_B) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 38.76/38.95      inference('sup-', [status(thm)], ['19', '22'])).
% 38.76/38.95  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.76/38.95  thf('25', plain,
% 38.76/38.95      (![X32 : $i, X33 : $i, X34 : $i]:
% 38.76/38.95         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 38.76/38.95          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 38.76/38.95          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 38.76/38.95  thf('26', plain,
% 38.76/38.95      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 38.76/38.95        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 38.76/38.95      inference('sup-', [status(thm)], ['24', '25'])).
% 38.76/38.95  thf('27', plain,
% 38.76/38.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.76/38.95  thf(redefinition_k1_relset_1, axiom,
% 38.76/38.95    (![A:$i,B:$i,C:$i]:
% 38.76/38.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 38.76/38.95       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 38.76/38.95  thf('28', plain,
% 38.76/38.95      (![X19 : $i, X20 : $i, X21 : $i]:
% 38.76/38.95         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 38.76/38.95          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 38.76/38.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 38.76/38.95  thf('29', plain,
% 38.76/38.95      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 38.76/38.95      inference('sup-', [status(thm)], ['27', '28'])).
% 38.76/38.95  thf('30', plain,
% 38.76/38.95      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 38.76/38.95      inference('demod', [status(thm)], ['26', '29'])).
% 38.76/38.95  thf('31', plain, (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 38.76/38.95      inference('sup-', [status(thm)], ['23', '30'])).
% 38.76/38.95  thf('32', plain, (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 38.76/38.95      inference('sup-', [status(thm)], ['23', '30'])).
% 38.76/38.95  thf(l13_xboole_0, axiom,
% 38.76/38.95    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 38.76/38.95  thf('33', plain,
% 38.76/38.95      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 38.76/38.95      inference('cnf', [status(esa)], [l13_xboole_0])).
% 38.76/38.95  thf('34', plain,
% 38.76/38.95      (![X30 : $i, X31 : $i]:
% 38.76/38.95         ((zip_tseitin_0 @ X30 @ X31) | ((X31) != (k1_xboole_0)))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 38.76/38.95  thf('35', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 38.76/38.95      inference('simplify', [status(thm)], ['34'])).
% 38.76/38.95  thf('36', plain,
% 38.76/38.95      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 38.76/38.95      inference('sup+', [status(thm)], ['33', '35'])).
% 38.76/38.95  thf('37', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X0 @ sk_B))),
% 38.76/38.95      inference('sup-', [status(thm)], ['32', '36'])).
% 38.76/38.95  thf(t4_subset_1, axiom,
% 38.76/38.95    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 38.76/38.95  thf('38', plain,
% 38.76/38.95      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 38.76/38.95      inference('cnf', [status(esa)], [t4_subset_1])).
% 38.76/38.95  thf('39', plain,
% 38.76/38.95      (![X35 : $i, X36 : $i, X37 : $i]:
% 38.76/38.95         (~ (zip_tseitin_0 @ X35 @ X36)
% 38.76/38.95          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 38.76/38.95          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 38.76/38.95  thf('40', plain,
% 38.76/38.95      (![X0 : $i, X1 : $i]:
% 38.76/38.95         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 38.76/38.95      inference('sup-', [status(thm)], ['38', '39'])).
% 38.76/38.95  thf('41', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         (((sk_A) = (k1_relat_1 @ sk_D))
% 38.76/38.95          | (zip_tseitin_1 @ k1_xboole_0 @ X0 @ sk_B))),
% 38.76/38.95      inference('sup-', [status(thm)], ['37', '40'])).
% 38.76/38.95  thf('42', plain,
% 38.76/38.95      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 38.76/38.95      inference('cnf', [status(esa)], [l13_xboole_0])).
% 38.76/38.95  thf('43', plain,
% 38.76/38.95      (![X35 : $i, X36 : $i, X37 : $i]:
% 38.76/38.95         (((X35) != (k1_xboole_0))
% 38.76/38.95          | ((X36) = (k1_xboole_0))
% 38.76/38.95          | (v1_funct_2 @ X37 @ X36 @ X35)
% 38.76/38.95          | ((X37) != (k1_xboole_0))
% 38.76/38.95          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 38.76/38.95  thf('44', plain,
% 38.76/38.95      (![X36 : $i]:
% 38.76/38.95         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 38.76/38.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ k1_xboole_0)))
% 38.76/38.95          | (v1_funct_2 @ k1_xboole_0 @ X36 @ k1_xboole_0)
% 38.76/38.95          | ((X36) = (k1_xboole_0)))),
% 38.76/38.95      inference('simplify', [status(thm)], ['43'])).
% 38.76/38.95  thf('45', plain,
% 38.76/38.95      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 38.76/38.95      inference('cnf', [status(esa)], [t4_subset_1])).
% 38.76/38.95  thf('46', plain,
% 38.76/38.95      (![X36 : $i]:
% 38.76/38.95         ((v1_funct_2 @ k1_xboole_0 @ X36 @ k1_xboole_0)
% 38.76/38.95          | ((X36) = (k1_xboole_0)))),
% 38.76/38.95      inference('demod', [status(thm)], ['44', '45'])).
% 38.76/38.95  thf('47', plain,
% 38.76/38.95      (![X32 : $i, X33 : $i, X34 : $i]:
% 38.76/38.95         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 38.76/38.95          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 38.76/38.95          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 38.76/38.95  thf('48', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         (((X0) = (k1_xboole_0))
% 38.76/38.95          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 38.76/38.95          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 38.76/38.95      inference('sup-', [status(thm)], ['46', '47'])).
% 38.76/38.95  thf('49', plain,
% 38.76/38.95      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 38.76/38.95      inference('cnf', [status(esa)], [t4_subset_1])).
% 38.76/38.95  thf('50', plain,
% 38.76/38.95      (![X19 : $i, X20 : $i, X21 : $i]:
% 38.76/38.95         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 38.76/38.95          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 38.76/38.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 38.76/38.95  thf('51', plain,
% 38.76/38.95      (![X0 : $i, X1 : $i]:
% 38.76/38.95         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 38.76/38.95      inference('sup-', [status(thm)], ['49', '50'])).
% 38.76/38.95  thf(t88_relat_1, axiom,
% 38.76/38.95    (![A:$i,B:$i]:
% 38.76/38.95     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 38.76/38.95  thf('52', plain,
% 38.76/38.95      (![X9 : $i, X10 : $i]:
% 38.76/38.95         ((r1_tarski @ (k7_relat_1 @ X9 @ X10) @ X9) | ~ (v1_relat_1 @ X9))),
% 38.76/38.95      inference('cnf', [status(esa)], [t88_relat_1])).
% 38.76/38.95  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 38.76/38.95  thf('53', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 38.76/38.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 38.76/38.95  thf('54', plain,
% 38.76/38.95      (![X1 : $i, X3 : $i]:
% 38.76/38.95         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 38.76/38.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 38.76/38.95  thf('55', plain,
% 38.76/38.95      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 38.76/38.95      inference('sup-', [status(thm)], ['53', '54'])).
% 38.76/38.95  thf('56', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         (~ (v1_relat_1 @ k1_xboole_0)
% 38.76/38.95          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 38.76/38.95      inference('sup-', [status(thm)], ['52', '55'])).
% 38.76/38.95  thf('57', plain,
% 38.76/38.95      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 38.76/38.95      inference('cnf', [status(esa)], [t4_subset_1])).
% 38.76/38.95  thf(cc1_relset_1, axiom,
% 38.76/38.95    (![A:$i,B:$i,C:$i]:
% 38.76/38.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 38.76/38.95       ( v1_relat_1 @ C ) ))).
% 38.76/38.95  thf('58', plain,
% 38.76/38.95      (![X13 : $i, X14 : $i, X15 : $i]:
% 38.76/38.95         ((v1_relat_1 @ X13)
% 38.76/38.95          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 38.76/38.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 38.76/38.95  thf('59', plain, ((v1_relat_1 @ k1_xboole_0)),
% 38.76/38.95      inference('sup-', [status(thm)], ['57', '58'])).
% 38.76/38.95  thf('60', plain,
% 38.76/38.95      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 38.76/38.95      inference('demod', [status(thm)], ['56', '59'])).
% 38.76/38.95  thf('61', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 38.76/38.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 38.76/38.95  thf(t91_relat_1, axiom,
% 38.76/38.95    (![A:$i,B:$i]:
% 38.76/38.95     ( ( v1_relat_1 @ B ) =>
% 38.76/38.95       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 38.76/38.95         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 38.76/38.95  thf('62', plain,
% 38.76/38.95      (![X11 : $i, X12 : $i]:
% 38.76/38.95         (~ (r1_tarski @ X11 @ (k1_relat_1 @ X12))
% 38.76/38.95          | ((k1_relat_1 @ (k7_relat_1 @ X12 @ X11)) = (X11))
% 38.76/38.95          | ~ (v1_relat_1 @ X12))),
% 38.76/38.95      inference('cnf', [status(esa)], [t91_relat_1])).
% 38.76/38.95  thf('63', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         (~ (v1_relat_1 @ X0)
% 38.76/38.95          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 38.76/38.95      inference('sup-', [status(thm)], ['61', '62'])).
% 38.76/38.95  thf('64', plain,
% 38.76/38.95      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 38.76/38.95        | ~ (v1_relat_1 @ k1_xboole_0))),
% 38.76/38.95      inference('sup+', [status(thm)], ['60', '63'])).
% 38.76/38.95  thf('65', plain, ((v1_relat_1 @ k1_xboole_0)),
% 38.76/38.95      inference('sup-', [status(thm)], ['57', '58'])).
% 38.76/38.95  thf('66', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 38.76/38.95      inference('demod', [status(thm)], ['64', '65'])).
% 38.76/38.95  thf('67', plain,
% 38.76/38.95      (![X0 : $i, X1 : $i]:
% 38.76/38.95         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 38.76/38.95      inference('demod', [status(thm)], ['51', '66'])).
% 38.76/38.95  thf('68', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         (((X0) = (k1_xboole_0))
% 38.76/38.95          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 38.76/38.95          | ((X0) = (k1_xboole_0)))),
% 38.76/38.95      inference('demod', [status(thm)], ['48', '67'])).
% 38.76/38.95  thf('69', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 38.76/38.95          | ((X0) = (k1_xboole_0)))),
% 38.76/38.95      inference('simplify', [status(thm)], ['68'])).
% 38.76/38.95  thf('70', plain,
% 38.76/38.95      (![X0 : $i, X1 : $i]:
% 38.76/38.95         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 38.76/38.95          | ~ (v1_xboole_0 @ X0)
% 38.76/38.95          | ((X1) = (k1_xboole_0)))),
% 38.76/38.95      inference('sup-', [status(thm)], ['42', '69'])).
% 38.76/38.95  thf('71', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         (((sk_A) = (k1_relat_1 @ sk_D))
% 38.76/38.95          | ((sk_B) = (k1_xboole_0))
% 38.76/38.95          | ~ (v1_xboole_0 @ X0))),
% 38.76/38.95      inference('sup-', [status(thm)], ['41', '70'])).
% 38.76/38.95  thf('72', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.76/38.95  thf('73', plain,
% 38.76/38.95      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 38.76/38.95      inference('split', [status(esa)], ['72'])).
% 38.76/38.95  thf('74', plain,
% 38.76/38.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('split', [status(esa)], ['72'])).
% 38.76/38.95  thf('75', plain,
% 38.76/38.95      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 38.76/38.95        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 38.76/38.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 38.76/38.95      inference('demod', [status(thm)], ['0', '5'])).
% 38.76/38.95  thf('76', plain,
% 38.76/38.95      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 38.76/38.95            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 38.76/38.95         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 38.76/38.95              sk_B)))
% 38.76/38.95         <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('sup-', [status(thm)], ['74', '75'])).
% 38.76/38.95  thf('77', plain,
% 38.76/38.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('split', [status(esa)], ['72'])).
% 38.76/38.95  thf('78', plain,
% 38.76/38.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.76/38.95  thf('79', plain,
% 38.76/38.95      (((m1_subset_1 @ sk_D @ 
% 38.76/38.95         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 38.76/38.95         <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('sup+', [status(thm)], ['77', '78'])).
% 38.76/38.95  thf(cc3_relset_1, axiom,
% 38.76/38.95    (![A:$i,B:$i]:
% 38.76/38.95     ( ( v1_xboole_0 @ A ) =>
% 38.76/38.95       ( ![C:$i]:
% 38.76/38.95         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 38.76/38.95           ( v1_xboole_0 @ C ) ) ) ))).
% 38.76/38.95  thf('80', plain,
% 38.76/38.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 38.76/38.95         (~ (v1_xboole_0 @ X16)
% 38.76/38.95          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X18)))
% 38.76/38.95          | (v1_xboole_0 @ X17))),
% 38.76/38.95      inference('cnf', [status(esa)], [cc3_relset_1])).
% 38.76/38.95  thf('81', plain,
% 38.76/38.95      ((((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 38.76/38.95         <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('sup-', [status(thm)], ['79', '80'])).
% 38.76/38.95  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 38.76/38.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 38.76/38.95  thf('83', plain, (((v1_xboole_0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('demod', [status(thm)], ['81', '82'])).
% 38.76/38.95  thf('84', plain,
% 38.76/38.95      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 38.76/38.95      inference('cnf', [status(esa)], [l13_xboole_0])).
% 38.76/38.95  thf('85', plain,
% 38.76/38.95      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('sup-', [status(thm)], ['83', '84'])).
% 38.76/38.95  thf('86', plain,
% 38.76/38.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('split', [status(esa)], ['72'])).
% 38.76/38.95  thf('87', plain, ((r1_tarski @ sk_C @ sk_A)),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.76/38.95  thf('88', plain,
% 38.76/38.95      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('sup+', [status(thm)], ['86', '87'])).
% 38.76/38.95  thf('89', plain,
% 38.76/38.95      (![X1 : $i, X3 : $i]:
% 38.76/38.95         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 38.76/38.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 38.76/38.95  thf('90', plain,
% 38.76/38.95      (((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C))))
% 38.76/38.95         <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('sup-', [status(thm)], ['88', '89'])).
% 38.76/38.95  thf('91', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 38.76/38.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 38.76/38.95  thf('92', plain,
% 38.76/38.95      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('demod', [status(thm)], ['90', '91'])).
% 38.76/38.95  thf('93', plain,
% 38.76/38.95      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('sup-', [status(thm)], ['83', '84'])).
% 38.76/38.95  thf('94', plain, ((v1_funct_1 @ sk_D)),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.76/38.95  thf('95', plain,
% 38.76/38.95      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('sup+', [status(thm)], ['93', '94'])).
% 38.76/38.95  thf('96', plain,
% 38.76/38.95      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 38.76/38.95      inference('cnf', [status(esa)], [t4_subset_1])).
% 38.76/38.95  thf('97', plain,
% 38.76/38.95      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 38.76/38.95         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 38.76/38.95          | ~ (v1_funct_1 @ X42)
% 38.76/38.95          | ((k2_partfun1 @ X43 @ X44 @ X42 @ X45) = (k7_relat_1 @ X42 @ X45)))),
% 38.76/38.95      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 38.76/38.95  thf('98', plain,
% 38.76/38.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.76/38.95         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 38.76/38.95            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 38.76/38.95          | ~ (v1_funct_1 @ k1_xboole_0))),
% 38.76/38.95      inference('sup-', [status(thm)], ['96', '97'])).
% 38.76/38.95  thf('99', plain,
% 38.76/38.95      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 38.76/38.95      inference('demod', [status(thm)], ['56', '59'])).
% 38.76/38.95  thf('100', plain,
% 38.76/38.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.76/38.95         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 38.76/38.95          | ~ (v1_funct_1 @ k1_xboole_0))),
% 38.76/38.95      inference('demod', [status(thm)], ['98', '99'])).
% 38.76/38.95  thf('101', plain,
% 38.76/38.95      ((![X0 : $i, X1 : $i, X2 : $i]:
% 38.76/38.95          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 38.76/38.95         <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('sup-', [status(thm)], ['95', '100'])).
% 38.76/38.95  thf('102', plain,
% 38.76/38.95      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('demod', [status(thm)], ['90', '91'])).
% 38.76/38.95  thf('103', plain,
% 38.76/38.95      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 38.76/38.95      inference('cnf', [status(esa)], [t4_subset_1])).
% 38.76/38.95  thf('104', plain,
% 38.76/38.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('split', [status(esa)], ['72'])).
% 38.76/38.95  thf('105', plain,
% 38.76/38.95      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('sup-', [status(thm)], ['83', '84'])).
% 38.76/38.95  thf('106', plain,
% 38.76/38.95      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('demod', [status(thm)], ['90', '91'])).
% 38.76/38.95  thf('107', plain,
% 38.76/38.95      ((![X0 : $i, X1 : $i, X2 : $i]:
% 38.76/38.95          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 38.76/38.95         <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('sup-', [status(thm)], ['95', '100'])).
% 38.76/38.95  thf('108', plain,
% 38.76/38.95      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 38.76/38.95      inference('demod', [status(thm)], ['90', '91'])).
% 38.76/38.95  thf('109', plain,
% 38.76/38.95      (![X0 : $i, X1 : $i]:
% 38.76/38.95         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 38.76/38.95      inference('demod', [status(thm)], ['51', '66'])).
% 38.76/38.95  thf('110', plain,
% 38.76/38.95      (![X32 : $i, X33 : $i, X34 : $i]:
% 38.76/38.95         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 38.76/38.95          | (v1_funct_2 @ X34 @ X32 @ X33)
% 38.76/38.95          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 38.76/38.95  thf('111', plain,
% 38.76/38.95      (![X0 : $i, X1 : $i]:
% 38.76/38.95         (((X1) != (k1_xboole_0))
% 38.76/38.95          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 38.76/38.95          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 38.76/38.95      inference('sup-', [status(thm)], ['109', '110'])).
% 38.76/38.95  thf('112', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 38.76/38.95          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 38.76/38.95      inference('simplify', [status(thm)], ['111'])).
% 38.76/38.95  thf('113', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 38.76/38.95      inference('simplify', [status(thm)], ['34'])).
% 38.76/38.95  thf('114', plain,
% 38.76/38.95      (![X0 : $i, X1 : $i]:
% 38.76/38.95         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 38.76/38.95      inference('sup-', [status(thm)], ['38', '39'])).
% 38.76/38.95  thf('115', plain,
% 38.76/38.95      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 38.76/38.95      inference('sup-', [status(thm)], ['113', '114'])).
% 38.76/38.95  thf('116', plain,
% 38.76/38.95      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 38.76/38.95      inference('demod', [status(thm)], ['112', '115'])).
% 38.76/38.95  thf('117', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 38.76/38.95      inference('demod', [status(thm)],
% 38.76/38.95                ['76', '85', '92', '101', '102', '103', '104', '105', '106', 
% 38.76/38.95                 '107', '108', '116'])).
% 38.76/38.95  thf('118', plain,
% 38.76/38.95      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 38.76/38.95      inference('split', [status(esa)], ['72'])).
% 38.76/38.95  thf('119', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 38.76/38.95      inference('sat_resolution*', [status(thm)], ['117', '118'])).
% 38.76/38.95  thf('120', plain, (((sk_B) != (k1_xboole_0))),
% 38.76/38.95      inference('simpl_trail', [status(thm)], ['73', '119'])).
% 38.76/38.95  thf('121', plain,
% 38.76/38.95      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ~ (v1_xboole_0 @ X0))),
% 38.76/38.95      inference('simplify_reflect-', [status(thm)], ['71', '120'])).
% 38.76/38.95  thf('122', plain,
% 38.76/38.95      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 38.76/38.95      inference('sup-', [status(thm)], ['31', '121'])).
% 38.76/38.95  thf('123', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 38.76/38.95      inference('simplify', [status(thm)], ['122'])).
% 38.76/38.95  thf('124', plain,
% 38.76/38.95      (![X11 : $i, X12 : $i]:
% 38.76/38.95         (~ (r1_tarski @ X11 @ (k1_relat_1 @ X12))
% 38.76/38.95          | ((k1_relat_1 @ (k7_relat_1 @ X12 @ X11)) = (X11))
% 38.76/38.95          | ~ (v1_relat_1 @ X12))),
% 38.76/38.95      inference('cnf', [status(esa)], [t91_relat_1])).
% 38.76/38.95  thf('125', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         (~ (r1_tarski @ X0 @ sk_A)
% 38.76/38.95          | ~ (v1_relat_1 @ sk_D)
% 38.76/38.95          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 38.76/38.95      inference('sup-', [status(thm)], ['123', '124'])).
% 38.76/38.95  thf('126', plain,
% 38.76/38.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.76/38.95  thf('127', plain,
% 38.76/38.95      (![X13 : $i, X14 : $i, X15 : $i]:
% 38.76/38.95         ((v1_relat_1 @ X13)
% 38.76/38.95          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 38.76/38.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 38.76/38.95  thf('128', plain, ((v1_relat_1 @ sk_D)),
% 38.76/38.95      inference('sup-', [status(thm)], ['126', '127'])).
% 38.76/38.95  thf('129', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         (~ (r1_tarski @ X0 @ sk_A)
% 38.76/38.95          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 38.76/38.95      inference('demod', [status(thm)], ['125', '128'])).
% 38.76/38.95  thf('130', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 38.76/38.95      inference('sup-', [status(thm)], ['16', '129'])).
% 38.76/38.95  thf('131', plain,
% 38.76/38.95      (![X9 : $i, X10 : $i]:
% 38.76/38.95         ((r1_tarski @ (k7_relat_1 @ X9 @ X10) @ X9) | ~ (v1_relat_1 @ X9))),
% 38.76/38.95      inference('cnf', [status(esa)], [t88_relat_1])).
% 38.76/38.95  thf('132', plain,
% 38.76/38.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.76/38.95  thf(t4_relset_1, axiom,
% 38.76/38.95    (![A:$i,B:$i,C:$i,D:$i]:
% 38.76/38.95     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 38.76/38.95       ( ( r1_tarski @ A @ D ) =>
% 38.76/38.95         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 38.76/38.95  thf('133', plain,
% 38.76/38.95      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 38.76/38.95         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 38.76/38.95          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 38.76/38.95          | ~ (r1_tarski @ X26 @ X29))),
% 38.76/38.95      inference('cnf', [status(esa)], [t4_relset_1])).
% 38.76/38.95  thf('134', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         (~ (r1_tarski @ X0 @ sk_D)
% 38.76/38.95          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 38.76/38.95      inference('sup-', [status(thm)], ['132', '133'])).
% 38.76/38.95  thf('135', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         (~ (v1_relat_1 @ sk_D)
% 38.76/38.95          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 38.76/38.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 38.76/38.95      inference('sup-', [status(thm)], ['131', '134'])).
% 38.76/38.95  thf('136', plain, ((v1_relat_1 @ sk_D)),
% 38.76/38.95      inference('sup-', [status(thm)], ['126', '127'])).
% 38.76/38.95  thf('137', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 38.76/38.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 38.76/38.95      inference('demod', [status(thm)], ['135', '136'])).
% 38.76/38.95  thf(t13_relset_1, axiom,
% 38.76/38.95    (![A:$i,B:$i,C:$i,D:$i]:
% 38.76/38.95     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 38.76/38.95       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 38.76/38.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 38.76/38.95  thf('138', plain,
% 38.76/38.95      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 38.76/38.95         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 38.76/38.95          | (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 38.76/38.95          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 38.76/38.95      inference('cnf', [status(esa)], [t13_relset_1])).
% 38.76/38.95  thf('139', plain,
% 38.76/38.95      (![X0 : $i, X1 : $i]:
% 38.76/38.95         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 38.76/38.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 38.76/38.95          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 38.76/38.95      inference('sup-', [status(thm)], ['137', '138'])).
% 38.76/38.95  thf('140', plain,
% 38.76/38.95      (![X0 : $i]:
% 38.76/38.95         (~ (r1_tarski @ sk_C @ X0)
% 38.76/38.95          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 38.76/38.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B))))),
% 38.76/38.95      inference('sup-', [status(thm)], ['130', '139'])).
% 38.76/38.95  thf('141', plain,
% 38.76/38.95      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 38.76/38.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 38.76/38.95      inference('sup-', [status(thm)], ['15', '140'])).
% 38.76/38.95  thf('142', plain,
% 38.76/38.95      (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 38.76/38.95      inference('demod', [status(thm)], ['13', '141'])).
% 38.76/38.95  thf('143', plain,
% 38.76/38.95      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 38.76/38.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 38.76/38.95      inference('sup-', [status(thm)], ['15', '140'])).
% 38.76/38.95  thf('144', plain,
% 38.76/38.95      (![X19 : $i, X20 : $i, X21 : $i]:
% 38.76/38.95         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 38.76/38.95          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 38.76/38.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 38.76/38.95  thf('145', plain,
% 38.76/38.95      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C))
% 38.76/38.95         = (k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)))),
% 38.76/38.95      inference('sup-', [status(thm)], ['143', '144'])).
% 38.76/38.95  thf('146', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 38.76/38.95      inference('sup-', [status(thm)], ['16', '129'])).
% 38.76/38.95  thf('147', plain,
% 38.76/38.95      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 38.76/38.95      inference('demod', [status(thm)], ['145', '146'])).
% 38.76/38.95  thf('148', plain,
% 38.76/38.95      (![X32 : $i, X33 : $i, X34 : $i]:
% 38.76/38.95         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 38.76/38.95          | (v1_funct_2 @ X34 @ X32 @ X33)
% 38.76/38.95          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 38.76/38.95  thf('149', plain,
% 38.76/38.95      ((((sk_C) != (sk_C))
% 38.76/38.95        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 38.76/38.95        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 38.76/38.95      inference('sup-', [status(thm)], ['147', '148'])).
% 38.76/38.95  thf('150', plain,
% 38.76/38.95      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 38.76/38.95        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C))),
% 38.76/38.95      inference('simplify', [status(thm)], ['149'])).
% 38.76/38.95  thf('151', plain,
% 38.76/38.95      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 38.76/38.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 38.76/38.95      inference('sup-', [status(thm)], ['15', '140'])).
% 38.76/38.95  thf('152', plain,
% 38.76/38.95      (![X35 : $i, X36 : $i, X37 : $i]:
% 38.76/38.95         (~ (zip_tseitin_0 @ X35 @ X36)
% 38.76/38.95          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 38.76/38.95          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 38.76/38.95  thf('153', plain,
% 38.76/38.95      (((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 38.76/38.95        | ~ (zip_tseitin_0 @ sk_B @ sk_C))),
% 38.76/38.95      inference('sup-', [status(thm)], ['151', '152'])).
% 38.76/38.95  thf('154', plain,
% 38.76/38.95      (![X30 : $i, X31 : $i]:
% 38.76/38.95         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 38.76/38.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 38.76/38.95  thf('155', plain,
% 38.76/38.95      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 38.76/38.95      inference('cnf', [status(esa)], [l13_xboole_0])).
% 38.76/38.95  thf('156', plain,
% 38.76/38.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.76/38.95         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X2) | ~ (v1_xboole_0 @ X1))),
% 38.76/38.95      inference('sup+', [status(thm)], ['154', '155'])).
% 38.76/38.95  thf('157', plain,
% 38.76/38.95      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 38.76/38.95      inference('split', [status(esa)], ['72'])).
% 38.76/38.95  thf('158', plain,
% 38.76/38.95      ((![X0 : $i, X1 : $i]:
% 38.76/38.95          (((X0) != (k1_xboole_0))
% 38.76/38.95           | ~ (v1_xboole_0 @ X0)
% 38.76/38.95           | (zip_tseitin_0 @ sk_B @ X1)))
% 38.76/38.95         <= (~ (((sk_B) = (k1_xboole_0))))),
% 38.76/38.95      inference('sup-', [status(thm)], ['156', '157'])).
% 38.76/38.95  thf('159', plain,
% 38.76/38.95      ((![X1 : $i]:
% 38.76/38.95          ((zip_tseitin_0 @ sk_B @ X1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 38.76/38.95         <= (~ (((sk_B) = (k1_xboole_0))))),
% 38.76/38.95      inference('simplify', [status(thm)], ['158'])).
% 38.76/38.95  thf('160', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 38.76/38.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 38.76/38.95  thf('161', plain,
% 38.76/38.95      ((![X1 : $i]: (zip_tseitin_0 @ sk_B @ X1))
% 38.76/38.95         <= (~ (((sk_B) = (k1_xboole_0))))),
% 38.76/38.95      inference('simplify_reflect+', [status(thm)], ['159', '160'])).
% 38.76/38.95  thf('162', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 38.76/38.95      inference('sat_resolution*', [status(thm)], ['117', '118'])).
% 38.76/38.95  thf('163', plain, (![X1 : $i]: (zip_tseitin_0 @ sk_B @ X1)),
% 38.76/38.95      inference('simpl_trail', [status(thm)], ['161', '162'])).
% 38.76/38.95  thf('164', plain,
% 38.76/38.95      ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)),
% 38.76/38.95      inference('demod', [status(thm)], ['153', '163'])).
% 38.76/38.95  thf('165', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 38.76/38.95      inference('demod', [status(thm)], ['150', '164'])).
% 38.76/38.95  thf('166', plain, ($false), inference('demod', [status(thm)], ['142', '165'])).
% 38.76/38.95  
% 38.76/38.95  % SZS output end Refutation
% 38.76/38.95  
% 38.76/38.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
