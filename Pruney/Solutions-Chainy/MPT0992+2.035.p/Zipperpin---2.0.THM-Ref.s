%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FdlAq5fsb7

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:39 EST 2020

% Result     : Theorem 41.25s
% Output     : Refutation 41.25s
% Verified   : 
% Statistics : Number of formulae       :  206 (1065 expanded)
%              Number of leaves         :   44 ( 324 expanded)
%              Depth                    :   21
%              Number of atoms          : 1588 (17552 expanded)
%              Number of equality atoms :  135 (1150 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X43 @ X44 @ X42 @ X45 ) ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ( ( k2_partfun1 @ X47 @ X48 @ X46 @ X49 )
        = ( k7_relat_1 @ X46 @ X49 ) ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
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

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('17',plain,(
    ! [X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ ( k1_relat_1 @ X21 ) )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('18',plain,
    ( ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('25',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ ( k1_relat_1 @ X21 ) )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('40',plain,
    ( ( ( k7_relat_1 @ sk_B @ k1_xboole_0 )
      = sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('42',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X2 @ X3 )
      | ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('47',plain,
    ( ( v1_relat_1 @ sk_B )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('49',plain,
    ( ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k7_relat_1 @ sk_B @ k1_xboole_0 )
      = sk_B ) ),
    inference(clc,[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['23','50'])).

thf('52',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('55',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('56',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('57',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('58',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('63',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('67',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('68',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('70',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
      | ( k1_xboole_0 = sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('75',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('77',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('79',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('80',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('81',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('82',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','68','75','76','77','78','79','80','81'])).

thf('83',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('87',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ( k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ X0 )
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','21'])).

thf('90',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ( k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ X0 )
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('92',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','21'])).

thf('93',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('94',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36
       != ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X35 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('102',plain,(
    ! [X34: $i] :
      ( zip_tseitin_0 @ X34 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('104',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['100','106'])).

thf('108',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['82','88','89','90','91','92','107'])).

thf('109',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('110',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['108','109'])).

thf('111',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['53','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['51','111'])).

thf('113',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('114',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('116',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['114','115'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('117',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('121',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('123',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('125',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v5_relat_1 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('126',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['124','125'])).

thf(fc22_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v5_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('127',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) @ X24 )
      | ~ ( v5_relat_1 @ X22 @ X24 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc22_relat_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['119','120'])).

thf('130',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['128','129'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('131',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X43 @ X44 @ X42 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('139',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['132','141'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('143',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X50 ) @ X51 )
      | ( v1_funct_2 @ X50 @ ( k1_relat_1 @ X50 ) @ X51 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('146',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('148',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['144','145','148'])).

thf('150',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['123','149'])).

thf('151',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','150'])).

thf('152',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','122'])).

thf('153',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['132','141'])).

thf('154',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X50 ) @ X51 )
      | ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ X51 ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('157',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('158',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['152','158'])).

thf('160',plain,(
    $false ),
    inference(demod,[status(thm)],['151','159'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FdlAq5fsb7
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:57:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 41.25/41.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 41.25/41.46  % Solved by: fo/fo7.sh
% 41.25/41.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 41.25/41.46  % done 19934 iterations in 40.999s
% 41.25/41.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 41.25/41.46  % SZS output start Refutation
% 41.25/41.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 41.25/41.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 41.25/41.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 41.25/41.46  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 41.25/41.46  thf(sk_B_type, type, sk_B: $i).
% 41.25/41.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 41.25/41.46  thf(sk_A_type, type, sk_A: $i).
% 41.25/41.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 41.25/41.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 41.25/41.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 41.25/41.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 41.25/41.46  thf(sk_C_type, type, sk_C: $i).
% 41.25/41.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 41.25/41.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 41.25/41.46  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 41.25/41.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 41.25/41.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 41.25/41.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 41.25/41.46  thf(sk_D_type, type, sk_D: $i).
% 41.25/41.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 41.25/41.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 41.25/41.46  thf(t38_funct_2, conjecture,
% 41.25/41.46    (![A:$i,B:$i,C:$i,D:$i]:
% 41.25/41.46     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 41.25/41.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 41.25/41.46       ( ( r1_tarski @ C @ A ) =>
% 41.25/41.46         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 41.25/41.46           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 41.25/41.46             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 41.25/41.46             ( m1_subset_1 @
% 41.25/41.46               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 41.25/41.46               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 41.25/41.46  thf(zf_stmt_0, negated_conjecture,
% 41.25/41.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 41.25/41.46        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 41.25/41.46            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 41.25/41.46          ( ( r1_tarski @ C @ A ) =>
% 41.25/41.46            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 41.25/41.46              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 41.25/41.46                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 41.25/41.46                ( m1_subset_1 @
% 41.25/41.46                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 41.25/41.46                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 41.25/41.46    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 41.25/41.46  thf('0', plain,
% 41.25/41.46      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 41.25/41.46        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 41.25/41.46             sk_B)
% 41.25/41.46        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 41.25/41.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf('1', plain,
% 41.25/41.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf(dt_k2_partfun1, axiom,
% 41.25/41.46    (![A:$i,B:$i,C:$i,D:$i]:
% 41.25/41.46     ( ( ( v1_funct_1 @ C ) & 
% 41.25/41.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 41.25/41.46       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 41.25/41.46         ( m1_subset_1 @
% 41.25/41.46           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 41.25/41.46           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 41.25/41.46  thf('2', plain,
% 41.25/41.46      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 41.25/41.46         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 41.25/41.46          | ~ (v1_funct_1 @ X42)
% 41.25/41.46          | (v1_funct_1 @ (k2_partfun1 @ X43 @ X44 @ X42 @ X45)))),
% 41.25/41.46      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 41.25/41.46  thf('3', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 41.25/41.46          | ~ (v1_funct_1 @ sk_D))),
% 41.25/41.46      inference('sup-', [status(thm)], ['1', '2'])).
% 41.25/41.46  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf('5', plain,
% 41.25/41.46      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 41.25/41.46      inference('demod', [status(thm)], ['3', '4'])).
% 41.25/41.46  thf('6', plain,
% 41.25/41.46      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 41.25/41.46        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 41.25/41.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 41.25/41.46      inference('demod', [status(thm)], ['0', '5'])).
% 41.25/41.46  thf('7', plain,
% 41.25/41.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf(redefinition_k2_partfun1, axiom,
% 41.25/41.46    (![A:$i,B:$i,C:$i,D:$i]:
% 41.25/41.46     ( ( ( v1_funct_1 @ C ) & 
% 41.25/41.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 41.25/41.46       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 41.25/41.46  thf('8', plain,
% 41.25/41.46      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 41.25/41.46         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 41.25/41.46          | ~ (v1_funct_1 @ X46)
% 41.25/41.46          | ((k2_partfun1 @ X47 @ X48 @ X46 @ X49) = (k7_relat_1 @ X46 @ X49)))),
% 41.25/41.46      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 41.25/41.46  thf('9', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 41.25/41.46          | ~ (v1_funct_1 @ sk_D))),
% 41.25/41.46      inference('sup-', [status(thm)], ['7', '8'])).
% 41.25/41.46  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf('11', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 41.25/41.46      inference('demod', [status(thm)], ['9', '10'])).
% 41.25/41.46  thf('12', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 41.25/41.46      inference('demod', [status(thm)], ['9', '10'])).
% 41.25/41.46  thf('13', plain,
% 41.25/41.46      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 41.25/41.46        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 41.25/41.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 41.25/41.46      inference('demod', [status(thm)], ['6', '11', '12'])).
% 41.25/41.46  thf('14', plain, ((r1_tarski @ sk_C @ sk_A)),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf(d1_funct_2, axiom,
% 41.25/41.46    (![A:$i,B:$i,C:$i]:
% 41.25/41.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 41.25/41.46       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 41.25/41.46           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 41.25/41.46             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 41.25/41.46         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 41.25/41.46           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 41.25/41.46             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 41.25/41.46  thf(zf_stmt_1, axiom,
% 41.25/41.46    (![B:$i,A:$i]:
% 41.25/41.46     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 41.25/41.46       ( zip_tseitin_0 @ B @ A ) ))).
% 41.25/41.46  thf('15', plain,
% 41.25/41.46      (![X34 : $i, X35 : $i]:
% 41.25/41.46         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 41.25/41.46  thf(t60_relat_1, axiom,
% 41.25/41.46    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 41.25/41.46     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 41.25/41.46  thf('16', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 41.25/41.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 41.25/41.46  thf(t98_relat_1, axiom,
% 41.25/41.46    (![A:$i]:
% 41.25/41.46     ( ( v1_relat_1 @ A ) =>
% 41.25/41.46       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 41.25/41.46  thf('17', plain,
% 41.25/41.46      (![X21 : $i]:
% 41.25/41.46         (((k7_relat_1 @ X21 @ (k1_relat_1 @ X21)) = (X21))
% 41.25/41.46          | ~ (v1_relat_1 @ X21))),
% 41.25/41.46      inference('cnf', [status(esa)], [t98_relat_1])).
% 41.25/41.46  thf('18', plain,
% 41.25/41.46      ((((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 41.25/41.46        | ~ (v1_relat_1 @ k1_xboole_0))),
% 41.25/41.46      inference('sup+', [status(thm)], ['16', '17'])).
% 41.25/41.46  thf(t4_subset_1, axiom,
% 41.25/41.46    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 41.25/41.46  thf('19', plain,
% 41.25/41.46      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 41.25/41.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 41.25/41.46  thf(cc1_relset_1, axiom,
% 41.25/41.46    (![A:$i,B:$i,C:$i]:
% 41.25/41.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 41.25/41.46       ( v1_relat_1 @ C ) ))).
% 41.25/41.46  thf('20', plain,
% 41.25/41.46      (![X25 : $i, X26 : $i, X27 : $i]:
% 41.25/41.46         ((v1_relat_1 @ X25)
% 41.25/41.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 41.25/41.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 41.25/41.46  thf('21', plain, ((v1_relat_1 @ k1_xboole_0)),
% 41.25/41.46      inference('sup-', [status(thm)], ['19', '20'])).
% 41.25/41.46  thf('22', plain,
% 41.25/41.46      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 41.25/41.46      inference('demod', [status(thm)], ['18', '21'])).
% 41.25/41.46  thf('23', plain,
% 41.25/41.46      (![X0 : $i, X1 : $i]:
% 41.25/41.46         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 41.25/41.46          | (zip_tseitin_0 @ X0 @ X1))),
% 41.25/41.46      inference('sup+', [status(thm)], ['15', '22'])).
% 41.25/41.46  thf('24', plain,
% 41.25/41.46      (![X34 : $i, X35 : $i]:
% 41.25/41.46         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 41.25/41.46  thf('25', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 41.25/41.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 41.25/41.46  thf('26', plain,
% 41.25/41.46      (![X0 : $i, X1 : $i]:
% 41.25/41.46         (((k1_relat_1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X1))),
% 41.25/41.46      inference('sup+', [status(thm)], ['24', '25'])).
% 41.25/41.46  thf('27', plain,
% 41.25/41.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 41.25/41.46  thf(zf_stmt_3, axiom,
% 41.25/41.46    (![C:$i,B:$i,A:$i]:
% 41.25/41.46     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 41.25/41.46       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 41.25/41.46  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 41.25/41.46  thf(zf_stmt_5, axiom,
% 41.25/41.46    (![A:$i,B:$i,C:$i]:
% 41.25/41.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 41.25/41.46       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 41.25/41.46         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 41.25/41.46           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 41.25/41.46             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 41.25/41.46  thf('28', plain,
% 41.25/41.46      (![X39 : $i, X40 : $i, X41 : $i]:
% 41.25/41.46         (~ (zip_tseitin_0 @ X39 @ X40)
% 41.25/41.46          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 41.25/41.46          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 41.25/41.46  thf('29', plain,
% 41.25/41.46      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 41.25/41.46      inference('sup-', [status(thm)], ['27', '28'])).
% 41.25/41.46  thf('30', plain,
% 41.25/41.46      ((((k1_relat_1 @ sk_B) = (k1_xboole_0))
% 41.25/41.46        | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 41.25/41.46      inference('sup-', [status(thm)], ['26', '29'])).
% 41.25/41.46  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf('32', plain,
% 41.25/41.46      (![X36 : $i, X37 : $i, X38 : $i]:
% 41.25/41.46         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 41.25/41.46          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 41.25/41.46          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 41.25/41.46  thf('33', plain,
% 41.25/41.46      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 41.25/41.46        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 41.25/41.46      inference('sup-', [status(thm)], ['31', '32'])).
% 41.25/41.46  thf('34', plain,
% 41.25/41.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf(redefinition_k1_relset_1, axiom,
% 41.25/41.46    (![A:$i,B:$i,C:$i]:
% 41.25/41.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 41.25/41.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 41.25/41.46  thf('35', plain,
% 41.25/41.46      (![X31 : $i, X32 : $i, X33 : $i]:
% 41.25/41.46         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 41.25/41.46          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 41.25/41.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 41.25/41.46  thf('36', plain,
% 41.25/41.46      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 41.25/41.46      inference('sup-', [status(thm)], ['34', '35'])).
% 41.25/41.46  thf('37', plain,
% 41.25/41.46      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 41.25/41.46      inference('demod', [status(thm)], ['33', '36'])).
% 41.25/41.46  thf('38', plain,
% 41.25/41.46      ((((k1_relat_1 @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 41.25/41.46      inference('sup-', [status(thm)], ['30', '37'])).
% 41.25/41.46  thf('39', plain,
% 41.25/41.46      (![X21 : $i]:
% 41.25/41.46         (((k7_relat_1 @ X21 @ (k1_relat_1 @ X21)) = (X21))
% 41.25/41.46          | ~ (v1_relat_1 @ X21))),
% 41.25/41.46      inference('cnf', [status(esa)], [t98_relat_1])).
% 41.25/41.46  thf('40', plain,
% 41.25/41.46      ((((k7_relat_1 @ sk_B @ k1_xboole_0) = (sk_B))
% 41.25/41.46        | ((sk_A) = (k1_relat_1 @ sk_D))
% 41.25/41.46        | ~ (v1_relat_1 @ sk_B))),
% 41.25/41.46      inference('sup+', [status(thm)], ['38', '39'])).
% 41.25/41.46  thf('41', plain,
% 41.25/41.46      (![X34 : $i, X35 : $i]:
% 41.25/41.46         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 41.25/41.46  thf('42', plain,
% 41.25/41.46      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 41.25/41.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 41.25/41.46  thf('43', plain,
% 41.25/41.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.25/41.46         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (zip_tseitin_0 @ X0 @ X2))),
% 41.25/41.46      inference('sup+', [status(thm)], ['41', '42'])).
% 41.25/41.46  thf('44', plain,
% 41.25/41.46      (![X25 : $i, X26 : $i, X27 : $i]:
% 41.25/41.46         ((v1_relat_1 @ X25)
% 41.25/41.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 41.25/41.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 41.25/41.46  thf('45', plain,
% 41.25/41.46      (![X2 : $i, X3 : $i]: ((zip_tseitin_0 @ X2 @ X3) | (v1_relat_1 @ X2))),
% 41.25/41.46      inference('sup-', [status(thm)], ['43', '44'])).
% 41.25/41.46  thf('46', plain,
% 41.25/41.46      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 41.25/41.46      inference('sup-', [status(thm)], ['27', '28'])).
% 41.25/41.46  thf('47', plain,
% 41.25/41.46      (((v1_relat_1 @ sk_B) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 41.25/41.46      inference('sup-', [status(thm)], ['45', '46'])).
% 41.25/41.46  thf('48', plain,
% 41.25/41.46      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 41.25/41.46      inference('demod', [status(thm)], ['33', '36'])).
% 41.25/41.46  thf('49', plain, (((v1_relat_1 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 41.25/41.46      inference('sup-', [status(thm)], ['47', '48'])).
% 41.25/41.46  thf('50', plain,
% 41.25/41.46      ((((sk_A) = (k1_relat_1 @ sk_D))
% 41.25/41.46        | ((k7_relat_1 @ sk_B @ k1_xboole_0) = (sk_B)))),
% 41.25/41.46      inference('clc', [status(thm)], ['40', '49'])).
% 41.25/41.46  thf('51', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         (((k1_xboole_0) = (sk_B))
% 41.25/41.46          | (zip_tseitin_0 @ sk_B @ X0)
% 41.25/41.46          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 41.25/41.46      inference('sup+', [status(thm)], ['23', '50'])).
% 41.25/41.46  thf('52', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf('53', plain,
% 41.25/41.46      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 41.25/41.46      inference('split', [status(esa)], ['52'])).
% 41.25/41.46  thf('54', plain,
% 41.25/41.46      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('split', [status(esa)], ['52'])).
% 41.25/41.46  thf('55', plain,
% 41.25/41.46      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 41.25/41.46        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 41.25/41.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 41.25/41.46      inference('demod', [status(thm)], ['0', '5'])).
% 41.25/41.46  thf('56', plain,
% 41.25/41.46      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 41.25/41.46            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 41.25/41.46         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 41.25/41.46              sk_B)))
% 41.25/41.46         <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('sup-', [status(thm)], ['54', '55'])).
% 41.25/41.46  thf(t113_zfmisc_1, axiom,
% 41.25/41.46    (![A:$i,B:$i]:
% 41.25/41.46     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 41.25/41.46       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 41.25/41.46  thf('57', plain,
% 41.25/41.46      (![X5 : $i, X6 : $i]:
% 41.25/41.46         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 41.25/41.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 41.25/41.46  thf('58', plain,
% 41.25/41.46      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 41.25/41.46      inference('simplify', [status(thm)], ['57'])).
% 41.25/41.46  thf('59', plain,
% 41.25/41.46      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('split', [status(esa)], ['52'])).
% 41.25/41.46  thf('60', plain,
% 41.25/41.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf('61', plain,
% 41.25/41.46      (((m1_subset_1 @ sk_D @ 
% 41.25/41.46         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 41.25/41.46         <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('sup+', [status(thm)], ['59', '60'])).
% 41.25/41.46  thf('62', plain,
% 41.25/41.46      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 41.25/41.46         <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('sup+', [status(thm)], ['58', '61'])).
% 41.25/41.46  thf(t3_subset, axiom,
% 41.25/41.46    (![A:$i,B:$i]:
% 41.25/41.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 41.25/41.46  thf('63', plain,
% 41.25/41.46      (![X8 : $i, X9 : $i]:
% 41.25/41.46         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 41.25/41.46      inference('cnf', [status(esa)], [t3_subset])).
% 41.25/41.46  thf('64', plain,
% 41.25/41.46      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('sup-', [status(thm)], ['62', '63'])).
% 41.25/41.46  thf(d10_xboole_0, axiom,
% 41.25/41.46    (![A:$i,B:$i]:
% 41.25/41.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 41.25/41.46  thf('65', plain,
% 41.25/41.46      (![X0 : $i, X2 : $i]:
% 41.25/41.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 41.25/41.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 41.25/41.46  thf('66', plain,
% 41.25/41.46      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 41.25/41.46         <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('sup-', [status(thm)], ['64', '65'])).
% 41.25/41.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 41.25/41.46  thf('67', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 41.25/41.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 41.25/41.46  thf('68', plain,
% 41.25/41.46      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('demod', [status(thm)], ['66', '67'])).
% 41.25/41.46  thf('69', plain,
% 41.25/41.46      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('split', [status(esa)], ['52'])).
% 41.25/41.46  thf('70', plain, ((r1_tarski @ sk_C @ sk_A)),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf('71', plain,
% 41.25/41.46      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('sup+', [status(thm)], ['69', '70'])).
% 41.25/41.46  thf('72', plain,
% 41.25/41.46      (![X0 : $i, X2 : $i]:
% 41.25/41.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 41.25/41.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 41.25/41.46  thf('73', plain,
% 41.25/41.46      (((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C))))
% 41.25/41.46         <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('sup-', [status(thm)], ['71', '72'])).
% 41.25/41.46  thf('74', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 41.25/41.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 41.25/41.46  thf('75', plain,
% 41.25/41.46      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('demod', [status(thm)], ['73', '74'])).
% 41.25/41.46  thf('76', plain,
% 41.25/41.46      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('demod', [status(thm)], ['73', '74'])).
% 41.25/41.46  thf('77', plain,
% 41.25/41.46      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 41.25/41.46      inference('simplify', [status(thm)], ['57'])).
% 41.25/41.46  thf('78', plain,
% 41.25/41.46      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('split', [status(esa)], ['52'])).
% 41.25/41.46  thf('79', plain,
% 41.25/41.46      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('demod', [status(thm)], ['66', '67'])).
% 41.25/41.46  thf('80', plain,
% 41.25/41.46      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('demod', [status(thm)], ['73', '74'])).
% 41.25/41.46  thf('81', plain,
% 41.25/41.46      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('demod', [status(thm)], ['73', '74'])).
% 41.25/41.46  thf('82', plain,
% 41.25/41.46      (((~ (m1_subset_1 @ 
% 41.25/41.46            (k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0) @ 
% 41.25/41.46            (k1_zfmisc_1 @ k1_xboole_0))
% 41.25/41.46         | ~ (v1_funct_2 @ 
% 41.25/41.46              (k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0) @ 
% 41.25/41.46              k1_xboole_0 @ sk_B)))
% 41.25/41.46         <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('demod', [status(thm)],
% 41.25/41.46                ['56', '68', '75', '76', '77', '78', '79', '80', '81'])).
% 41.25/41.46  thf('83', plain,
% 41.25/41.46      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('split', [status(esa)], ['52'])).
% 41.25/41.46  thf('84', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 41.25/41.46      inference('demod', [status(thm)], ['9', '10'])).
% 41.25/41.46  thf('85', plain,
% 41.25/41.46      ((![X0 : $i]:
% 41.25/41.46          ((k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ X0)
% 41.25/41.46            = (k7_relat_1 @ sk_D @ X0)))
% 41.25/41.46         <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('sup+', [status(thm)], ['83', '84'])).
% 41.25/41.46  thf('86', plain,
% 41.25/41.46      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('demod', [status(thm)], ['66', '67'])).
% 41.25/41.46  thf('87', plain,
% 41.25/41.46      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('demod', [status(thm)], ['66', '67'])).
% 41.25/41.46  thf('88', plain,
% 41.25/41.46      ((![X0 : $i]:
% 41.25/41.46          ((k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ X0)
% 41.25/41.46            = (k7_relat_1 @ k1_xboole_0 @ X0)))
% 41.25/41.46         <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('demod', [status(thm)], ['85', '86', '87'])).
% 41.25/41.46  thf('89', plain,
% 41.25/41.46      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 41.25/41.46      inference('demod', [status(thm)], ['18', '21'])).
% 41.25/41.46  thf('90', plain,
% 41.25/41.46      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 41.25/41.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 41.25/41.46  thf('91', plain,
% 41.25/41.46      ((![X0 : $i]:
% 41.25/41.46          ((k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ X0)
% 41.25/41.46            = (k7_relat_1 @ k1_xboole_0 @ X0)))
% 41.25/41.46         <= ((((sk_A) = (k1_xboole_0))))),
% 41.25/41.46      inference('demod', [status(thm)], ['85', '86', '87'])).
% 41.25/41.46  thf('92', plain,
% 41.25/41.46      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 41.25/41.46      inference('demod', [status(thm)], ['18', '21'])).
% 41.25/41.46  thf('93', plain,
% 41.25/41.46      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 41.25/41.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 41.25/41.46  thf('94', plain,
% 41.25/41.46      (![X31 : $i, X32 : $i, X33 : $i]:
% 41.25/41.46         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 41.25/41.46          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 41.25/41.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 41.25/41.46  thf('95', plain,
% 41.25/41.46      (![X0 : $i, X1 : $i]:
% 41.25/41.46         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 41.25/41.46      inference('sup-', [status(thm)], ['93', '94'])).
% 41.25/41.46  thf('96', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 41.25/41.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 41.25/41.46  thf('97', plain,
% 41.25/41.46      (![X0 : $i, X1 : $i]:
% 41.25/41.46         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 41.25/41.46      inference('demod', [status(thm)], ['95', '96'])).
% 41.25/41.46  thf('98', plain,
% 41.25/41.46      (![X36 : $i, X37 : $i, X38 : $i]:
% 41.25/41.46         (((X36) != (k1_relset_1 @ X36 @ X37 @ X38))
% 41.25/41.46          | (v1_funct_2 @ X38 @ X36 @ X37)
% 41.25/41.46          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 41.25/41.46  thf('99', plain,
% 41.25/41.46      (![X0 : $i, X1 : $i]:
% 41.25/41.46         (((X1) != (k1_xboole_0))
% 41.25/41.46          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 41.25/41.46          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 41.25/41.46      inference('sup-', [status(thm)], ['97', '98'])).
% 41.25/41.46  thf('100', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 41.25/41.46          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 41.25/41.46      inference('simplify', [status(thm)], ['99'])).
% 41.25/41.46  thf('101', plain,
% 41.25/41.46      (![X34 : $i, X35 : $i]:
% 41.25/41.46         ((zip_tseitin_0 @ X34 @ X35) | ((X35) != (k1_xboole_0)))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 41.25/41.46  thf('102', plain, (![X34 : $i]: (zip_tseitin_0 @ X34 @ k1_xboole_0)),
% 41.25/41.46      inference('simplify', [status(thm)], ['101'])).
% 41.25/41.46  thf('103', plain,
% 41.25/41.46      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 41.25/41.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 41.25/41.46  thf('104', plain,
% 41.25/41.46      (![X39 : $i, X40 : $i, X41 : $i]:
% 41.25/41.46         (~ (zip_tseitin_0 @ X39 @ X40)
% 41.25/41.46          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 41.25/41.46          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 41.25/41.46  thf('105', plain,
% 41.25/41.46      (![X0 : $i, X1 : $i]:
% 41.25/41.46         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 41.25/41.46      inference('sup-', [status(thm)], ['103', '104'])).
% 41.25/41.46  thf('106', plain,
% 41.25/41.46      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 41.25/41.46      inference('sup-', [status(thm)], ['102', '105'])).
% 41.25/41.46  thf('107', plain,
% 41.25/41.46      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 41.25/41.46      inference('demod', [status(thm)], ['100', '106'])).
% 41.25/41.46  thf('108', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 41.25/41.46      inference('demod', [status(thm)],
% 41.25/41.46                ['82', '88', '89', '90', '91', '92', '107'])).
% 41.25/41.46  thf('109', plain,
% 41.25/41.46      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 41.25/41.46      inference('split', [status(esa)], ['52'])).
% 41.25/41.46  thf('110', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 41.25/41.46      inference('sat_resolution*', [status(thm)], ['108', '109'])).
% 41.25/41.46  thf('111', plain, (((sk_B) != (k1_xboole_0))),
% 41.25/41.46      inference('simpl_trail', [status(thm)], ['53', '110'])).
% 41.25/41.46  thf('112', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         ((zip_tseitin_0 @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 41.25/41.46      inference('simplify_reflect-', [status(thm)], ['51', '111'])).
% 41.25/41.46  thf('113', plain,
% 41.25/41.46      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 41.25/41.46      inference('sup-', [status(thm)], ['27', '28'])).
% 41.25/41.46  thf('114', plain,
% 41.25/41.46      ((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 41.25/41.46      inference('sup-', [status(thm)], ['112', '113'])).
% 41.25/41.46  thf('115', plain,
% 41.25/41.46      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 41.25/41.46      inference('demod', [status(thm)], ['33', '36'])).
% 41.25/41.46  thf('116', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 41.25/41.46      inference('clc', [status(thm)], ['114', '115'])).
% 41.25/41.46  thf(t91_relat_1, axiom,
% 41.25/41.46    (![A:$i,B:$i]:
% 41.25/41.46     ( ( v1_relat_1 @ B ) =>
% 41.25/41.46       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 41.25/41.46         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 41.25/41.46  thf('117', plain,
% 41.25/41.46      (![X19 : $i, X20 : $i]:
% 41.25/41.46         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 41.25/41.46          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 41.25/41.46          | ~ (v1_relat_1 @ X20))),
% 41.25/41.46      inference('cnf', [status(esa)], [t91_relat_1])).
% 41.25/41.46  thf('118', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         (~ (r1_tarski @ X0 @ sk_A)
% 41.25/41.46          | ~ (v1_relat_1 @ sk_D)
% 41.25/41.46          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 41.25/41.46      inference('sup-', [status(thm)], ['116', '117'])).
% 41.25/41.46  thf('119', plain,
% 41.25/41.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf('120', plain,
% 41.25/41.46      (![X25 : $i, X26 : $i, X27 : $i]:
% 41.25/41.46         ((v1_relat_1 @ X25)
% 41.25/41.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 41.25/41.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 41.25/41.46  thf('121', plain, ((v1_relat_1 @ sk_D)),
% 41.25/41.46      inference('sup-', [status(thm)], ['119', '120'])).
% 41.25/41.46  thf('122', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         (~ (r1_tarski @ X0 @ sk_A)
% 41.25/41.46          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 41.25/41.46      inference('demod', [status(thm)], ['118', '121'])).
% 41.25/41.46  thf('123', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 41.25/41.46      inference('sup-', [status(thm)], ['14', '122'])).
% 41.25/41.46  thf('124', plain,
% 41.25/41.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf(cc2_relset_1, axiom,
% 41.25/41.46    (![A:$i,B:$i,C:$i]:
% 41.25/41.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 41.25/41.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 41.25/41.46  thf('125', plain,
% 41.25/41.46      (![X28 : $i, X29 : $i, X30 : $i]:
% 41.25/41.46         ((v5_relat_1 @ X28 @ X30)
% 41.25/41.46          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 41.25/41.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 41.25/41.46  thf('126', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 41.25/41.46      inference('sup-', [status(thm)], ['124', '125'])).
% 41.25/41.46  thf(fc22_relat_1, axiom,
% 41.25/41.46    (![A:$i,B:$i,C:$i]:
% 41.25/41.46     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ B ) ) =>
% 41.25/41.46       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 41.25/41.46         ( v5_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 41.25/41.46  thf('127', plain,
% 41.25/41.46      (![X22 : $i, X23 : $i, X24 : $i]:
% 41.25/41.46         ((v5_relat_1 @ (k7_relat_1 @ X22 @ X23) @ X24)
% 41.25/41.46          | ~ (v5_relat_1 @ X22 @ X24)
% 41.25/41.46          | ~ (v1_relat_1 @ X22))),
% 41.25/41.46      inference('cnf', [status(esa)], [fc22_relat_1])).
% 41.25/41.46  thf('128', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         (~ (v1_relat_1 @ sk_D)
% 41.25/41.46          | (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B))),
% 41.25/41.46      inference('sup-', [status(thm)], ['126', '127'])).
% 41.25/41.46  thf('129', plain, ((v1_relat_1 @ sk_D)),
% 41.25/41.46      inference('sup-', [status(thm)], ['119', '120'])).
% 41.25/41.46  thf('130', plain,
% 41.25/41.46      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 41.25/41.46      inference('demod', [status(thm)], ['128', '129'])).
% 41.25/41.46  thf(d19_relat_1, axiom,
% 41.25/41.46    (![A:$i,B:$i]:
% 41.25/41.46     ( ( v1_relat_1 @ B ) =>
% 41.25/41.46       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 41.25/41.46  thf('131', plain,
% 41.25/41.46      (![X14 : $i, X15 : $i]:
% 41.25/41.46         (~ (v5_relat_1 @ X14 @ X15)
% 41.25/41.46          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 41.25/41.46          | ~ (v1_relat_1 @ X14))),
% 41.25/41.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 41.25/41.46  thf('132', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 41.25/41.46          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 41.25/41.46      inference('sup-', [status(thm)], ['130', '131'])).
% 41.25/41.46  thf('133', plain,
% 41.25/41.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf('134', plain,
% 41.25/41.46      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 41.25/41.46         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 41.25/41.46          | ~ (v1_funct_1 @ X42)
% 41.25/41.46          | (m1_subset_1 @ (k2_partfun1 @ X43 @ X44 @ X42 @ X45) @ 
% 41.25/41.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 41.25/41.46      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 41.25/41.46  thf('135', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 41.25/41.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 41.25/41.46          | ~ (v1_funct_1 @ sk_D))),
% 41.25/41.46      inference('sup-', [status(thm)], ['133', '134'])).
% 41.25/41.46  thf('136', plain, ((v1_funct_1 @ sk_D)),
% 41.25/41.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.25/41.46  thf('137', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 41.25/41.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 41.25/41.46      inference('demod', [status(thm)], ['135', '136'])).
% 41.25/41.46  thf('138', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 41.25/41.46      inference('demod', [status(thm)], ['9', '10'])).
% 41.25/41.46  thf('139', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 41.25/41.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 41.25/41.46      inference('demod', [status(thm)], ['137', '138'])).
% 41.25/41.46  thf('140', plain,
% 41.25/41.46      (![X25 : $i, X26 : $i, X27 : $i]:
% 41.25/41.46         ((v1_relat_1 @ X25)
% 41.25/41.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 41.25/41.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 41.25/41.46  thf('141', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 41.25/41.46      inference('sup-', [status(thm)], ['139', '140'])).
% 41.25/41.46  thf('142', plain,
% 41.25/41.46      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 41.25/41.46      inference('demod', [status(thm)], ['132', '141'])).
% 41.25/41.46  thf(t4_funct_2, axiom,
% 41.25/41.46    (![A:$i,B:$i]:
% 41.25/41.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 41.25/41.46       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 41.25/41.46         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 41.25/41.46           ( m1_subset_1 @
% 41.25/41.46             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 41.25/41.46  thf('143', plain,
% 41.25/41.46      (![X50 : $i, X51 : $i]:
% 41.25/41.46         (~ (r1_tarski @ (k2_relat_1 @ X50) @ X51)
% 41.25/41.46          | (v1_funct_2 @ X50 @ (k1_relat_1 @ X50) @ X51)
% 41.25/41.46          | ~ (v1_funct_1 @ X50)
% 41.25/41.46          | ~ (v1_relat_1 @ X50))),
% 41.25/41.46      inference('cnf', [status(esa)], [t4_funct_2])).
% 41.25/41.46  thf('144', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 41.25/41.46          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 41.25/41.46          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 41.25/41.46             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 41.25/41.46      inference('sup-', [status(thm)], ['142', '143'])).
% 41.25/41.46  thf('145', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 41.25/41.46      inference('sup-', [status(thm)], ['139', '140'])).
% 41.25/41.46  thf('146', plain,
% 41.25/41.46      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 41.25/41.46      inference('demod', [status(thm)], ['3', '4'])).
% 41.25/41.46  thf('147', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 41.25/41.46      inference('demod', [status(thm)], ['9', '10'])).
% 41.25/41.46  thf('148', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 41.25/41.46      inference('demod', [status(thm)], ['146', '147'])).
% 41.25/41.46  thf('149', plain,
% 41.25/41.46      (![X0 : $i]:
% 41.25/41.46         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 41.25/41.46          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 41.25/41.46      inference('demod', [status(thm)], ['144', '145', '148'])).
% 41.25/41.46  thf('150', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 41.25/41.46      inference('sup+', [status(thm)], ['123', '149'])).
% 41.25/41.46  thf('151', plain,
% 41.25/41.46      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 41.25/41.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 41.25/41.46      inference('demod', [status(thm)], ['13', '150'])).
% 41.25/41.46  thf('152', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 41.25/41.47      inference('sup-', [status(thm)], ['14', '122'])).
% 41.25/41.47  thf('153', plain,
% 41.25/41.47      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 41.25/41.47      inference('demod', [status(thm)], ['132', '141'])).
% 41.25/41.47  thf('154', plain,
% 41.25/41.47      (![X50 : $i, X51 : $i]:
% 41.25/41.47         (~ (r1_tarski @ (k2_relat_1 @ X50) @ X51)
% 41.25/41.47          | (m1_subset_1 @ X50 @ 
% 41.25/41.47             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ X51)))
% 41.25/41.47          | ~ (v1_funct_1 @ X50)
% 41.25/41.47          | ~ (v1_relat_1 @ X50))),
% 41.25/41.47      inference('cnf', [status(esa)], [t4_funct_2])).
% 41.25/41.47  thf('155', plain,
% 41.25/41.47      (![X0 : $i]:
% 41.25/41.47         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 41.25/41.47          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 41.25/41.47          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 41.25/41.47             (k1_zfmisc_1 @ 
% 41.25/41.47              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 41.25/41.47      inference('sup-', [status(thm)], ['153', '154'])).
% 41.25/41.47  thf('156', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 41.25/41.47      inference('sup-', [status(thm)], ['139', '140'])).
% 41.25/41.47  thf('157', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 41.25/41.47      inference('demod', [status(thm)], ['146', '147'])).
% 41.25/41.47  thf('158', plain,
% 41.25/41.47      (![X0 : $i]:
% 41.25/41.47         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 41.25/41.47          (k1_zfmisc_1 @ 
% 41.25/41.47           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 41.25/41.47      inference('demod', [status(thm)], ['155', '156', '157'])).
% 41.25/41.47  thf('159', plain,
% 41.25/41.47      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 41.25/41.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 41.25/41.47      inference('sup+', [status(thm)], ['152', '158'])).
% 41.25/41.47  thf('160', plain, ($false), inference('demod', [status(thm)], ['151', '159'])).
% 41.25/41.47  
% 41.25/41.47  % SZS output end Refutation
% 41.25/41.47  
% 41.25/41.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
