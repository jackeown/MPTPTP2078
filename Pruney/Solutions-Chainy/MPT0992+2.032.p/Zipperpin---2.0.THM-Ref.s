%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s5gJQm7nCQ

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:39 EST 2020

% Result     : Theorem 39.03s
% Output     : Refutation 39.03s
% Verified   : 
% Statistics : Number of formulae       :  242 (4019 expanded)
%              Number of leaves         :   44 (1105 expanded)
%              Depth                    :   28
%              Number of atoms          : 1966 (64149 expanded)
%              Number of equality atoms :  159 (4894 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('16',plain,(
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

thf('17',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('31',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('42',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','44'])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','39'])).

thf('47',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('48',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('51',plain,(
    ! [X36: $i] :
      ( zip_tseitin_0 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','53'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('55',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X31 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('56',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
        | ~ ( v1_relat_1 @ sk_D )
        | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
        | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','39'])).

thf('58',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('59',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( v5_relat_1 @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('62',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D )
        | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('65',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('66',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','66'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('69',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('70',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['64','65'])).

thf('73',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('75',plain,
    ( ! [X0: $i,X1: $i] :
        ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','71','72','73','74'])).

thf('76',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ( ( k2_partfun1 @ X49 @ X50 @ X48 @ X51 )
        = ( k7_relat_1 @ X48 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('77',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( ( k2_partfun1 @ X1 @ X0 @ sk_D @ X2 )
          = ( k7_relat_1 @ sk_D @ X2 ) )
        | ~ ( v1_funct_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','39'])).

thf('79',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('80',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( v4_relat_1 @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','82'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('84',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D )
        | ( sk_D
          = ( k7_relat_1 @ sk_D @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['64','65'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X1 @ X0 @ sk_D @ X2 )
        = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','87','88'])).

thf('90',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('91',plain,
    ( ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('93',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('96',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('98',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','39'])).

thf('99',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('100',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('101',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X1 @ X0 @ sk_D @ X2 )
        = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','87','88'])).

thf('102',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('104',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','53'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
        | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['91','96','97','98','99','100','101','102','110'])).

thf('112',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('113',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['111','112'])).

thf('114',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','113'])).

thf('115',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['27','114'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('116',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['64','65'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('123',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('125',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['64','65'])).

thf('127',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['125','126'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('128',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('130',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['129'])).

thf('132',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X31 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','133'])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('135',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r1_tarski @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('143',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('145',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['127','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['64','65'])).

thf('149',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('153',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r1_tarski @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['152','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['64','65'])).

thf('158',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('160',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['151','160'])).

thf('162',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['120','161'])).

thf('163',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['13','162'])).

thf('164',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['120','161'])).

thf('165',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('166',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','119'])).

thf('168',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('170',plain,
    ( ( sk_C != sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['120','161'])).

thf('173',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('174',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['125','126'])).

thf('176',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('177',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('178',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','178'])).

thf('180',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['129'])).

thf('181',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','178'])).

thf('183',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['125','126'])).

thf('184',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('185',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_B
        = ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['182','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( sk_B
        = ( k2_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['181','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_B
        = ( k2_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['180','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_B
        = ( k2_relat_1 @ sk_D ) ) ) ),
    inference(condensation,[status(thm)],['188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X1 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['179','189'])).

thf('191',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','113'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(condensation,[status(thm)],['192'])).

thf('194',plain,(
    zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['174','193'])).

thf('195',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['171','194'])).

thf('196',plain,(
    $false ),
    inference(demod,[status(thm)],['163','195'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s5gJQm7nCQ
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:18:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 39.03/39.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 39.03/39.24  % Solved by: fo/fo7.sh
% 39.03/39.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 39.03/39.24  % done 17825 iterations in 38.778s
% 39.03/39.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 39.03/39.24  % SZS output start Refutation
% 39.03/39.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 39.03/39.24  thf(sk_A_type, type, sk_A: $i).
% 39.03/39.24  thf(sk_D_type, type, sk_D: $i).
% 39.03/39.24  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 39.03/39.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 39.03/39.24  thf(sk_C_type, type, sk_C: $i).
% 39.03/39.24  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 39.03/39.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 39.03/39.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 39.03/39.24  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 39.03/39.24  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 39.03/39.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 39.03/39.24  thf(sk_B_type, type, sk_B: $i).
% 39.03/39.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 39.03/39.24  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 39.03/39.24  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 39.03/39.24  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 39.03/39.24  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 39.03/39.24  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 39.03/39.24  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 39.03/39.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 39.03/39.24  thf(t38_funct_2, conjecture,
% 39.03/39.24    (![A:$i,B:$i,C:$i,D:$i]:
% 39.03/39.24     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 39.03/39.24         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 39.03/39.24       ( ( r1_tarski @ C @ A ) =>
% 39.03/39.24         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 39.03/39.24           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 39.03/39.24             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 39.03/39.24             ( m1_subset_1 @
% 39.03/39.24               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 39.03/39.24               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 39.03/39.24  thf(zf_stmt_0, negated_conjecture,
% 39.03/39.24    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 39.03/39.24        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 39.03/39.24            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 39.03/39.24          ( ( r1_tarski @ C @ A ) =>
% 39.03/39.24            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 39.03/39.24              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 39.03/39.24                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 39.03/39.24                ( m1_subset_1 @
% 39.03/39.24                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 39.03/39.24                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 39.03/39.24    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 39.03/39.24  thf('0', plain,
% 39.03/39.24      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 39.03/39.24        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 39.03/39.24             sk_B)
% 39.03/39.24        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.03/39.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf('1', plain,
% 39.03/39.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf(dt_k2_partfun1, axiom,
% 39.03/39.24    (![A:$i,B:$i,C:$i,D:$i]:
% 39.03/39.24     ( ( ( v1_funct_1 @ C ) & 
% 39.03/39.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 39.03/39.24       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 39.03/39.24         ( m1_subset_1 @
% 39.03/39.24           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 39.03/39.24           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 39.03/39.24  thf('2', plain,
% 39.03/39.24      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 39.03/39.24         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 39.03/39.24          | ~ (v1_funct_1 @ X44)
% 39.03/39.24          | (v1_funct_1 @ (k2_partfun1 @ X45 @ X46 @ X44 @ X47)))),
% 39.03/39.24      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 39.03/39.24  thf('3', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 39.03/39.24          | ~ (v1_funct_1 @ sk_D))),
% 39.03/39.24      inference('sup-', [status(thm)], ['1', '2'])).
% 39.03/39.24  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf('5', plain,
% 39.03/39.24      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 39.03/39.24      inference('demod', [status(thm)], ['3', '4'])).
% 39.03/39.24  thf('6', plain,
% 39.03/39.24      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 39.03/39.24        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.03/39.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 39.03/39.24      inference('demod', [status(thm)], ['0', '5'])).
% 39.03/39.24  thf('7', plain,
% 39.03/39.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf(redefinition_k2_partfun1, axiom,
% 39.03/39.24    (![A:$i,B:$i,C:$i,D:$i]:
% 39.03/39.24     ( ( ( v1_funct_1 @ C ) & 
% 39.03/39.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 39.03/39.24       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 39.03/39.24  thf('8', plain,
% 39.03/39.24      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 39.03/39.24         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 39.03/39.24          | ~ (v1_funct_1 @ X48)
% 39.03/39.24          | ((k2_partfun1 @ X49 @ X50 @ X48 @ X51) = (k7_relat_1 @ X48 @ X51)))),
% 39.03/39.24      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 39.03/39.24  thf('9', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 39.03/39.24          | ~ (v1_funct_1 @ sk_D))),
% 39.03/39.24      inference('sup-', [status(thm)], ['7', '8'])).
% 39.03/39.24  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf('11', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 39.03/39.24      inference('demod', [status(thm)], ['9', '10'])).
% 39.03/39.24  thf('12', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 39.03/39.24      inference('demod', [status(thm)], ['9', '10'])).
% 39.03/39.24  thf('13', plain,
% 39.03/39.24      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 39.03/39.24        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 39.03/39.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 39.03/39.24      inference('demod', [status(thm)], ['6', '11', '12'])).
% 39.03/39.24  thf('14', plain, ((r1_tarski @ sk_C @ sk_A)),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf(d1_funct_2, axiom,
% 39.03/39.24    (![A:$i,B:$i,C:$i]:
% 39.03/39.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 39.03/39.24       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 39.03/39.24           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 39.03/39.24             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 39.03/39.24         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 39.03/39.24           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 39.03/39.24             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 39.03/39.24  thf(zf_stmt_1, axiom,
% 39.03/39.24    (![B:$i,A:$i]:
% 39.03/39.24     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 39.03/39.24       ( zip_tseitin_0 @ B @ A ) ))).
% 39.03/39.24  thf('15', plain,
% 39.03/39.24      (![X36 : $i, X37 : $i]:
% 39.03/39.24         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_1])).
% 39.03/39.24  thf('16', plain,
% 39.03/39.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 39.03/39.24  thf(zf_stmt_3, axiom,
% 39.03/39.24    (![C:$i,B:$i,A:$i]:
% 39.03/39.24     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 39.03/39.24       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 39.03/39.24  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 39.03/39.24  thf(zf_stmt_5, axiom,
% 39.03/39.24    (![A:$i,B:$i,C:$i]:
% 39.03/39.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 39.03/39.24       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 39.03/39.24         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 39.03/39.24           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 39.03/39.24             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 39.03/39.24  thf('17', plain,
% 39.03/39.24      (![X41 : $i, X42 : $i, X43 : $i]:
% 39.03/39.24         (~ (zip_tseitin_0 @ X41 @ X42)
% 39.03/39.24          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 39.03/39.24          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_5])).
% 39.03/39.24  thf('18', plain,
% 39.03/39.24      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 39.03/39.24      inference('sup-', [status(thm)], ['16', '17'])).
% 39.03/39.24  thf('19', plain,
% 39.03/39.24      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 39.03/39.24      inference('sup-', [status(thm)], ['15', '18'])).
% 39.03/39.24  thf('20', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf('21', plain,
% 39.03/39.24      (![X38 : $i, X39 : $i, X40 : $i]:
% 39.03/39.24         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 39.03/39.24          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 39.03/39.24          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_3])).
% 39.03/39.24  thf('22', plain,
% 39.03/39.24      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 39.03/39.24        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 39.03/39.24      inference('sup-', [status(thm)], ['20', '21'])).
% 39.03/39.24  thf('23', plain,
% 39.03/39.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf(redefinition_k1_relset_1, axiom,
% 39.03/39.24    (![A:$i,B:$i,C:$i]:
% 39.03/39.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 39.03/39.24       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 39.03/39.24  thf('24', plain,
% 39.03/39.24      (![X26 : $i, X27 : $i, X28 : $i]:
% 39.03/39.24         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 39.03/39.24          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 39.03/39.24      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 39.03/39.24  thf('25', plain,
% 39.03/39.24      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 39.03/39.24      inference('sup-', [status(thm)], ['23', '24'])).
% 39.03/39.24  thf('26', plain,
% 39.03/39.24      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 39.03/39.24      inference('demod', [status(thm)], ['22', '25'])).
% 39.03/39.24  thf('27', plain,
% 39.03/39.24      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 39.03/39.24      inference('sup-', [status(thm)], ['19', '26'])).
% 39.03/39.24  thf('28', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf('29', plain,
% 39.03/39.24      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 39.03/39.24      inference('split', [status(esa)], ['28'])).
% 39.03/39.24  thf('30', plain,
% 39.03/39.24      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('split', [status(esa)], ['28'])).
% 39.03/39.24  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf('32', plain,
% 39.03/39.24      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup+', [status(thm)], ['30', '31'])).
% 39.03/39.24  thf('33', plain,
% 39.03/39.24      (![X38 : $i, X39 : $i, X40 : $i]:
% 39.03/39.24         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 39.03/39.24          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 39.03/39.24          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_3])).
% 39.03/39.24  thf('34', plain,
% 39.03/39.24      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 39.03/39.24         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['32', '33'])).
% 39.03/39.24  thf('35', plain,
% 39.03/39.24      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('split', [status(esa)], ['28'])).
% 39.03/39.24  thf('36', plain,
% 39.03/39.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf('37', plain,
% 39.03/39.24      (((m1_subset_1 @ sk_D @ 
% 39.03/39.24         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup+', [status(thm)], ['35', '36'])).
% 39.03/39.24  thf(t113_zfmisc_1, axiom,
% 39.03/39.24    (![A:$i,B:$i]:
% 39.03/39.24     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 39.03/39.24       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 39.03/39.24  thf('38', plain,
% 39.03/39.24      (![X8 : $i, X9 : $i]:
% 39.03/39.24         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 39.03/39.24      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 39.03/39.24  thf('39', plain,
% 39.03/39.24      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 39.03/39.24      inference('simplify', [status(thm)], ['38'])).
% 39.03/39.24  thf('40', plain,
% 39.03/39.24      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['37', '39'])).
% 39.03/39.24  thf('41', plain,
% 39.03/39.24      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 39.03/39.24      inference('simplify', [status(thm)], ['38'])).
% 39.03/39.24  thf('42', plain,
% 39.03/39.24      (![X26 : $i, X27 : $i, X28 : $i]:
% 39.03/39.24         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 39.03/39.24          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 39.03/39.24      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 39.03/39.24  thf('43', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 39.03/39.24          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 39.03/39.24      inference('sup-', [status(thm)], ['41', '42'])).
% 39.03/39.24  thf('44', plain,
% 39.03/39.24      ((![X0 : $i]:
% 39.03/39.24          ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['40', '43'])).
% 39.03/39.24  thf('45', plain,
% 39.03/39.24      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 39.03/39.24         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['34', '44'])).
% 39.03/39.24  thf('46', plain,
% 39.03/39.24      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['37', '39'])).
% 39.03/39.24  thf('47', plain,
% 39.03/39.24      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 39.03/39.24      inference('simplify', [status(thm)], ['38'])).
% 39.03/39.24  thf('48', plain,
% 39.03/39.24      (![X41 : $i, X42 : $i, X43 : $i]:
% 39.03/39.24         (~ (zip_tseitin_0 @ X41 @ X42)
% 39.03/39.24          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 39.03/39.24          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_5])).
% 39.03/39.24  thf('49', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 39.03/39.24          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 39.03/39.24          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 39.03/39.24      inference('sup-', [status(thm)], ['47', '48'])).
% 39.03/39.24  thf('50', plain,
% 39.03/39.24      (![X36 : $i, X37 : $i]:
% 39.03/39.24         ((zip_tseitin_0 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_1])).
% 39.03/39.24  thf('51', plain, (![X36 : $i]: (zip_tseitin_0 @ X36 @ k1_xboole_0)),
% 39.03/39.24      inference('simplify', [status(thm)], ['50'])).
% 39.03/39.24  thf('52', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 39.03/39.24          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 39.03/39.24      inference('demod', [status(thm)], ['49', '51'])).
% 39.03/39.24  thf('53', plain,
% 39.03/39.24      ((![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['46', '52'])).
% 39.03/39.24  thf('54', plain,
% 39.03/39.24      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['45', '53'])).
% 39.03/39.24  thf(t11_relset_1, axiom,
% 39.03/39.24    (![A:$i,B:$i,C:$i]:
% 39.03/39.24     ( ( v1_relat_1 @ C ) =>
% 39.03/39.24       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 39.03/39.24           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 39.03/39.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 39.03/39.24  thf('55', plain,
% 39.03/39.24      (![X29 : $i, X30 : $i, X31 : $i]:
% 39.03/39.24         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 39.03/39.24          | ~ (r1_tarski @ (k2_relat_1 @ X29) @ X31)
% 39.03/39.24          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 39.03/39.24          | ~ (v1_relat_1 @ X29))),
% 39.03/39.24      inference('cnf', [status(esa)], [t11_relset_1])).
% 39.03/39.24  thf('56', plain,
% 39.03/39.24      ((![X0 : $i, X1 : $i]:
% 39.03/39.24          (~ (r1_tarski @ k1_xboole_0 @ X0)
% 39.03/39.24           | ~ (v1_relat_1 @ sk_D)
% 39.03/39.24           | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 39.03/39.24           | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X1)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['54', '55'])).
% 39.03/39.24  thf('57', plain,
% 39.03/39.24      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['37', '39'])).
% 39.03/39.24  thf('58', plain,
% 39.03/39.24      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 39.03/39.24      inference('simplify', [status(thm)], ['38'])).
% 39.03/39.24  thf(cc2_relset_1, axiom,
% 39.03/39.24    (![A:$i,B:$i,C:$i]:
% 39.03/39.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 39.03/39.24       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 39.03/39.24  thf('59', plain,
% 39.03/39.24      (![X23 : $i, X24 : $i, X25 : $i]:
% 39.03/39.24         ((v5_relat_1 @ X23 @ X25)
% 39.03/39.24          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 39.03/39.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 39.03/39.24  thf('60', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 39.03/39.24          | (v5_relat_1 @ X1 @ X0))),
% 39.03/39.24      inference('sup-', [status(thm)], ['58', '59'])).
% 39.03/39.24  thf('61', plain,
% 39.03/39.24      ((![X0 : $i]: (v5_relat_1 @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['57', '60'])).
% 39.03/39.24  thf(d19_relat_1, axiom,
% 39.03/39.24    (![A:$i,B:$i]:
% 39.03/39.24     ( ( v1_relat_1 @ B ) =>
% 39.03/39.24       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 39.03/39.24  thf('62', plain,
% 39.03/39.24      (![X10 : $i, X11 : $i]:
% 39.03/39.24         (~ (v5_relat_1 @ X10 @ X11)
% 39.03/39.24          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 39.03/39.24          | ~ (v1_relat_1 @ X10))),
% 39.03/39.24      inference('cnf', [status(esa)], [d19_relat_1])).
% 39.03/39.24  thf('63', plain,
% 39.03/39.24      ((![X0 : $i]:
% 39.03/39.24          (~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ X0)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['61', '62'])).
% 39.03/39.24  thf('64', plain,
% 39.03/39.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf(cc1_relset_1, axiom,
% 39.03/39.24    (![A:$i,B:$i,C:$i]:
% 39.03/39.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 39.03/39.24       ( v1_relat_1 @ C ) ))).
% 39.03/39.24  thf('65', plain,
% 39.03/39.24      (![X20 : $i, X21 : $i, X22 : $i]:
% 39.03/39.24         ((v1_relat_1 @ X20)
% 39.03/39.24          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 39.03/39.24      inference('cnf', [status(esa)], [cc1_relset_1])).
% 39.03/39.24  thf('66', plain, ((v1_relat_1 @ sk_D)),
% 39.03/39.24      inference('sup-', [status(thm)], ['64', '65'])).
% 39.03/39.24  thf('67', plain,
% 39.03/39.24      ((![X0 : $i]: (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['63', '66'])).
% 39.03/39.24  thf('68', plain,
% 39.03/39.24      ((![X0 : $i]: (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['63', '66'])).
% 39.03/39.24  thf(t3_xboole_1, axiom,
% 39.03/39.24    (![A:$i]:
% 39.03/39.24     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 39.03/39.24  thf('69', plain,
% 39.03/39.24      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 39.03/39.24      inference('cnf', [status(esa)], [t3_xboole_1])).
% 39.03/39.24  thf('70', plain,
% 39.03/39.24      ((((k2_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['68', '69'])).
% 39.03/39.24  thf('71', plain,
% 39.03/39.24      ((![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['67', '70'])).
% 39.03/39.24  thf('72', plain, ((v1_relat_1 @ sk_D)),
% 39.03/39.24      inference('sup-', [status(thm)], ['64', '65'])).
% 39.03/39.24  thf('73', plain,
% 39.03/39.24      ((((k2_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['68', '69'])).
% 39.03/39.24  thf('74', plain,
% 39.03/39.24      ((![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['67', '70'])).
% 39.03/39.24  thf('75', plain,
% 39.03/39.24      ((![X0 : $i, X1 : $i]:
% 39.03/39.24          (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['56', '71', '72', '73', '74'])).
% 39.03/39.24  thf('76', plain,
% 39.03/39.24      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 39.03/39.24         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 39.03/39.24          | ~ (v1_funct_1 @ X48)
% 39.03/39.24          | ((k2_partfun1 @ X49 @ X50 @ X48 @ X51) = (k7_relat_1 @ X48 @ X51)))),
% 39.03/39.24      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 39.03/39.24  thf('77', plain,
% 39.03/39.24      ((![X0 : $i, X1 : $i, X2 : $i]:
% 39.03/39.24          (((k2_partfun1 @ X1 @ X0 @ sk_D @ X2) = (k7_relat_1 @ sk_D @ X2))
% 39.03/39.24           | ~ (v1_funct_1 @ sk_D)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['75', '76'])).
% 39.03/39.24  thf('78', plain,
% 39.03/39.24      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['37', '39'])).
% 39.03/39.24  thf('79', plain,
% 39.03/39.24      (![X8 : $i, X9 : $i]:
% 39.03/39.24         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 39.03/39.24      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 39.03/39.24  thf('80', plain,
% 39.03/39.24      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 39.03/39.24      inference('simplify', [status(thm)], ['79'])).
% 39.03/39.24  thf('81', plain,
% 39.03/39.24      (![X23 : $i, X24 : $i, X25 : $i]:
% 39.03/39.24         ((v4_relat_1 @ X23 @ X24)
% 39.03/39.24          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 39.03/39.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 39.03/39.24  thf('82', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 39.03/39.24          | (v4_relat_1 @ X1 @ X0))),
% 39.03/39.24      inference('sup-', [status(thm)], ['80', '81'])).
% 39.03/39.24  thf('83', plain,
% 39.03/39.24      ((![X0 : $i]: (v4_relat_1 @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['78', '82'])).
% 39.03/39.24  thf(t209_relat_1, axiom,
% 39.03/39.24    (![A:$i,B:$i]:
% 39.03/39.24     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 39.03/39.24       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 39.03/39.24  thf('84', plain,
% 39.03/39.24      (![X14 : $i, X15 : $i]:
% 39.03/39.24         (((X14) = (k7_relat_1 @ X14 @ X15))
% 39.03/39.24          | ~ (v4_relat_1 @ X14 @ X15)
% 39.03/39.24          | ~ (v1_relat_1 @ X14))),
% 39.03/39.24      inference('cnf', [status(esa)], [t209_relat_1])).
% 39.03/39.24  thf('85', plain,
% 39.03/39.24      ((![X0 : $i]:
% 39.03/39.24          (~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ X0))))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['83', '84'])).
% 39.03/39.24  thf('86', plain, ((v1_relat_1 @ sk_D)),
% 39.03/39.24      inference('sup-', [status(thm)], ['64', '65'])).
% 39.03/39.24  thf('87', plain,
% 39.03/39.24      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['85', '86'])).
% 39.03/39.24  thf('88', plain, ((v1_funct_1 @ sk_D)),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf('89', plain,
% 39.03/39.24      ((![X0 : $i, X1 : $i, X2 : $i]:
% 39.03/39.24          ((k2_partfun1 @ X1 @ X0 @ sk_D @ X2) = (sk_D)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['77', '87', '88'])).
% 39.03/39.24  thf('90', plain,
% 39.03/39.24      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 39.03/39.24        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.03/39.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 39.03/39.24      inference('demod', [status(thm)], ['0', '5'])).
% 39.03/39.24  thf('91', plain,
% 39.03/39.24      (((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 39.03/39.24         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 39.03/39.24              sk_B)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['89', '90'])).
% 39.03/39.24  thf('92', plain,
% 39.03/39.24      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('split', [status(esa)], ['28'])).
% 39.03/39.24  thf('93', plain, ((r1_tarski @ sk_C @ sk_A)),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf('94', plain,
% 39.03/39.24      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup+', [status(thm)], ['92', '93'])).
% 39.03/39.24  thf('95', plain,
% 39.03/39.24      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 39.03/39.24      inference('cnf', [status(esa)], [t3_xboole_1])).
% 39.03/39.24  thf('96', plain,
% 39.03/39.24      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['94', '95'])).
% 39.03/39.24  thf('97', plain,
% 39.03/39.24      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 39.03/39.24      inference('simplify', [status(thm)], ['38'])).
% 39.03/39.24  thf('98', plain,
% 39.03/39.24      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['37', '39'])).
% 39.03/39.24  thf('99', plain,
% 39.03/39.24      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('split', [status(esa)], ['28'])).
% 39.03/39.24  thf('100', plain,
% 39.03/39.24      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['94', '95'])).
% 39.03/39.24  thf('101', plain,
% 39.03/39.24      ((![X0 : $i, X1 : $i, X2 : $i]:
% 39.03/39.24          ((k2_partfun1 @ X1 @ X0 @ sk_D @ X2) = (sk_D)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['77', '87', '88'])).
% 39.03/39.24  thf('102', plain,
% 39.03/39.24      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['94', '95'])).
% 39.03/39.24  thf('103', plain,
% 39.03/39.24      ((![X0 : $i]:
% 39.03/39.24          ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['40', '43'])).
% 39.03/39.24  thf('104', plain,
% 39.03/39.24      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['45', '53'])).
% 39.03/39.24  thf('105', plain,
% 39.03/39.24      ((![X0 : $i]: ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_xboole_0)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['103', '104'])).
% 39.03/39.24  thf('106', plain,
% 39.03/39.24      (![X38 : $i, X39 : $i, X40 : $i]:
% 39.03/39.24         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 39.03/39.24          | (v1_funct_2 @ X40 @ X38 @ X39)
% 39.03/39.24          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_3])).
% 39.03/39.24  thf('107', plain,
% 39.03/39.24      ((![X0 : $i]:
% 39.03/39.24          (((k1_xboole_0) != (k1_xboole_0))
% 39.03/39.24           | ~ (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0)
% 39.03/39.24           | (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['105', '106'])).
% 39.03/39.24  thf('108', plain,
% 39.03/39.24      ((![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['46', '52'])).
% 39.03/39.24  thf('109', plain,
% 39.03/39.24      ((![X0 : $i]:
% 39.03/39.24          (((k1_xboole_0) != (k1_xboole_0))
% 39.03/39.24           | (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('demod', [status(thm)], ['107', '108'])).
% 39.03/39.24  thf('110', plain,
% 39.03/39.24      ((![X0 : $i]: (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0))
% 39.03/39.24         <= ((((sk_A) = (k1_xboole_0))))),
% 39.03/39.24      inference('simplify', [status(thm)], ['109'])).
% 39.03/39.24  thf('111', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 39.03/39.24      inference('demod', [status(thm)],
% 39.03/39.24                ['91', '96', '97', '98', '99', '100', '101', '102', '110'])).
% 39.03/39.24  thf('112', plain,
% 39.03/39.24      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 39.03/39.24      inference('split', [status(esa)], ['28'])).
% 39.03/39.24  thf('113', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 39.03/39.24      inference('sat_resolution*', [status(thm)], ['111', '112'])).
% 39.03/39.24  thf('114', plain, (((sk_B) != (k1_xboole_0))),
% 39.03/39.24      inference('simpl_trail', [status(thm)], ['29', '113'])).
% 39.03/39.24  thf('115', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 39.03/39.24      inference('simplify_reflect-', [status(thm)], ['27', '114'])).
% 39.03/39.24  thf(t91_relat_1, axiom,
% 39.03/39.24    (![A:$i,B:$i]:
% 39.03/39.24     ( ( v1_relat_1 @ B ) =>
% 39.03/39.24       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 39.03/39.24         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 39.03/39.24  thf('116', plain,
% 39.03/39.24      (![X18 : $i, X19 : $i]:
% 39.03/39.24         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 39.03/39.24          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 39.03/39.24          | ~ (v1_relat_1 @ X19))),
% 39.03/39.24      inference('cnf', [status(esa)], [t91_relat_1])).
% 39.03/39.24  thf('117', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         (~ (r1_tarski @ X0 @ sk_A)
% 39.03/39.24          | ~ (v1_relat_1 @ sk_D)
% 39.03/39.24          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 39.03/39.24      inference('sup-', [status(thm)], ['115', '116'])).
% 39.03/39.24  thf('118', plain, ((v1_relat_1 @ sk_D)),
% 39.03/39.24      inference('sup-', [status(thm)], ['64', '65'])).
% 39.03/39.24  thf('119', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         (~ (r1_tarski @ X0 @ sk_A)
% 39.03/39.24          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 39.03/39.24      inference('demod', [status(thm)], ['117', '118'])).
% 39.03/39.24  thf('120', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 39.03/39.24      inference('sup-', [status(thm)], ['14', '119'])).
% 39.03/39.24  thf('121', plain,
% 39.03/39.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf('122', plain,
% 39.03/39.24      (![X23 : $i, X24 : $i, X25 : $i]:
% 39.03/39.24         ((v5_relat_1 @ X23 @ X25)
% 39.03/39.24          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 39.03/39.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 39.03/39.24  thf('123', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 39.03/39.24      inference('sup-', [status(thm)], ['121', '122'])).
% 39.03/39.24  thf('124', plain,
% 39.03/39.24      (![X10 : $i, X11 : $i]:
% 39.03/39.24         (~ (v5_relat_1 @ X10 @ X11)
% 39.03/39.24          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 39.03/39.24          | ~ (v1_relat_1 @ X10))),
% 39.03/39.24      inference('cnf', [status(esa)], [d19_relat_1])).
% 39.03/39.24  thf('125', plain,
% 39.03/39.24      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 39.03/39.24      inference('sup-', [status(thm)], ['123', '124'])).
% 39.03/39.24  thf('126', plain, ((v1_relat_1 @ sk_D)),
% 39.03/39.24      inference('sup-', [status(thm)], ['64', '65'])).
% 39.03/39.24  thf('127', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 39.03/39.24      inference('demod', [status(thm)], ['125', '126'])).
% 39.03/39.24  thf(t88_relat_1, axiom,
% 39.03/39.24    (![A:$i,B:$i]:
% 39.03/39.24     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 39.03/39.24  thf('128', plain,
% 39.03/39.24      (![X16 : $i, X17 : $i]:
% 39.03/39.24         ((r1_tarski @ (k7_relat_1 @ X16 @ X17) @ X16) | ~ (v1_relat_1 @ X16))),
% 39.03/39.24      inference('cnf', [status(esa)], [t88_relat_1])).
% 39.03/39.24  thf(d10_xboole_0, axiom,
% 39.03/39.24    (![A:$i,B:$i]:
% 39.03/39.24     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 39.03/39.24  thf('129', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 39.03/39.24      inference('cnf', [status(esa)], [d10_xboole_0])).
% 39.03/39.24  thf('130', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 39.03/39.24      inference('simplify', [status(thm)], ['129'])).
% 39.03/39.24  thf('131', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 39.03/39.24      inference('simplify', [status(thm)], ['129'])).
% 39.03/39.24  thf('132', plain,
% 39.03/39.24      (![X29 : $i, X30 : $i, X31 : $i]:
% 39.03/39.24         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 39.03/39.24          | ~ (r1_tarski @ (k2_relat_1 @ X29) @ X31)
% 39.03/39.24          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 39.03/39.24          | ~ (v1_relat_1 @ X29))),
% 39.03/39.24      inference('cnf', [status(esa)], [t11_relset_1])).
% 39.03/39.24  thf('133', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         (~ (v1_relat_1 @ X0)
% 39.03/39.24          | (m1_subset_1 @ X0 @ 
% 39.03/39.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 39.03/39.24          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 39.03/39.24      inference('sup-', [status(thm)], ['131', '132'])).
% 39.03/39.24  thf('134', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         ((m1_subset_1 @ X0 @ 
% 39.03/39.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 39.03/39.24          | ~ (v1_relat_1 @ X0))),
% 39.03/39.24      inference('sup-', [status(thm)], ['130', '133'])).
% 39.03/39.24  thf(t4_relset_1, axiom,
% 39.03/39.24    (![A:$i,B:$i,C:$i,D:$i]:
% 39.03/39.24     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 39.03/39.24       ( ( r1_tarski @ A @ D ) =>
% 39.03/39.24         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 39.03/39.24  thf('135', plain,
% 39.03/39.24      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 39.03/39.24         ((m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 39.03/39.24          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 39.03/39.24          | ~ (r1_tarski @ X32 @ X35))),
% 39.03/39.24      inference('cnf', [status(esa)], [t4_relset_1])).
% 39.03/39.24  thf('136', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         (~ (v1_relat_1 @ X0)
% 39.03/39.24          | ~ (r1_tarski @ X1 @ X0)
% 39.03/39.24          | (m1_subset_1 @ X1 @ 
% 39.03/39.24             (k1_zfmisc_1 @ 
% 39.03/39.24              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['134', '135'])).
% 39.03/39.24  thf('137', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         (~ (v1_relat_1 @ X0)
% 39.03/39.24          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 39.03/39.24             (k1_zfmisc_1 @ 
% 39.03/39.24              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 39.03/39.24          | ~ (v1_relat_1 @ X0))),
% 39.03/39.24      inference('sup-', [status(thm)], ['128', '136'])).
% 39.03/39.24  thf('138', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         ((m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 39.03/39.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 39.03/39.24          | ~ (v1_relat_1 @ X0))),
% 39.03/39.24      inference('simplify', [status(thm)], ['137'])).
% 39.03/39.24  thf('139', plain,
% 39.03/39.24      (![X23 : $i, X24 : $i, X25 : $i]:
% 39.03/39.24         ((v5_relat_1 @ X23 @ X25)
% 39.03/39.24          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 39.03/39.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 39.03/39.24  thf('140', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         (~ (v1_relat_1 @ X0)
% 39.03/39.24          | (v5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 39.03/39.24      inference('sup-', [status(thm)], ['138', '139'])).
% 39.03/39.24  thf('141', plain,
% 39.03/39.24      (![X10 : $i, X11 : $i]:
% 39.03/39.24         (~ (v5_relat_1 @ X10 @ X11)
% 39.03/39.24          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 39.03/39.24          | ~ (v1_relat_1 @ X10))),
% 39.03/39.24      inference('cnf', [status(esa)], [d19_relat_1])).
% 39.03/39.24  thf('142', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         (~ (v1_relat_1 @ X0)
% 39.03/39.24          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 39.03/39.24          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 39.03/39.24             (k2_relat_1 @ X0)))),
% 39.03/39.24      inference('sup-', [status(thm)], ['140', '141'])).
% 39.03/39.24  thf(dt_k7_relat_1, axiom,
% 39.03/39.24    (![A:$i,B:$i]:
% 39.03/39.24     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 39.03/39.24  thf('143', plain,
% 39.03/39.24      (![X12 : $i, X13 : $i]:
% 39.03/39.24         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 39.03/39.24      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 39.03/39.24  thf('144', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 39.03/39.24           (k2_relat_1 @ X0))
% 39.03/39.24          | ~ (v1_relat_1 @ X0))),
% 39.03/39.24      inference('clc', [status(thm)], ['142', '143'])).
% 39.03/39.24  thf(t1_xboole_1, axiom,
% 39.03/39.24    (![A:$i,B:$i,C:$i]:
% 39.03/39.24     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 39.03/39.24       ( r1_tarski @ A @ C ) ))).
% 39.03/39.24  thf('145', plain,
% 39.03/39.24      (![X3 : $i, X4 : $i, X5 : $i]:
% 39.03/39.24         (~ (r1_tarski @ X3 @ X4)
% 39.03/39.24          | ~ (r1_tarski @ X4 @ X5)
% 39.03/39.24          | (r1_tarski @ X3 @ X5))),
% 39.03/39.24      inference('cnf', [status(esa)], [t1_xboole_1])).
% 39.03/39.24  thf('146', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.03/39.24         (~ (v1_relat_1 @ X0)
% 39.03/39.24          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 39.03/39.24          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X2))),
% 39.03/39.24      inference('sup-', [status(thm)], ['144', '145'])).
% 39.03/39.24  thf('147', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)
% 39.03/39.24          | ~ (v1_relat_1 @ sk_D))),
% 39.03/39.24      inference('sup-', [status(thm)], ['127', '146'])).
% 39.03/39.24  thf('148', plain, ((v1_relat_1 @ sk_D)),
% 39.03/39.24      inference('sup-', [status(thm)], ['64', '65'])).
% 39.03/39.24  thf('149', plain,
% 39.03/39.24      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 39.03/39.24      inference('demod', [status(thm)], ['147', '148'])).
% 39.03/39.24  thf('150', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         (~ (v1_relat_1 @ X0)
% 39.03/39.24          | (m1_subset_1 @ X0 @ 
% 39.03/39.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 39.03/39.24          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 39.03/39.24      inference('sup-', [status(thm)], ['131', '132'])).
% 39.03/39.24  thf('151', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 39.03/39.24           (k1_zfmisc_1 @ 
% 39.03/39.24            (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))
% 39.03/39.24          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 39.03/39.24      inference('sup-', [status(thm)], ['149', '150'])).
% 39.03/39.24  thf('152', plain,
% 39.03/39.24      (![X16 : $i, X17 : $i]:
% 39.03/39.24         ((r1_tarski @ (k7_relat_1 @ X16 @ X17) @ X16) | ~ (v1_relat_1 @ X16))),
% 39.03/39.24      inference('cnf', [status(esa)], [t88_relat_1])).
% 39.03/39.24  thf('153', plain,
% 39.03/39.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.03/39.24  thf('154', plain,
% 39.03/39.24      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 39.03/39.24         ((m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 39.03/39.24          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 39.03/39.24          | ~ (r1_tarski @ X32 @ X35))),
% 39.03/39.24      inference('cnf', [status(esa)], [t4_relset_1])).
% 39.03/39.24  thf('155', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         (~ (r1_tarski @ X0 @ sk_D)
% 39.03/39.24          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['153', '154'])).
% 39.03/39.24  thf('156', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         (~ (v1_relat_1 @ sk_D)
% 39.03/39.24          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 39.03/39.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 39.03/39.24      inference('sup-', [status(thm)], ['152', '155'])).
% 39.03/39.24  thf('157', plain, ((v1_relat_1 @ sk_D)),
% 39.03/39.24      inference('sup-', [status(thm)], ['64', '65'])).
% 39.03/39.24  thf('158', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 39.03/39.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.03/39.24      inference('demod', [status(thm)], ['156', '157'])).
% 39.03/39.24  thf('159', plain,
% 39.03/39.24      (![X20 : $i, X21 : $i, X22 : $i]:
% 39.03/39.24         ((v1_relat_1 @ X20)
% 39.03/39.24          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 39.03/39.24      inference('cnf', [status(esa)], [cc1_relset_1])).
% 39.03/39.24  thf('160', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 39.03/39.24      inference('sup-', [status(thm)], ['158', '159'])).
% 39.03/39.24  thf('161', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 39.03/39.24          (k1_zfmisc_1 @ 
% 39.03/39.24           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 39.03/39.24      inference('demod', [status(thm)], ['151', '160'])).
% 39.03/39.24  thf('162', plain,
% 39.03/39.24      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 39.03/39.24        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 39.03/39.24      inference('sup+', [status(thm)], ['120', '161'])).
% 39.03/39.24  thf('163', plain,
% 39.03/39.24      (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 39.03/39.24      inference('demod', [status(thm)], ['13', '162'])).
% 39.03/39.24  thf('164', plain,
% 39.03/39.24      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 39.03/39.24        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 39.03/39.24      inference('sup+', [status(thm)], ['120', '161'])).
% 39.03/39.24  thf('165', plain,
% 39.03/39.24      (![X26 : $i, X27 : $i, X28 : $i]:
% 39.03/39.24         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 39.03/39.24          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 39.03/39.24      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 39.03/39.24  thf('166', plain,
% 39.03/39.24      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C))
% 39.03/39.24         = (k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)))),
% 39.03/39.24      inference('sup-', [status(thm)], ['164', '165'])).
% 39.03/39.24  thf('167', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 39.03/39.24      inference('sup-', [status(thm)], ['14', '119'])).
% 39.03/39.24  thf('168', plain,
% 39.03/39.24      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 39.03/39.24      inference('demod', [status(thm)], ['166', '167'])).
% 39.03/39.24  thf('169', plain,
% 39.03/39.24      (![X38 : $i, X39 : $i, X40 : $i]:
% 39.03/39.24         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 39.03/39.24          | (v1_funct_2 @ X40 @ X38 @ X39)
% 39.03/39.24          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_3])).
% 39.03/39.24  thf('170', plain,
% 39.03/39.24      ((((sk_C) != (sk_C))
% 39.03/39.24        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 39.03/39.24        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 39.03/39.24      inference('sup-', [status(thm)], ['168', '169'])).
% 39.03/39.24  thf('171', plain,
% 39.03/39.24      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 39.03/39.24        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C))),
% 39.03/39.24      inference('simplify', [status(thm)], ['170'])).
% 39.03/39.24  thf('172', plain,
% 39.03/39.24      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 39.03/39.24        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 39.03/39.24      inference('sup+', [status(thm)], ['120', '161'])).
% 39.03/39.24  thf('173', plain,
% 39.03/39.24      (![X41 : $i, X42 : $i, X43 : $i]:
% 39.03/39.24         (~ (zip_tseitin_0 @ X41 @ X42)
% 39.03/39.24          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 39.03/39.24          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_5])).
% 39.03/39.24  thf('174', plain,
% 39.03/39.24      (((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 39.03/39.24        | ~ (zip_tseitin_0 @ sk_B @ sk_C))),
% 39.03/39.24      inference('sup-', [status(thm)], ['172', '173'])).
% 39.03/39.24  thf('175', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 39.03/39.24      inference('demod', [status(thm)], ['125', '126'])).
% 39.03/39.24  thf('176', plain,
% 39.03/39.24      (![X36 : $i, X37 : $i]:
% 39.03/39.24         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_1])).
% 39.03/39.24  thf('177', plain,
% 39.03/39.24      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 39.03/39.24      inference('cnf', [status(esa)], [t3_xboole_1])).
% 39.03/39.24  thf('178', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.03/39.24         (~ (r1_tarski @ X1 @ X0)
% 39.03/39.24          | (zip_tseitin_0 @ X0 @ X2)
% 39.03/39.24          | ((X1) = (k1_xboole_0)))),
% 39.03/39.24      inference('sup-', [status(thm)], ['176', '177'])).
% 39.03/39.24  thf('179', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B @ X0))),
% 39.03/39.24      inference('sup-', [status(thm)], ['175', '178'])).
% 39.03/39.24  thf('180', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 39.03/39.24      inference('simplify', [status(thm)], ['129'])).
% 39.03/39.24  thf('181', plain,
% 39.03/39.24      (![X36 : $i, X37 : $i]:
% 39.03/39.24         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 39.03/39.24      inference('cnf', [status(esa)], [zf_stmt_1])).
% 39.03/39.24  thf('182', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B @ X0))),
% 39.03/39.24      inference('sup-', [status(thm)], ['175', '178'])).
% 39.03/39.24  thf('183', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 39.03/39.24      inference('demod', [status(thm)], ['125', '126'])).
% 39.03/39.24  thf('184', plain,
% 39.03/39.24      (![X0 : $i, X2 : $i]:
% 39.03/39.24         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 39.03/39.24      inference('cnf', [status(esa)], [d10_xboole_0])).
% 39.03/39.24  thf('185', plain,
% 39.03/39.24      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 39.03/39.24        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 39.03/39.24      inference('sup-', [status(thm)], ['183', '184'])).
% 39.03/39.24  thf('186', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         (~ (r1_tarski @ sk_B @ k1_xboole_0)
% 39.03/39.24          | (zip_tseitin_0 @ sk_B @ X0)
% 39.03/39.24          | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 39.03/39.24      inference('sup-', [status(thm)], ['182', '185'])).
% 39.03/39.24  thf('187', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.03/39.24         (~ (r1_tarski @ sk_B @ X0)
% 39.03/39.24          | (zip_tseitin_0 @ X0 @ X2)
% 39.03/39.24          | ((sk_B) = (k2_relat_1 @ sk_D))
% 39.03/39.24          | (zip_tseitin_0 @ sk_B @ X1))),
% 39.03/39.24      inference('sup-', [status(thm)], ['181', '186'])).
% 39.03/39.24  thf('188', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         ((zip_tseitin_0 @ sk_B @ X0)
% 39.03/39.24          | ((sk_B) = (k2_relat_1 @ sk_D))
% 39.03/39.24          | (zip_tseitin_0 @ sk_B @ X1))),
% 39.03/39.24      inference('sup-', [status(thm)], ['180', '187'])).
% 39.03/39.24  thf('189', plain,
% 39.03/39.24      (![X0 : $i]:
% 39.03/39.24         ((zip_tseitin_0 @ sk_B @ X0) | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 39.03/39.24      inference('condensation', [status(thm)], ['188'])).
% 39.03/39.24  thf('190', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         (((sk_B) = (k1_xboole_0))
% 39.03/39.24          | (zip_tseitin_0 @ sk_B @ X1)
% 39.03/39.24          | (zip_tseitin_0 @ sk_B @ X0))),
% 39.03/39.24      inference('sup+', [status(thm)], ['179', '189'])).
% 39.03/39.24  thf('191', plain, (((sk_B) != (k1_xboole_0))),
% 39.03/39.24      inference('simpl_trail', [status(thm)], ['29', '113'])).
% 39.03/39.24  thf('192', plain,
% 39.03/39.24      (![X0 : $i, X1 : $i]:
% 39.03/39.24         ((zip_tseitin_0 @ sk_B @ X1) | (zip_tseitin_0 @ sk_B @ X0))),
% 39.03/39.24      inference('simplify_reflect-', [status(thm)], ['190', '191'])).
% 39.03/39.24  thf('193', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 39.03/39.24      inference('condensation', [status(thm)], ['192'])).
% 39.03/39.24  thf('194', plain,
% 39.03/39.24      ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)),
% 39.03/39.24      inference('demod', [status(thm)], ['174', '193'])).
% 39.03/39.24  thf('195', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 39.03/39.24      inference('demod', [status(thm)], ['171', '194'])).
% 39.03/39.24  thf('196', plain, ($false), inference('demod', [status(thm)], ['163', '195'])).
% 39.03/39.24  
% 39.03/39.24  % SZS output end Refutation
% 39.03/39.24  
% 39.09/39.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
