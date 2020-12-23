%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A86gzZav4e

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:15 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 443 expanded)
%              Number of leaves         :   46 ( 142 expanded)
%              Depth                    :   21
%              Number of atoms          : 1063 (5604 expanded)
%              Number of equality atoms :   78 ( 412 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t9_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v5_relat_1 @ sk_D @ sk_B_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B_1 ),
    inference(demod,[status(thm)],['10','15'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['5','18'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X44 ) @ X45 )
      | ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X44 ) @ X45 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('25',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('33',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('38',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('39',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('42',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('47',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','49'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('51',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['47','48'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('55',plain,(
    ! [X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X31 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('56',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','58'])).

thf('60',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('64',plain,(
    ! [X36: $i] :
      ( zip_tseitin_0 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('66',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['62','68'])).

thf('70',plain,(
    ! [X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X31 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('71',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('74',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','78'])).

thf('80',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('81',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','83'])).

thf('85',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('86',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('87',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('89',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('90',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('96',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','84','93','94','95'])).

thf('97',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','96'])).

thf('98',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['35','97'])).

thf('99',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['30','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22','23','99'])).

thf('101',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','102','103'])).

thf('105',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','104'])).

thf('106',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['5','18'])).

thf('107',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X44 ) @ X45 )
      | ( v1_funct_2 @ X44 @ ( k1_relat_1 @ X44 ) @ X45 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('110',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['30','98'])).

thf('112',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['105','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A86gzZav4e
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:20:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 361 iterations in 0.193s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.64  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.64  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.64  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(t9_funct_2, conjecture,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.64       ( ( r1_tarski @ B @ C ) =>
% 0.46/0.64         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.46/0.64           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.46/0.64             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.64            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.64          ( ( r1_tarski @ B @ C ) =>
% 0.46/0.64            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.46/0.64              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.46/0.64                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ sk_D)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.46/0.64        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.46/0.64         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.64  thf('5', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(cc2_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.64         ((v5_relat_1 @ X25 @ X27)
% 0.46/0.64          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.64  thf('8', plain, ((v5_relat_1 @ sk_D @ sk_B_1)),
% 0.46/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf(d19_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i]:
% 0.46/0.64         (~ (v5_relat_1 @ X15 @ X16)
% 0.46/0.64          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.46/0.64          | ~ (v1_relat_1 @ X15))),
% 0.46/0.64      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(cc2_relat_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.46/0.64          | (v1_relat_1 @ X13)
% 0.46/0.64          | ~ (v1_relat_1 @ X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.64  thf(fc6_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.64  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.64      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.64  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B_1)),
% 0.46/0.64      inference('demod', [status(thm)], ['10', '15'])).
% 0.46/0.64  thf(t1_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.64       ( r1_tarski @ A @ C ) ))).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.64          | ~ (r1_tarski @ X1 @ X2)
% 0.46/0.64          | (r1_tarski @ X0 @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.64  thf('19', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '18'])).
% 0.46/0.64  thf(t4_funct_2, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.64       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.46/0.64         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.46/0.64           ( m1_subset_1 @
% 0.46/0.64             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X44 : $i, X45 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k2_relat_1 @ X44) @ X45)
% 0.46/0.64          | (m1_subset_1 @ X44 @ 
% 0.46/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X44) @ X45)))
% 0.46/0.64          | ~ (v1_funct_1 @ X44)
% 0.46/0.64          | ~ (v1_relat_1 @ X44))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_D)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_D)
% 0.46/0.64        | (m1_subset_1 @ sk_D @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.64      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.64  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(d1_funct_2, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.64           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.64             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.64         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.64           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.64             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_1, axiom,
% 0.46/0.64    (![C:$i,B:$i,A:$i]:
% 0.46/0.64     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.64       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.46/0.64         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.46/0.64          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 0.46/0.64          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.46/0.64        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.64         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.46/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.46/0.64        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.46/0.64      inference('demod', [status(thm)], ['26', '29'])).
% 0.46/0.64  thf(zf_stmt_2, axiom,
% 0.46/0.64    (![B:$i,A:$i]:
% 0.46/0.64     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.64       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X36 : $i, X37 : $i]:
% 0.46/0.64         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_5, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.64         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.64           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.64             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.46/0.64         (~ (zip_tseitin_0 @ X41 @ X42)
% 0.46/0.64          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 0.46/0.64          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.46/0.64        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['31', '34'])).
% 0.46/0.64  thf('36', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['36'])).
% 0.46/0.64  thf(t4_subset_1, axiom,
% 0.46/0.64    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.64         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.46/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.64         ((v4_relat_1 @ X25 @ X26)
% 0.46/0.64          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.64  thf('43', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.46/0.64      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.64  thf(t209_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.64       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X19 : $i, X20 : $i]:
% 0.46/0.64         (((X19) = (k7_relat_1 @ X19 @ X20))
% 0.46/0.64          | ~ (v4_relat_1 @ X19 @ X20)
% 0.46/0.64          | ~ (v1_relat_1 @ X19))),
% 0.46/0.64      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ k1_xboole_0)
% 0.46/0.64          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.64  thf(t113_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i]:
% 0.46/0.64         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['46'])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.64  thf('49', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.64      inference('sup+', [status(thm)], ['47', '48'])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['45', '49'])).
% 0.46/0.64  thf(t87_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (![X21 : $i, X22 : $i]:
% 0.46/0.64         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X21 @ X22)) @ X22)
% 0.46/0.64          | ~ (v1_relat_1 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['50', '51'])).
% 0.46/0.64  thf('53', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.64      inference('sup+', [status(thm)], ['47', '48'])).
% 0.46/0.64  thf('54', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.46/0.64      inference('demod', [status(thm)], ['52', '53'])).
% 0.46/0.64  thf(t34_mcart_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ~( ( r2_hidden @ B @ A ) & 
% 0.46/0.64                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.64                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.46/0.64                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      (![X31 : $i]:
% 0.46/0.64         (((X31) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X31) @ X31))),
% 0.46/0.64      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.46/0.64  thf(t7_ordinal1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (![X23 : $i, X24 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X23 @ X24) | ~ (r1_tarski @ X24 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.64  thf('58', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['54', '57'])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['40', '58'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.46/0.64         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 0.46/0.64          | (v1_funct_2 @ X40 @ X38 @ X39)
% 0.46/0.64          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X1) != (k1_xboole_0))
% 0.46/0.64          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.46/0.64          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.64          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['61'])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      (![X36 : $i, X37 : $i]:
% 0.46/0.64         ((zip_tseitin_0 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.64  thf('64', plain, (![X36 : $i]: (zip_tseitin_0 @ X36 @ k1_xboole_0)),
% 0.46/0.64      inference('simplify', [status(thm)], ['63'])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.64  thf('66', plain,
% 0.46/0.64      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.46/0.64         (~ (zip_tseitin_0 @ X41 @ X42)
% 0.46/0.64          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 0.46/0.64          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.46/0.64      inference('sup-', [status(thm)], ['64', '67'])).
% 0.46/0.64  thf('69', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.64      inference('demod', [status(thm)], ['62', '68'])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      (![X31 : $i]:
% 0.46/0.64         (((X31) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X31) @ X31))),
% 0.46/0.64      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['36'])).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('73', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_D @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['71', '72'])).
% 0.46/0.64  thf(t5_subset, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.46/0.64          ( v1_xboole_0 @ C ) ) ))).
% 0.46/0.64  thf('74', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X10 @ X11)
% 0.46/0.64          | ~ (v1_xboole_0 @ X12)
% 0.46/0.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t5_subset])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      ((![X0 : $i]:
% 0.46/0.64          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 0.46/0.64           | ~ (r2_hidden @ X0 @ sk_D)))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['73', '74'])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['46'])).
% 0.46/0.64  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.64  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.64  thf('78', plain,
% 0.46/0.64      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['70', '78'])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['36'])).
% 0.46/0.64  thf('81', plain,
% 0.46/0.64      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.46/0.64         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.46/0.64         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['80', '81'])).
% 0.46/0.64  thf('83', plain,
% 0.46/0.64      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.46/0.64         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['79', '82'])).
% 0.46/0.64  thf('84', plain,
% 0.46/0.64      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['69', '83'])).
% 0.46/0.64  thf('85', plain,
% 0.46/0.64      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['46'])).
% 0.46/0.64  thf('86', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_D @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['71', '72'])).
% 0.46/0.64  thf('87', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['85', '86'])).
% 0.46/0.64  thf('88', plain,
% 0.46/0.64      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['46'])).
% 0.46/0.64  thf('89', plain,
% 0.46/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['36'])).
% 0.46/0.64  thf('90', plain,
% 0.46/0.64      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.46/0.64         <= (~
% 0.46/0.64             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('91', plain,
% 0.46/0.64      ((~ (m1_subset_1 @ sk_D @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.46/0.64         <= (~
% 0.46/0.64             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.46/0.64             (((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['89', '90'])).
% 0.46/0.64  thf('92', plain,
% 0.46/0.64      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.46/0.64         <= (~
% 0.46/0.64             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.46/0.64             (((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['88', '91'])).
% 0.46/0.64  thf('93', plain,
% 0.46/0.64      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.46/0.64       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['87', '92'])).
% 0.46/0.64  thf('94', plain,
% 0.46/0.64      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.46/0.64       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('95', plain,
% 0.46/0.64      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.46/0.64      inference('split', [status(esa)], ['36'])).
% 0.46/0.64  thf('96', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['4', '84', '93', '94', '95'])).
% 0.46/0.64  thf('97', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['37', '96'])).
% 0.46/0.64  thf('98', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['35', '97'])).
% 0.46/0.64  thf('99', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['30', '98'])).
% 0.46/0.64  thf('100', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['21', '22', '23', '99'])).
% 0.46/0.64  thf('101', plain,
% 0.46/0.64      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.46/0.64         <= (~
% 0.46/0.64             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('102', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['100', '101'])).
% 0.46/0.64  thf('103', plain,
% 0.46/0.64      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.46/0.64       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.46/0.64       ~ ((v1_funct_1 @ sk_D))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('104', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['4', '102', '103'])).
% 0.46/0.64  thf('105', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['1', '104'])).
% 0.46/0.64  thf('106', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '18'])).
% 0.46/0.64  thf('107', plain,
% 0.46/0.64      (![X44 : $i, X45 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k2_relat_1 @ X44) @ X45)
% 0.46/0.64          | (v1_funct_2 @ X44 @ (k1_relat_1 @ X44) @ X45)
% 0.46/0.64          | ~ (v1_funct_1 @ X44)
% 0.46/0.64          | ~ (v1_relat_1 @ X44))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.46/0.64  thf('108', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_D)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_D)
% 0.46/0.64        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['106', '107'])).
% 0.46/0.64  thf('109', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.64      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.64  thf('110', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('111', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['30', '98'])).
% 0.46/0.64  thf('112', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 0.46/0.64  thf('113', plain, ($false), inference('demod', [status(thm)], ['105', '112'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
