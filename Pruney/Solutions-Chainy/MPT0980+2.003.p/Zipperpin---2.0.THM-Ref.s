%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.syMdTcW7q0

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:54 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 791 expanded)
%              Number of leaves         :   37 ( 231 expanded)
%              Depth                    :   21
%              Number of atoms          : 1466 (14414 expanded)
%              Number of equality atoms :  146 ( 950 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t26_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
             => ( ( ( C = k1_xboole_0 )
                  & ( B != k1_xboole_0 ) )
                | ( v2_funct_1 @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_funct_2])).

thf('0',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v5_relat_1 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('5',plain,
    ( ( v5_relat_1 @ sk_D @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_funct_2 @ sk_E @ k1_xboole_0 @ sk_C )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ( X16
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('25',plain,(
    ! [X14: $i] :
      ( zip_tseitin_0 @ X14 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','25'])).

thf('27',plain,
    ( ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E )
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','26','29'])).

thf(t47_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) )
           => ( v2_funct_1 @ B ) ) ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v2_funct_1 @ X6 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X6 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_E )
        | ~ ( v1_funct_1 @ sk_E )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','37','38'])).

thf('40',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['10','11'])).

thf('42',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_funct_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('48',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 != k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X20 @ k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('56',plain,
    ( ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('57',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('58',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( sk_D = k1_xboole_0 )
        | ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0 )
          = ( k5_relat_1 @ sk_D @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ sk_D ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( sk_D = k1_xboole_0 )
        | ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0 )
          = ( k5_relat_1 @ sk_D @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ~ ( v1_funct_1 @ sk_E )
      | ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E )
        = ( k5_relat_1 @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E )
        = ( k5_relat_1 @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('66',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,(
    v2_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( v2_funct_1 @ ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,
    ( ( ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','71'])).

thf('73',plain,
    ( ( ( sk_D = k1_xboole_0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('75',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ k1_xboole_0 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','75'])).

thf('77',plain,(
    v2_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['77','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v5_relat_1 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('90',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['10','11'])).

thf('94',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('96',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('97',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('101',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_C = X1 )
      | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ( X16
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('108',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('111',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['108','111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_B
          = ( k1_relat_1 @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','112'])).

thf('114',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_B
          = ( k1_relat_1 @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['95','113'])).

thf('115',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B
          = ( k1_relat_1 @ sk_E ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['114'])).

thf('116',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('117',plain,
    ( ( ( sk_B
        = ( k1_relat_1 @ sk_E ) )
      | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['108','111'])).

thf('119',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v2_funct_1 @ X6 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X6 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('121',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B )
        | ~ ( v1_relat_1 @ sk_E )
        | ~ ( v1_funct_1 @ sk_E )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['35','36'])).

thf('123',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['10','11'])).

thf('127',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ~ ( v2_funct_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['87','130'])).

thf('132',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('133',plain,(
    sk_B = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_funct_1 @ ( k5_relat_1 @ k1_xboole_0 @ sk_E ) ) ),
    inference(simpl_trail,[status(thm)],['76','133'])).

thf('135',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['77','86'])).

thf('136',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('137',plain,(
    sk_B = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['131','132'])).

thf('138',plain,(
    sk_D = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['136','137'])).

thf('139',plain,(
    v2_funct_1 @ ( k5_relat_1 @ k1_xboole_0 @ sk_E ) ),
    inference(demod,[status(thm)],['135','138'])).

thf('140',plain,(
    $false ),
    inference(demod,[status(thm)],['134','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.syMdTcW7q0
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:28:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.37/1.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.37/1.56  % Solved by: fo/fo7.sh
% 1.37/1.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.56  % done 1216 iterations in 1.090s
% 1.37/1.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.37/1.56  % SZS output start Refutation
% 1.37/1.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.37/1.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.37/1.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.37/1.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.37/1.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.37/1.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.37/1.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.37/1.56  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.37/1.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.37/1.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.37/1.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.37/1.56  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.56  thf(sk_E_type, type, sk_E: $i).
% 1.37/1.56  thf(sk_D_type, type, sk_D: $i).
% 1.37/1.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.37/1.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.37/1.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.37/1.56  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.37/1.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.37/1.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.37/1.56  thf(sk_C_type, type, sk_C: $i).
% 1.37/1.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.37/1.56  thf(t26_funct_2, conjecture,
% 1.37/1.56    (![A:$i,B:$i,C:$i,D:$i]:
% 1.37/1.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.37/1.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.37/1.56       ( ![E:$i]:
% 1.37/1.56         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.37/1.56             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.37/1.56           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.37/1.56             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.37/1.56               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 1.37/1.56  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.37/1.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.37/1.56            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.37/1.56          ( ![E:$i]:
% 1.37/1.56            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.37/1.56                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.37/1.56              ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.37/1.56                ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.37/1.56                  ( v2_funct_1 @ D ) ) ) ) ) ) )),
% 1.37/1.56    inference('cnf.neg', [status(esa)], [t26_funct_2])).
% 1.37/1.56  thf('0', plain, ((((sk_C) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('1', plain, ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('split', [status(esa)], ['0'])).
% 1.37/1.56  thf('2', plain,
% 1.37/1.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('3', plain,
% 1.37/1.56      (((m1_subset_1 @ sk_D @ 
% 1.37/1.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup+', [status(thm)], ['1', '2'])).
% 1.37/1.56  thf(cc2_relset_1, axiom,
% 1.37/1.56    (![A:$i,B:$i,C:$i]:
% 1.37/1.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.37/1.56  thf('4', plain,
% 1.37/1.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.37/1.56         ((v5_relat_1 @ X8 @ X10)
% 1.37/1.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.37/1.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.37/1.56  thf('5', plain,
% 1.37/1.56      (((v5_relat_1 @ sk_D @ k1_xboole_0)) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup-', [status(thm)], ['3', '4'])).
% 1.37/1.56  thf(d19_relat_1, axiom,
% 1.37/1.56    (![A:$i,B:$i]:
% 1.37/1.56     ( ( v1_relat_1 @ B ) =>
% 1.37/1.56       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.37/1.56  thf('6', plain,
% 1.37/1.56      (![X2 : $i, X3 : $i]:
% 1.37/1.56         (~ (v5_relat_1 @ X2 @ X3)
% 1.37/1.56          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 1.37/1.56          | ~ (v1_relat_1 @ X2))),
% 1.37/1.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.37/1.56  thf('7', plain,
% 1.37/1.56      (((~ (v1_relat_1 @ sk_D)
% 1.37/1.56         | (r1_tarski @ (k2_relat_1 @ sk_D) @ k1_xboole_0)))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup-', [status(thm)], ['5', '6'])).
% 1.37/1.56  thf('8', plain,
% 1.37/1.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf(cc2_relat_1, axiom,
% 1.37/1.56    (![A:$i]:
% 1.37/1.56     ( ( v1_relat_1 @ A ) =>
% 1.37/1.56       ( ![B:$i]:
% 1.37/1.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.37/1.56  thf('9', plain,
% 1.37/1.56      (![X0 : $i, X1 : $i]:
% 1.37/1.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.37/1.56          | (v1_relat_1 @ X0)
% 1.37/1.56          | ~ (v1_relat_1 @ X1))),
% 1.37/1.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.37/1.56  thf('10', plain,
% 1.37/1.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 1.37/1.56      inference('sup-', [status(thm)], ['8', '9'])).
% 1.37/1.56  thf(fc6_relat_1, axiom,
% 1.37/1.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.37/1.56  thf('11', plain,
% 1.37/1.56      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.37/1.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.37/1.56  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 1.37/1.56      inference('demod', [status(thm)], ['10', '11'])).
% 1.37/1.56  thf('13', plain,
% 1.37/1.56      (((r1_tarski @ (k2_relat_1 @ sk_D) @ k1_xboole_0))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('demod', [status(thm)], ['7', '12'])).
% 1.37/1.56  thf('14', plain,
% 1.37/1.56      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('split', [status(esa)], ['0'])).
% 1.37/1.56  thf('15', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('16', plain,
% 1.37/1.56      (((v1_funct_2 @ sk_E @ k1_xboole_0 @ sk_C))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup+', [status(thm)], ['14', '15'])).
% 1.37/1.56  thf(d1_funct_2, axiom,
% 1.37/1.56    (![A:$i,B:$i,C:$i]:
% 1.37/1.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.37/1.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.37/1.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.37/1.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.37/1.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.37/1.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.37/1.56  thf(zf_stmt_1, axiom,
% 1.37/1.56    (![C:$i,B:$i,A:$i]:
% 1.37/1.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.37/1.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.37/1.56  thf('17', plain,
% 1.37/1.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.37/1.56         (~ (v1_funct_2 @ X18 @ X16 @ X17)
% 1.37/1.56          | ((X16) = (k1_relset_1 @ X16 @ X17 @ X18))
% 1.37/1.56          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.37/1.56  thf('18', plain,
% 1.37/1.56      (((~ (zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0)
% 1.37/1.56         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E))))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup-', [status(thm)], ['16', '17'])).
% 1.37/1.56  thf('19', plain,
% 1.37/1.56      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('split', [status(esa)], ['0'])).
% 1.37/1.56  thf('20', plain,
% 1.37/1.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('21', plain,
% 1.37/1.56      (((m1_subset_1 @ sk_E @ 
% 1.37/1.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup+', [status(thm)], ['19', '20'])).
% 1.37/1.56  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.37/1.56  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.37/1.56  thf(zf_stmt_4, axiom,
% 1.37/1.56    (![B:$i,A:$i]:
% 1.37/1.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.37/1.56       ( zip_tseitin_0 @ B @ A ) ))).
% 1.37/1.56  thf(zf_stmt_5, axiom,
% 1.37/1.56    (![A:$i,B:$i,C:$i]:
% 1.37/1.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.37/1.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.37/1.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.37/1.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.37/1.56  thf('22', plain,
% 1.37/1.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.37/1.56         (~ (zip_tseitin_0 @ X19 @ X20)
% 1.37/1.56          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 1.37/1.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.37/1.56  thf('23', plain,
% 1.37/1.56      ((((zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0)
% 1.37/1.56         | ~ (zip_tseitin_0 @ sk_C @ k1_xboole_0)))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup-', [status(thm)], ['21', '22'])).
% 1.37/1.56  thf('24', plain,
% 1.37/1.56      (![X14 : $i, X15 : $i]:
% 1.37/1.56         ((zip_tseitin_0 @ X14 @ X15) | ((X15) != (k1_xboole_0)))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.37/1.56  thf('25', plain, (![X14 : $i]: (zip_tseitin_0 @ X14 @ k1_xboole_0)),
% 1.37/1.56      inference('simplify', [status(thm)], ['24'])).
% 1.37/1.56  thf('26', plain,
% 1.37/1.56      (((zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('demod', [status(thm)], ['23', '25'])).
% 1.37/1.56  thf('27', plain,
% 1.37/1.56      (((m1_subset_1 @ sk_E @ 
% 1.37/1.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup+', [status(thm)], ['19', '20'])).
% 1.37/1.56  thf(redefinition_k1_relset_1, axiom,
% 1.37/1.56    (![A:$i,B:$i,C:$i]:
% 1.37/1.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.37/1.56  thf('28', plain,
% 1.37/1.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.37/1.56         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 1.37/1.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.37/1.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.37/1.56  thf('29', plain,
% 1.37/1.56      ((((k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E) = (k1_relat_1 @ sk_E)))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup-', [status(thm)], ['27', '28'])).
% 1.37/1.56  thf('30', plain,
% 1.37/1.56      ((((k1_xboole_0) = (k1_relat_1 @ sk_E))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('demod', [status(thm)], ['18', '26', '29'])).
% 1.37/1.56  thf(t47_funct_1, axiom,
% 1.37/1.56    (![A:$i]:
% 1.37/1.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.37/1.56       ( ![B:$i]:
% 1.37/1.56         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.37/1.56           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.37/1.56               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 1.37/1.56             ( v2_funct_1 @ B ) ) ) ) ))).
% 1.37/1.56  thf('31', plain,
% 1.37/1.56      (![X6 : $i, X7 : $i]:
% 1.37/1.56         (~ (v1_relat_1 @ X6)
% 1.37/1.56          | ~ (v1_funct_1 @ X6)
% 1.37/1.56          | (v2_funct_1 @ X6)
% 1.37/1.56          | ~ (r1_tarski @ (k2_relat_1 @ X6) @ (k1_relat_1 @ X7))
% 1.37/1.56          | ~ (v2_funct_1 @ (k5_relat_1 @ X6 @ X7))
% 1.37/1.56          | ~ (v1_funct_1 @ X7)
% 1.37/1.56          | ~ (v1_relat_1 @ X7))),
% 1.37/1.56      inference('cnf', [status(esa)], [t47_funct_1])).
% 1.37/1.56  thf('32', plain,
% 1.37/1.56      ((![X0 : $i]:
% 1.37/1.56          (~ (r1_tarski @ (k2_relat_1 @ X0) @ k1_xboole_0)
% 1.37/1.56           | ~ (v1_relat_1 @ sk_E)
% 1.37/1.56           | ~ (v1_funct_1 @ sk_E)
% 1.37/1.56           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.37/1.56           | (v2_funct_1 @ X0)
% 1.37/1.56           | ~ (v1_funct_1 @ X0)
% 1.37/1.56           | ~ (v1_relat_1 @ X0)))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup-', [status(thm)], ['30', '31'])).
% 1.37/1.56  thf('33', plain,
% 1.37/1.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('34', plain,
% 1.37/1.56      (![X0 : $i, X1 : $i]:
% 1.37/1.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.37/1.56          | (v1_relat_1 @ X0)
% 1.37/1.56          | ~ (v1_relat_1 @ X1))),
% 1.37/1.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.37/1.56  thf('35', plain,
% 1.37/1.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 1.37/1.56      inference('sup-', [status(thm)], ['33', '34'])).
% 1.37/1.56  thf('36', plain,
% 1.37/1.56      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.37/1.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.37/1.56  thf('37', plain, ((v1_relat_1 @ sk_E)),
% 1.37/1.56      inference('demod', [status(thm)], ['35', '36'])).
% 1.37/1.56  thf('38', plain, ((v1_funct_1 @ sk_E)),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('39', plain,
% 1.37/1.56      ((![X0 : $i]:
% 1.37/1.56          (~ (r1_tarski @ (k2_relat_1 @ X0) @ k1_xboole_0)
% 1.37/1.56           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.37/1.56           | (v2_funct_1 @ X0)
% 1.37/1.56           | ~ (v1_funct_1 @ X0)
% 1.37/1.56           | ~ (v1_relat_1 @ X0)))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('demod', [status(thm)], ['32', '37', '38'])).
% 1.37/1.56  thf('40', plain,
% 1.37/1.56      (((~ (v1_relat_1 @ sk_D)
% 1.37/1.56         | ~ (v1_funct_1 @ sk_D)
% 1.37/1.56         | (v2_funct_1 @ sk_D)
% 1.37/1.56         | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup-', [status(thm)], ['13', '39'])).
% 1.37/1.56  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 1.37/1.56      inference('demod', [status(thm)], ['10', '11'])).
% 1.37/1.56  thf('42', plain, ((v1_funct_1 @ sk_D)),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('43', plain,
% 1.37/1.56      ((((v2_funct_1 @ sk_D) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.37/1.56  thf('44', plain, (~ (v2_funct_1 @ sk_D)),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('45', plain,
% 1.37/1.56      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('clc', [status(thm)], ['43', '44'])).
% 1.37/1.56  thf('46', plain,
% 1.37/1.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('47', plain,
% 1.37/1.56      (((m1_subset_1 @ sk_D @ 
% 1.37/1.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup+', [status(thm)], ['1', '2'])).
% 1.37/1.56  thf('48', plain,
% 1.37/1.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.37/1.56         (((X19) != (k1_xboole_0))
% 1.37/1.56          | ((X20) = (k1_xboole_0))
% 1.37/1.56          | ((X21) = (k1_xboole_0))
% 1.37/1.56          | ~ (v1_funct_2 @ X21 @ X20 @ X19)
% 1.37/1.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.37/1.56  thf('49', plain,
% 1.37/1.56      (![X20 : $i, X21 : $i]:
% 1.37/1.56         (~ (m1_subset_1 @ X21 @ 
% 1.37/1.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ k1_xboole_0)))
% 1.37/1.56          | ~ (v1_funct_2 @ X21 @ X20 @ k1_xboole_0)
% 1.37/1.56          | ((X21) = (k1_xboole_0))
% 1.37/1.56          | ((X20) = (k1_xboole_0)))),
% 1.37/1.56      inference('simplify', [status(thm)], ['48'])).
% 1.37/1.56  thf('50', plain,
% 1.37/1.56      (((((sk_A) = (k1_xboole_0))
% 1.37/1.56         | ((sk_D) = (k1_xboole_0))
% 1.37/1.56         | ~ (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0)))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup-', [status(thm)], ['47', '49'])).
% 1.37/1.56  thf('51', plain,
% 1.37/1.56      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('split', [status(esa)], ['0'])).
% 1.37/1.56  thf('52', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('53', plain,
% 1.37/1.56      (((v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup+', [status(thm)], ['51', '52'])).
% 1.37/1.56  thf('54', plain,
% 1.37/1.56      (((((sk_A) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0))))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('demod', [status(thm)], ['50', '53'])).
% 1.37/1.56  thf('55', plain,
% 1.37/1.56      (((m1_subset_1 @ sk_D @ 
% 1.37/1.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup+', [status(thm)], ['1', '2'])).
% 1.37/1.56  thf('56', plain,
% 1.37/1.56      ((((m1_subset_1 @ sk_D @ 
% 1.37/1.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))
% 1.37/1.56         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup+', [status(thm)], ['54', '55'])).
% 1.37/1.56  thf(redefinition_k1_partfun1, axiom,
% 1.37/1.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.37/1.56     ( ( ( v1_funct_1 @ E ) & 
% 1.37/1.56         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.37/1.56         ( v1_funct_1 @ F ) & 
% 1.37/1.56         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.37/1.56       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.37/1.56  thf('57', plain,
% 1.37/1.56      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.37/1.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.37/1.56          | ~ (v1_funct_1 @ X22)
% 1.37/1.56          | ~ (v1_funct_1 @ X25)
% 1.37/1.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.37/1.56          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 1.37/1.56              = (k5_relat_1 @ X22 @ X25)))),
% 1.37/1.56      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.37/1.56  thf('58', plain,
% 1.37/1.56      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.56          (((sk_D) = (k1_xboole_0))
% 1.37/1.56           | ((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0)
% 1.37/1.56               = (k5_relat_1 @ sk_D @ X0))
% 1.37/1.56           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.37/1.56           | ~ (v1_funct_1 @ X0)
% 1.37/1.56           | ~ (v1_funct_1 @ sk_D)))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup-', [status(thm)], ['56', '57'])).
% 1.37/1.56  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('60', plain,
% 1.37/1.56      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.56          (((sk_D) = (k1_xboole_0))
% 1.37/1.56           | ((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0)
% 1.37/1.56               = (k5_relat_1 @ sk_D @ X0))
% 1.37/1.56           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.37/1.56           | ~ (v1_funct_1 @ X0)))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('demod', [status(thm)], ['58', '59'])).
% 1.37/1.56  thf('61', plain,
% 1.37/1.56      (((~ (v1_funct_1 @ sk_E)
% 1.37/1.56         | ((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ 
% 1.37/1.56             sk_E) = (k5_relat_1 @ sk_D @ sk_E))
% 1.37/1.56         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup-', [status(thm)], ['46', '60'])).
% 1.37/1.56  thf('62', plain, ((v1_funct_1 @ sk_E)),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('63', plain,
% 1.37/1.56      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('split', [status(esa)], ['0'])).
% 1.37/1.56  thf('64', plain,
% 1.37/1.56      (((((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ 
% 1.37/1.56           sk_D @ sk_E) = (k5_relat_1 @ sk_D @ sk_E))
% 1.37/1.56         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.37/1.56  thf('65', plain,
% 1.37/1.56      (((((sk_A) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0))))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('demod', [status(thm)], ['50', '53'])).
% 1.37/1.56  thf('66', plain,
% 1.37/1.56      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('split', [status(esa)], ['0'])).
% 1.37/1.56  thf('67', plain,
% 1.37/1.56      ((v2_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('68', plain,
% 1.37/1.56      (((v2_funct_1 @ 
% 1.37/1.56         (k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E)))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup+', [status(thm)], ['66', '67'])).
% 1.37/1.56  thf('69', plain,
% 1.37/1.56      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('split', [status(esa)], ['0'])).
% 1.37/1.56  thf('70', plain,
% 1.37/1.56      (((v2_funct_1 @ 
% 1.37/1.56         (k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E)))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('demod', [status(thm)], ['68', '69'])).
% 1.37/1.56  thf('71', plain,
% 1.37/1.56      ((((v2_funct_1 @ 
% 1.37/1.56          (k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ 
% 1.37/1.56           sk_D @ sk_E))
% 1.37/1.56         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup+', [status(thm)], ['65', '70'])).
% 1.37/1.56  thf('72', plain,
% 1.37/1.56      ((((v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))
% 1.37/1.56         | ((sk_D) = (k1_xboole_0))
% 1.37/1.56         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup+', [status(thm)], ['64', '71'])).
% 1.37/1.56  thf('73', plain,
% 1.37/1.56      (((((sk_D) = (k1_xboole_0)) | (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('simplify', [status(thm)], ['72'])).
% 1.37/1.56  thf('74', plain,
% 1.37/1.56      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('clc', [status(thm)], ['43', '44'])).
% 1.37/1.56  thf('75', plain,
% 1.37/1.56      ((((sk_D) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('clc', [status(thm)], ['73', '74'])).
% 1.37/1.56  thf('76', plain,
% 1.37/1.56      ((~ (v2_funct_1 @ (k5_relat_1 @ k1_xboole_0 @ sk_E)))
% 1.37/1.56         <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('demod', [status(thm)], ['45', '75'])).
% 1.37/1.56  thf('77', plain,
% 1.37/1.56      ((v2_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('78', plain,
% 1.37/1.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('79', plain,
% 1.37/1.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('80', plain,
% 1.37/1.56      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.37/1.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.37/1.56          | ~ (v1_funct_1 @ X22)
% 1.37/1.56          | ~ (v1_funct_1 @ X25)
% 1.37/1.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.37/1.56          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 1.37/1.56              = (k5_relat_1 @ X22 @ X25)))),
% 1.37/1.56      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.37/1.56  thf('81', plain,
% 1.37/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.56         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.37/1.56            = (k5_relat_1 @ sk_D @ X0))
% 1.37/1.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.37/1.56          | ~ (v1_funct_1 @ X0)
% 1.37/1.56          | ~ (v1_funct_1 @ sk_D))),
% 1.37/1.56      inference('sup-', [status(thm)], ['79', '80'])).
% 1.37/1.56  thf('82', plain, ((v1_funct_1 @ sk_D)),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('83', plain,
% 1.37/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.56         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.37/1.56            = (k5_relat_1 @ sk_D @ X0))
% 1.37/1.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.37/1.56          | ~ (v1_funct_1 @ X0))),
% 1.37/1.56      inference('demod', [status(thm)], ['81', '82'])).
% 1.37/1.56  thf('84', plain,
% 1.37/1.56      ((~ (v1_funct_1 @ sk_E)
% 1.37/1.56        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.37/1.56            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.37/1.56      inference('sup-', [status(thm)], ['78', '83'])).
% 1.37/1.56  thf('85', plain, ((v1_funct_1 @ sk_E)),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('86', plain,
% 1.37/1.56      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.37/1.56         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.37/1.56      inference('demod', [status(thm)], ['84', '85'])).
% 1.37/1.56  thf('87', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 1.37/1.56      inference('demod', [status(thm)], ['77', '86'])).
% 1.37/1.56  thf('88', plain,
% 1.37/1.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('89', plain,
% 1.37/1.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.37/1.56         ((v5_relat_1 @ X8 @ X10)
% 1.37/1.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.37/1.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.37/1.56  thf('90', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 1.37/1.56      inference('sup-', [status(thm)], ['88', '89'])).
% 1.37/1.56  thf('91', plain,
% 1.37/1.56      (![X2 : $i, X3 : $i]:
% 1.37/1.56         (~ (v5_relat_1 @ X2 @ X3)
% 1.37/1.56          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 1.37/1.56          | ~ (v1_relat_1 @ X2))),
% 1.37/1.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.37/1.56  thf('92', plain,
% 1.37/1.56      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 1.37/1.56      inference('sup-', [status(thm)], ['90', '91'])).
% 1.37/1.56  thf('93', plain, ((v1_relat_1 @ sk_D)),
% 1.37/1.56      inference('demod', [status(thm)], ['10', '11'])).
% 1.37/1.56  thf('94', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 1.37/1.56      inference('demod', [status(thm)], ['92', '93'])).
% 1.37/1.56  thf('95', plain,
% 1.37/1.56      (![X14 : $i, X15 : $i]:
% 1.37/1.56         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.37/1.56  thf('96', plain,
% 1.37/1.56      (![X14 : $i, X15 : $i]:
% 1.37/1.56         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.37/1.56  thf('97', plain,
% 1.37/1.56      (![X14 : $i, X15 : $i]:
% 1.37/1.56         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.37/1.56  thf('98', plain,
% 1.37/1.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.37/1.56         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 1.37/1.56      inference('sup+', [status(thm)], ['96', '97'])).
% 1.37/1.56  thf('99', plain,
% 1.37/1.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('100', plain,
% 1.37/1.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.37/1.56         (~ (zip_tseitin_0 @ X19 @ X20)
% 1.37/1.56          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 1.37/1.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.37/1.56  thf('101', plain,
% 1.37/1.56      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.37/1.56      inference('sup-', [status(thm)], ['99', '100'])).
% 1.37/1.56  thf('102', plain,
% 1.37/1.56      (![X0 : $i, X1 : $i]:
% 1.37/1.56         ((zip_tseitin_0 @ X1 @ X0)
% 1.37/1.56          | ((sk_C) = (X1))
% 1.37/1.56          | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.37/1.56      inference('sup-', [status(thm)], ['98', '101'])).
% 1.37/1.56  thf('103', plain,
% 1.37/1.56      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.37/1.56      inference('split', [status(esa)], ['0'])).
% 1.37/1.56  thf('104', plain,
% 1.37/1.56      ((![X0 : $i, X1 : $i]:
% 1.37/1.56          (((X0) != (k1_xboole_0))
% 1.37/1.56           | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.37/1.56           | (zip_tseitin_0 @ X0 @ X1)))
% 1.37/1.56         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup-', [status(thm)], ['102', '103'])).
% 1.37/1.56  thf('105', plain,
% 1.37/1.56      ((![X1 : $i]:
% 1.37/1.56          ((zip_tseitin_0 @ k1_xboole_0 @ X1)
% 1.37/1.56           | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)))
% 1.37/1.56         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.37/1.56      inference('simplify', [status(thm)], ['104'])).
% 1.37/1.56  thf('106', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('107', plain,
% 1.37/1.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.37/1.56         (~ (v1_funct_2 @ X18 @ X16 @ X17)
% 1.37/1.56          | ((X16) = (k1_relset_1 @ X16 @ X17 @ X18))
% 1.37/1.56          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.37/1.56  thf('108', plain,
% 1.37/1.56      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.37/1.56        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.37/1.56      inference('sup-', [status(thm)], ['106', '107'])).
% 1.37/1.56  thf('109', plain,
% 1.37/1.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('110', plain,
% 1.37/1.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.37/1.56         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 1.37/1.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.37/1.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.37/1.56  thf('111', plain,
% 1.37/1.56      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.37/1.56      inference('sup-', [status(thm)], ['109', '110'])).
% 1.37/1.56  thf('112', plain,
% 1.37/1.56      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_E)))),
% 1.37/1.56      inference('demod', [status(thm)], ['108', '111'])).
% 1.37/1.56  thf('113', plain,
% 1.37/1.56      ((![X0 : $i]:
% 1.37/1.56          ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_B) = (k1_relat_1 @ sk_E))))
% 1.37/1.56         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup-', [status(thm)], ['105', '112'])).
% 1.37/1.56  thf('114', plain,
% 1.37/1.56      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.56          ((zip_tseitin_0 @ X0 @ X1)
% 1.37/1.56           | (zip_tseitin_0 @ X0 @ X2)
% 1.37/1.56           | ((sk_B) = (k1_relat_1 @ sk_E))))
% 1.37/1.56         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup+', [status(thm)], ['95', '113'])).
% 1.37/1.56  thf('115', plain,
% 1.37/1.56      ((![X0 : $i, X1 : $i]:
% 1.37/1.56          (((sk_B) = (k1_relat_1 @ sk_E)) | (zip_tseitin_0 @ X1 @ X0)))
% 1.37/1.56         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.37/1.56      inference('condensation', [status(thm)], ['114'])).
% 1.37/1.56  thf('116', plain,
% 1.37/1.56      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.37/1.56      inference('sup-', [status(thm)], ['99', '100'])).
% 1.37/1.56  thf('117', plain,
% 1.37/1.56      (((((sk_B) = (k1_relat_1 @ sk_E)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)))
% 1.37/1.56         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup-', [status(thm)], ['115', '116'])).
% 1.37/1.56  thf('118', plain,
% 1.37/1.56      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_E)))),
% 1.37/1.56      inference('demod', [status(thm)], ['108', '111'])).
% 1.37/1.56  thf('119', plain,
% 1.37/1.56      ((((sk_B) = (k1_relat_1 @ sk_E))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.37/1.56      inference('clc', [status(thm)], ['117', '118'])).
% 1.37/1.56  thf('120', plain,
% 1.37/1.56      (![X6 : $i, X7 : $i]:
% 1.37/1.56         (~ (v1_relat_1 @ X6)
% 1.37/1.56          | ~ (v1_funct_1 @ X6)
% 1.37/1.56          | (v2_funct_1 @ X6)
% 1.37/1.56          | ~ (r1_tarski @ (k2_relat_1 @ X6) @ (k1_relat_1 @ X7))
% 1.37/1.56          | ~ (v2_funct_1 @ (k5_relat_1 @ X6 @ X7))
% 1.37/1.56          | ~ (v1_funct_1 @ X7)
% 1.37/1.56          | ~ (v1_relat_1 @ X7))),
% 1.37/1.56      inference('cnf', [status(esa)], [t47_funct_1])).
% 1.37/1.56  thf('121', plain,
% 1.37/1.56      ((![X0 : $i]:
% 1.37/1.56          (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B)
% 1.37/1.56           | ~ (v1_relat_1 @ sk_E)
% 1.37/1.56           | ~ (v1_funct_1 @ sk_E)
% 1.37/1.56           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.37/1.56           | (v2_funct_1 @ X0)
% 1.37/1.56           | ~ (v1_funct_1 @ X0)
% 1.37/1.56           | ~ (v1_relat_1 @ X0)))
% 1.37/1.56         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup-', [status(thm)], ['119', '120'])).
% 1.37/1.56  thf('122', plain, ((v1_relat_1 @ sk_E)),
% 1.37/1.56      inference('demod', [status(thm)], ['35', '36'])).
% 1.37/1.56  thf('123', plain, ((v1_funct_1 @ sk_E)),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('124', plain,
% 1.37/1.56      ((![X0 : $i]:
% 1.37/1.56          (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B)
% 1.37/1.56           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.37/1.56           | (v2_funct_1 @ X0)
% 1.37/1.56           | ~ (v1_funct_1 @ X0)
% 1.37/1.56           | ~ (v1_relat_1 @ X0)))
% 1.37/1.56         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.37/1.56      inference('demod', [status(thm)], ['121', '122', '123'])).
% 1.37/1.56  thf('125', plain,
% 1.37/1.56      (((~ (v1_relat_1 @ sk_D)
% 1.37/1.56         | ~ (v1_funct_1 @ sk_D)
% 1.37/1.56         | (v2_funct_1 @ sk_D)
% 1.37/1.56         | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.37/1.56         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.37/1.56      inference('sup-', [status(thm)], ['94', '124'])).
% 1.37/1.56  thf('126', plain, ((v1_relat_1 @ sk_D)),
% 1.37/1.56      inference('demod', [status(thm)], ['10', '11'])).
% 1.37/1.56  thf('127', plain, ((v1_funct_1 @ sk_D)),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('128', plain,
% 1.37/1.56      ((((v2_funct_1 @ sk_D) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.37/1.56         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.37/1.56      inference('demod', [status(thm)], ['125', '126', '127'])).
% 1.37/1.56  thf('129', plain, (~ (v2_funct_1 @ sk_D)),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('130', plain,
% 1.37/1.56      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 1.37/1.56         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.37/1.56      inference('clc', [status(thm)], ['128', '129'])).
% 1.37/1.56  thf('131', plain, ((((sk_C) = (k1_xboole_0)))),
% 1.37/1.56      inference('sup-', [status(thm)], ['87', '130'])).
% 1.37/1.56  thf('132', plain,
% 1.37/1.56      ((((sk_B) = (k1_xboole_0))) | ~ (((sk_C) = (k1_xboole_0)))),
% 1.37/1.56      inference('split', [status(esa)], ['0'])).
% 1.37/1.56  thf('133', plain, ((((sk_B) = (k1_xboole_0)))),
% 1.37/1.56      inference('sat_resolution*', [status(thm)], ['131', '132'])).
% 1.37/1.56  thf('134', plain, (~ (v2_funct_1 @ (k5_relat_1 @ k1_xboole_0 @ sk_E))),
% 1.37/1.56      inference('simpl_trail', [status(thm)], ['76', '133'])).
% 1.37/1.56  thf('135', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 1.37/1.56      inference('demod', [status(thm)], ['77', '86'])).
% 1.37/1.56  thf('136', plain,
% 1.37/1.56      ((((sk_D) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.37/1.56      inference('clc', [status(thm)], ['73', '74'])).
% 1.37/1.56  thf('137', plain, ((((sk_B) = (k1_xboole_0)))),
% 1.37/1.56      inference('sat_resolution*', [status(thm)], ['131', '132'])).
% 1.37/1.56  thf('138', plain, (((sk_D) = (k1_xboole_0))),
% 1.37/1.56      inference('simpl_trail', [status(thm)], ['136', '137'])).
% 1.37/1.56  thf('139', plain, ((v2_funct_1 @ (k5_relat_1 @ k1_xboole_0 @ sk_E))),
% 1.37/1.56      inference('demod', [status(thm)], ['135', '138'])).
% 1.37/1.56  thf('140', plain, ($false), inference('demod', [status(thm)], ['134', '139'])).
% 1.37/1.56  
% 1.37/1.56  % SZS output end Refutation
% 1.37/1.56  
% 1.37/1.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
