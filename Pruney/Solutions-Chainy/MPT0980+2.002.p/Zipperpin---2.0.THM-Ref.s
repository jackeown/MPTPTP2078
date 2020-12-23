%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H3uNYuePCC

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:54 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 763 expanded)
%              Number of leaves         :   36 ( 218 expanded)
%              Depth                    :   21
%              Number of atoms          : 1531 (14649 expanded)
%              Number of equality atoms :  155 (1001 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,
    ( ( r1_tarski @ ( k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D ) @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('10',plain,
    ( ( ( k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D )
      = ( k2_relat_1 @ sk_D ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v1_funct_2 @ sk_E @ k1_xboole_0 @ sk_C )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

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

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('21',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E )
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,
    ( ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

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

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('27',plain,(
    ! [X17: $i] :
      ( zip_tseitin_0 @ X17 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','27'])).

thf('29',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','28'])).

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

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_funct_1 @ X3 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_E )
        | ~ ( v1_funct_1 @ sk_E )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','34','35'])).

thf('37',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','40','41'])).

thf('43',plain,(
    ~ ( v2_funct_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('47',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X24 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X23 @ k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('55',plain,
    ( ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('56',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('57',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( sk_D = k1_xboole_0 )
        | ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0 )
          = ( k5_relat_1 @ sk_D @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ sk_D ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( sk_D = k1_xboole_0 )
        | ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0 )
          = ( k5_relat_1 @ sk_D @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ~ ( v1_funct_1 @ sk_E )
      | ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E )
        = ( k5_relat_1 @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ( ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E )
        = ( k5_relat_1 @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('65',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,(
    v2_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('69',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( v2_funct_1 @ ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','70'])).

thf('72',plain,
    ( ( ( sk_D = k1_xboole_0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('74',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ k1_xboole_0 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','74'])).

thf('76',plain,(
    v2_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['76','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('89',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('94',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('97',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('98',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('102',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_C = X1 )
      | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('105',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('109',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('112',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['109','112'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_B
          = ( k1_relat_1 @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','113'])).

thf('115',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_B
          = ( k1_relat_1 @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','114'])).

thf('116',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B
          = ( k1_relat_1 @ sk_E ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['115'])).

thf('117',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('118',plain,
    ( ( ( sk_B
        = ( k1_relat_1 @ sk_E ) )
      | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['109','112'])).

thf('120',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_funct_1 @ X3 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B )
        | ~ ( v1_relat_1 @ sk_E )
        | ~ ( v1_funct_1 @ sk_E )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['32','33'])).

thf('124',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['38','39'])).

thf('128',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,(
    ~ ( v2_funct_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','131'])).

thf('133',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('134',plain,(
    sk_B = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_funct_1 @ ( k5_relat_1 @ k1_xboole_0 @ sk_E ) ) ),
    inference(simpl_trail,[status(thm)],['75','134'])).

thf('136',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['76','85'])).

thf('137',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('138',plain,(
    sk_B = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['132','133'])).

thf('139',plain,(
    sk_D = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['137','138'])).

thf('140',plain,(
    v2_funct_1 @ ( k5_relat_1 @ k1_xboole_0 @ sk_E ) ),
    inference(demod,[status(thm)],['136','139'])).

thf('141',plain,(
    $false ),
    inference(demod,[status(thm)],['135','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H3uNYuePCC
% 0.15/0.39  % Computer   : n007.cluster.edu
% 0.15/0.39  % Model      : x86_64 x86_64
% 0.15/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.39  % Memory     : 8042.1875MB
% 0.15/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.39  % CPULimit   : 60
% 0.15/0.39  % DateTime   : Tue Dec  1 10:49:36 EST 2020
% 0.15/0.39  % CPUTime    : 
% 0.15/0.39  % Running portfolio for 600 s
% 0.15/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 1.45/1.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.45/1.63  % Solved by: fo/fo7.sh
% 1.45/1.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.45/1.63  % done 1274 iterations in 1.134s
% 1.45/1.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.45/1.63  % SZS output start Refutation
% 1.45/1.63  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.45/1.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.45/1.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.45/1.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.45/1.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.45/1.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.45/1.63  thf(sk_D_type, type, sk_D: $i).
% 1.45/1.63  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.45/1.63  thf(sk_A_type, type, sk_A: $i).
% 1.45/1.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.45/1.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.45/1.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.45/1.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.45/1.63  thf(sk_B_type, type, sk_B: $i).
% 1.45/1.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.45/1.63  thf(sk_C_type, type, sk_C: $i).
% 1.45/1.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.45/1.63  thf(sk_E_type, type, sk_E: $i).
% 1.45/1.63  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.45/1.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.45/1.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.45/1.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.45/1.63  thf(t26_funct_2, conjecture,
% 1.45/1.63    (![A:$i,B:$i,C:$i,D:$i]:
% 1.45/1.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.45/1.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.45/1.63       ( ![E:$i]:
% 1.45/1.63         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.45/1.63             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.45/1.63           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.45/1.63             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.45/1.63               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 1.45/1.63  thf(zf_stmt_0, negated_conjecture,
% 1.45/1.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.45/1.63        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.45/1.63            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.45/1.63          ( ![E:$i]:
% 1.45/1.63            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.45/1.63                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.45/1.63              ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.45/1.63                ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.45/1.63                  ( v2_funct_1 @ D ) ) ) ) ) ) )),
% 1.45/1.63    inference('cnf.neg', [status(esa)], [t26_funct_2])).
% 1.45/1.63  thf('0', plain, ((((sk_C) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('1', plain, ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('split', [status(esa)], ['0'])).
% 1.45/1.63  thf('2', plain,
% 1.45/1.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('3', plain,
% 1.45/1.63      (((m1_subset_1 @ sk_D @ 
% 1.45/1.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup+', [status(thm)], ['1', '2'])).
% 1.45/1.63  thf(dt_k2_relset_1, axiom,
% 1.45/1.63    (![A:$i,B:$i,C:$i]:
% 1.45/1.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.45/1.63       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.45/1.63  thf('4', plain,
% 1.45/1.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.45/1.63         ((m1_subset_1 @ (k2_relset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 1.45/1.63          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.45/1.63      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 1.45/1.63  thf('5', plain,
% 1.45/1.63      (((m1_subset_1 @ (k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ 
% 1.45/1.63         (k1_zfmisc_1 @ k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['3', '4'])).
% 1.45/1.63  thf(t3_subset, axiom,
% 1.45/1.63    (![A:$i,B:$i]:
% 1.45/1.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.45/1.63  thf('6', plain,
% 1.45/1.63      (![X0 : $i, X1 : $i]:
% 1.45/1.63         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.45/1.63      inference('cnf', [status(esa)], [t3_subset])).
% 1.45/1.63  thf('7', plain,
% 1.45/1.63      (((r1_tarski @ (k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ k1_xboole_0))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['5', '6'])).
% 1.45/1.63  thf('8', plain,
% 1.45/1.63      (((m1_subset_1 @ sk_D @ 
% 1.45/1.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup+', [status(thm)], ['1', '2'])).
% 1.45/1.63  thf(redefinition_k2_relset_1, axiom,
% 1.45/1.63    (![A:$i,B:$i,C:$i]:
% 1.45/1.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.45/1.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.45/1.63  thf('9', plain,
% 1.45/1.63      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.45/1.63         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.45/1.63          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.45/1.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.45/1.63  thf('10', plain,
% 1.45/1.63      ((((k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D) = (k2_relat_1 @ sk_D)))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['8', '9'])).
% 1.45/1.63  thf('11', plain,
% 1.45/1.63      (((r1_tarski @ (k2_relat_1 @ sk_D) @ k1_xboole_0))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('demod', [status(thm)], ['7', '10'])).
% 1.45/1.63  thf('12', plain,
% 1.45/1.63      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('split', [status(esa)], ['0'])).
% 1.45/1.63  thf('13', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('14', plain,
% 1.45/1.63      (((v1_funct_2 @ sk_E @ k1_xboole_0 @ sk_C))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup+', [status(thm)], ['12', '13'])).
% 1.45/1.63  thf(d1_funct_2, axiom,
% 1.45/1.63    (![A:$i,B:$i,C:$i]:
% 1.45/1.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.45/1.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.45/1.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.45/1.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.45/1.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.45/1.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.45/1.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.45/1.63  thf(zf_stmt_1, axiom,
% 1.45/1.63    (![C:$i,B:$i,A:$i]:
% 1.45/1.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.45/1.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.45/1.63  thf('15', plain,
% 1.45/1.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.45/1.63         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.45/1.63          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 1.45/1.63          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.45/1.63  thf('16', plain,
% 1.45/1.63      (((~ (zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0)
% 1.45/1.63         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E))))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['14', '15'])).
% 1.45/1.63  thf('17', plain,
% 1.45/1.63      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('split', [status(esa)], ['0'])).
% 1.45/1.63  thf('18', plain,
% 1.45/1.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('19', plain,
% 1.45/1.63      (((m1_subset_1 @ sk_E @ 
% 1.45/1.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup+', [status(thm)], ['17', '18'])).
% 1.45/1.63  thf(redefinition_k1_relset_1, axiom,
% 1.45/1.63    (![A:$i,B:$i,C:$i]:
% 1.45/1.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.45/1.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.45/1.63  thf('20', plain,
% 1.45/1.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.45/1.63         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 1.45/1.63          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.45/1.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.45/1.63  thf('21', plain,
% 1.45/1.63      ((((k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E) = (k1_relat_1 @ sk_E)))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['19', '20'])).
% 1.45/1.63  thf('22', plain,
% 1.45/1.63      (((~ (zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0)
% 1.45/1.63         | ((k1_xboole_0) = (k1_relat_1 @ sk_E))))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('demod', [status(thm)], ['16', '21'])).
% 1.45/1.63  thf('23', plain,
% 1.45/1.63      (((m1_subset_1 @ sk_E @ 
% 1.45/1.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup+', [status(thm)], ['17', '18'])).
% 1.45/1.63  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.45/1.63  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.45/1.63  thf(zf_stmt_4, axiom,
% 1.45/1.63    (![B:$i,A:$i]:
% 1.45/1.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.45/1.63       ( zip_tseitin_0 @ B @ A ) ))).
% 1.45/1.63  thf(zf_stmt_5, axiom,
% 1.45/1.63    (![A:$i,B:$i,C:$i]:
% 1.45/1.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.45/1.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.45/1.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.45/1.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.45/1.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.45/1.63  thf('24', plain,
% 1.45/1.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.45/1.63         (~ (zip_tseitin_0 @ X22 @ X23)
% 1.45/1.63          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 1.45/1.63          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.45/1.63  thf('25', plain,
% 1.45/1.63      ((((zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0)
% 1.45/1.63         | ~ (zip_tseitin_0 @ sk_C @ k1_xboole_0)))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['23', '24'])).
% 1.45/1.63  thf('26', plain,
% 1.45/1.63      (![X17 : $i, X18 : $i]:
% 1.45/1.63         ((zip_tseitin_0 @ X17 @ X18) | ((X18) != (k1_xboole_0)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.45/1.63  thf('27', plain, (![X17 : $i]: (zip_tseitin_0 @ X17 @ k1_xboole_0)),
% 1.45/1.63      inference('simplify', [status(thm)], ['26'])).
% 1.45/1.63  thf('28', plain,
% 1.45/1.63      (((zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('demod', [status(thm)], ['25', '27'])).
% 1.45/1.63  thf('29', plain,
% 1.45/1.63      ((((k1_xboole_0) = (k1_relat_1 @ sk_E))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('demod', [status(thm)], ['22', '28'])).
% 1.45/1.63  thf(t47_funct_1, axiom,
% 1.45/1.63    (![A:$i]:
% 1.45/1.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.45/1.63       ( ![B:$i]:
% 1.45/1.63         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.45/1.63           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.45/1.63               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 1.45/1.63             ( v2_funct_1 @ B ) ) ) ) ))).
% 1.45/1.63  thf('30', plain,
% 1.45/1.63      (![X3 : $i, X4 : $i]:
% 1.45/1.63         (~ (v1_relat_1 @ X3)
% 1.45/1.63          | ~ (v1_funct_1 @ X3)
% 1.45/1.63          | (v2_funct_1 @ X3)
% 1.45/1.63          | ~ (r1_tarski @ (k2_relat_1 @ X3) @ (k1_relat_1 @ X4))
% 1.45/1.63          | ~ (v2_funct_1 @ (k5_relat_1 @ X3 @ X4))
% 1.45/1.63          | ~ (v1_funct_1 @ X4)
% 1.45/1.63          | ~ (v1_relat_1 @ X4))),
% 1.45/1.63      inference('cnf', [status(esa)], [t47_funct_1])).
% 1.45/1.63  thf('31', plain,
% 1.45/1.63      ((![X0 : $i]:
% 1.45/1.63          (~ (r1_tarski @ (k2_relat_1 @ X0) @ k1_xboole_0)
% 1.45/1.63           | ~ (v1_relat_1 @ sk_E)
% 1.45/1.63           | ~ (v1_funct_1 @ sk_E)
% 1.45/1.63           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.45/1.63           | (v2_funct_1 @ X0)
% 1.45/1.63           | ~ (v1_funct_1 @ X0)
% 1.45/1.63           | ~ (v1_relat_1 @ X0)))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['29', '30'])).
% 1.45/1.63  thf('32', plain,
% 1.45/1.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf(cc1_relset_1, axiom,
% 1.45/1.63    (![A:$i,B:$i,C:$i]:
% 1.45/1.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.45/1.63       ( v1_relat_1 @ C ) ))).
% 1.45/1.63  thf('33', plain,
% 1.45/1.63      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.45/1.63         ((v1_relat_1 @ X5)
% 1.45/1.63          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.45/1.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.45/1.63  thf('34', plain, ((v1_relat_1 @ sk_E)),
% 1.45/1.63      inference('sup-', [status(thm)], ['32', '33'])).
% 1.45/1.63  thf('35', plain, ((v1_funct_1 @ sk_E)),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('36', plain,
% 1.45/1.63      ((![X0 : $i]:
% 1.45/1.63          (~ (r1_tarski @ (k2_relat_1 @ X0) @ k1_xboole_0)
% 1.45/1.63           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.45/1.63           | (v2_funct_1 @ X0)
% 1.45/1.63           | ~ (v1_funct_1 @ X0)
% 1.45/1.63           | ~ (v1_relat_1 @ X0)))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('demod', [status(thm)], ['31', '34', '35'])).
% 1.45/1.63  thf('37', plain,
% 1.45/1.63      (((~ (v1_relat_1 @ sk_D)
% 1.45/1.63         | ~ (v1_funct_1 @ sk_D)
% 1.45/1.63         | (v2_funct_1 @ sk_D)
% 1.45/1.63         | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['11', '36'])).
% 1.45/1.63  thf('38', plain,
% 1.45/1.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('39', plain,
% 1.45/1.63      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.45/1.63         ((v1_relat_1 @ X5)
% 1.45/1.63          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.45/1.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.45/1.63  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 1.45/1.63      inference('sup-', [status(thm)], ['38', '39'])).
% 1.45/1.63  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('42', plain,
% 1.45/1.63      ((((v2_funct_1 @ sk_D) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('demod', [status(thm)], ['37', '40', '41'])).
% 1.45/1.63  thf('43', plain, (~ (v2_funct_1 @ sk_D)),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('44', plain,
% 1.45/1.63      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('clc', [status(thm)], ['42', '43'])).
% 1.45/1.63  thf('45', plain,
% 1.45/1.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('46', plain,
% 1.45/1.63      (((m1_subset_1 @ sk_D @ 
% 1.45/1.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup+', [status(thm)], ['1', '2'])).
% 1.45/1.63  thf('47', plain,
% 1.45/1.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.45/1.63         (((X22) != (k1_xboole_0))
% 1.45/1.63          | ((X23) = (k1_xboole_0))
% 1.45/1.63          | ((X24) = (k1_xboole_0))
% 1.45/1.63          | ~ (v1_funct_2 @ X24 @ X23 @ X22)
% 1.45/1.63          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.45/1.63  thf('48', plain,
% 1.45/1.63      (![X23 : $i, X24 : $i]:
% 1.45/1.63         (~ (m1_subset_1 @ X24 @ 
% 1.45/1.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ k1_xboole_0)))
% 1.45/1.63          | ~ (v1_funct_2 @ X24 @ X23 @ k1_xboole_0)
% 1.45/1.63          | ((X24) = (k1_xboole_0))
% 1.45/1.63          | ((X23) = (k1_xboole_0)))),
% 1.45/1.63      inference('simplify', [status(thm)], ['47'])).
% 1.45/1.63  thf('49', plain,
% 1.45/1.63      (((((sk_A) = (k1_xboole_0))
% 1.45/1.63         | ((sk_D) = (k1_xboole_0))
% 1.45/1.63         | ~ (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0)))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['46', '48'])).
% 1.45/1.63  thf('50', plain,
% 1.45/1.63      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('split', [status(esa)], ['0'])).
% 1.45/1.63  thf('51', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('52', plain,
% 1.45/1.63      (((v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup+', [status(thm)], ['50', '51'])).
% 1.45/1.63  thf('53', plain,
% 1.45/1.63      (((((sk_A) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0))))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('demod', [status(thm)], ['49', '52'])).
% 1.45/1.63  thf('54', plain,
% 1.45/1.63      (((m1_subset_1 @ sk_D @ 
% 1.45/1.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup+', [status(thm)], ['1', '2'])).
% 1.45/1.63  thf('55', plain,
% 1.45/1.63      ((((m1_subset_1 @ sk_D @ 
% 1.45/1.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))
% 1.45/1.63         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup+', [status(thm)], ['53', '54'])).
% 1.45/1.63  thf(redefinition_k1_partfun1, axiom,
% 1.45/1.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.45/1.63     ( ( ( v1_funct_1 @ E ) & 
% 1.45/1.63         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.45/1.63         ( v1_funct_1 @ F ) & 
% 1.45/1.63         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.45/1.63       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.45/1.63  thf('56', plain,
% 1.45/1.63      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.45/1.63         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.45/1.63          | ~ (v1_funct_1 @ X25)
% 1.45/1.63          | ~ (v1_funct_1 @ X28)
% 1.45/1.63          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.45/1.63          | ((k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 1.45/1.63              = (k5_relat_1 @ X25 @ X28)))),
% 1.45/1.63      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.45/1.63  thf('57', plain,
% 1.45/1.63      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.63          (((sk_D) = (k1_xboole_0))
% 1.45/1.63           | ((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0)
% 1.45/1.63               = (k5_relat_1 @ sk_D @ X0))
% 1.45/1.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.45/1.63           | ~ (v1_funct_1 @ X0)
% 1.45/1.63           | ~ (v1_funct_1 @ sk_D)))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['55', '56'])).
% 1.45/1.63  thf('58', plain, ((v1_funct_1 @ sk_D)),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('59', plain,
% 1.45/1.63      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.63          (((sk_D) = (k1_xboole_0))
% 1.45/1.63           | ((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0)
% 1.45/1.63               = (k5_relat_1 @ sk_D @ X0))
% 1.45/1.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.45/1.63           | ~ (v1_funct_1 @ X0)))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('demod', [status(thm)], ['57', '58'])).
% 1.45/1.63  thf('60', plain,
% 1.45/1.63      (((~ (v1_funct_1 @ sk_E)
% 1.45/1.63         | ((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ 
% 1.45/1.63             sk_E) = (k5_relat_1 @ sk_D @ sk_E))
% 1.45/1.63         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['45', '59'])).
% 1.45/1.63  thf('61', plain, ((v1_funct_1 @ sk_E)),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('62', plain,
% 1.45/1.63      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('split', [status(esa)], ['0'])).
% 1.45/1.63  thf('63', plain,
% 1.45/1.63      (((((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ 
% 1.45/1.63           sk_D @ sk_E) = (k5_relat_1 @ sk_D @ sk_E))
% 1.45/1.63         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.45/1.63  thf('64', plain,
% 1.45/1.63      (((((sk_A) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0))))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('demod', [status(thm)], ['49', '52'])).
% 1.45/1.63  thf('65', plain,
% 1.45/1.63      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('split', [status(esa)], ['0'])).
% 1.45/1.63  thf('66', plain,
% 1.45/1.63      ((v2_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('67', plain,
% 1.45/1.63      (((v2_funct_1 @ 
% 1.45/1.63         (k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E)))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup+', [status(thm)], ['65', '66'])).
% 1.45/1.63  thf('68', plain,
% 1.45/1.63      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('split', [status(esa)], ['0'])).
% 1.45/1.63  thf('69', plain,
% 1.45/1.63      (((v2_funct_1 @ 
% 1.45/1.63         (k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E)))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('demod', [status(thm)], ['67', '68'])).
% 1.45/1.63  thf('70', plain,
% 1.45/1.63      ((((v2_funct_1 @ 
% 1.45/1.63          (k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ 
% 1.45/1.63           sk_D @ sk_E))
% 1.45/1.63         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup+', [status(thm)], ['64', '69'])).
% 1.45/1.63  thf('71', plain,
% 1.45/1.63      ((((v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))
% 1.45/1.63         | ((sk_D) = (k1_xboole_0))
% 1.45/1.63         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup+', [status(thm)], ['63', '70'])).
% 1.45/1.63  thf('72', plain,
% 1.45/1.63      (((((sk_D) = (k1_xboole_0)) | (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('simplify', [status(thm)], ['71'])).
% 1.45/1.63  thf('73', plain,
% 1.45/1.63      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('clc', [status(thm)], ['42', '43'])).
% 1.45/1.63  thf('74', plain,
% 1.45/1.63      ((((sk_D) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('clc', [status(thm)], ['72', '73'])).
% 1.45/1.63  thf('75', plain,
% 1.45/1.63      ((~ (v2_funct_1 @ (k5_relat_1 @ k1_xboole_0 @ sk_E)))
% 1.45/1.63         <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('demod', [status(thm)], ['44', '74'])).
% 1.45/1.63  thf('76', plain,
% 1.45/1.63      ((v2_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('77', plain,
% 1.45/1.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('78', plain,
% 1.45/1.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('79', plain,
% 1.45/1.63      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.45/1.63         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.45/1.63          | ~ (v1_funct_1 @ X25)
% 1.45/1.63          | ~ (v1_funct_1 @ X28)
% 1.45/1.63          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.45/1.63          | ((k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 1.45/1.63              = (k5_relat_1 @ X25 @ X28)))),
% 1.45/1.63      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.45/1.63  thf('80', plain,
% 1.45/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.63         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.45/1.63            = (k5_relat_1 @ sk_D @ X0))
% 1.45/1.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.45/1.63          | ~ (v1_funct_1 @ X0)
% 1.45/1.63          | ~ (v1_funct_1 @ sk_D))),
% 1.45/1.63      inference('sup-', [status(thm)], ['78', '79'])).
% 1.45/1.63  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('82', plain,
% 1.45/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.63         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.45/1.63            = (k5_relat_1 @ sk_D @ X0))
% 1.45/1.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.45/1.63          | ~ (v1_funct_1 @ X0))),
% 1.45/1.63      inference('demod', [status(thm)], ['80', '81'])).
% 1.45/1.63  thf('83', plain,
% 1.45/1.63      ((~ (v1_funct_1 @ sk_E)
% 1.45/1.63        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.45/1.63            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.45/1.63      inference('sup-', [status(thm)], ['77', '82'])).
% 1.45/1.63  thf('84', plain, ((v1_funct_1 @ sk_E)),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('85', plain,
% 1.45/1.63      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.45/1.63         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.45/1.63      inference('demod', [status(thm)], ['83', '84'])).
% 1.45/1.63  thf('86', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 1.45/1.63      inference('demod', [status(thm)], ['76', '85'])).
% 1.45/1.63  thf('87', plain,
% 1.45/1.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('88', plain,
% 1.45/1.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.45/1.63         ((m1_subset_1 @ (k2_relset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 1.45/1.63          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.45/1.63      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 1.45/1.63  thf('89', plain,
% 1.45/1.63      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 1.45/1.63      inference('sup-', [status(thm)], ['87', '88'])).
% 1.45/1.63  thf('90', plain,
% 1.45/1.63      (![X0 : $i, X1 : $i]:
% 1.45/1.63         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.45/1.63      inference('cnf', [status(esa)], [t3_subset])).
% 1.45/1.63  thf('91', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_B)),
% 1.45/1.63      inference('sup-', [status(thm)], ['89', '90'])).
% 1.45/1.63  thf('92', plain,
% 1.45/1.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('93', plain,
% 1.45/1.63      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.45/1.63         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.45/1.63          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.45/1.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.45/1.63  thf('94', plain,
% 1.45/1.63      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.45/1.63      inference('sup-', [status(thm)], ['92', '93'])).
% 1.45/1.63  thf('95', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 1.45/1.63      inference('demod', [status(thm)], ['91', '94'])).
% 1.45/1.63  thf('96', plain,
% 1.45/1.63      (![X17 : $i, X18 : $i]:
% 1.45/1.63         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.45/1.63  thf('97', plain,
% 1.45/1.63      (![X17 : $i, X18 : $i]:
% 1.45/1.63         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.45/1.63  thf('98', plain,
% 1.45/1.63      (![X17 : $i, X18 : $i]:
% 1.45/1.63         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.45/1.63  thf('99', plain,
% 1.45/1.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.45/1.63         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 1.45/1.63      inference('sup+', [status(thm)], ['97', '98'])).
% 1.45/1.63  thf('100', plain,
% 1.45/1.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('101', plain,
% 1.45/1.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.45/1.63         (~ (zip_tseitin_0 @ X22 @ X23)
% 1.45/1.63          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 1.45/1.63          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.45/1.63  thf('102', plain,
% 1.45/1.63      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.45/1.63      inference('sup-', [status(thm)], ['100', '101'])).
% 1.45/1.63  thf('103', plain,
% 1.45/1.63      (![X0 : $i, X1 : $i]:
% 1.45/1.63         ((zip_tseitin_0 @ X1 @ X0)
% 1.45/1.63          | ((sk_C) = (X1))
% 1.45/1.63          | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.45/1.63      inference('sup-', [status(thm)], ['99', '102'])).
% 1.45/1.63  thf('104', plain,
% 1.45/1.63      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.63      inference('split', [status(esa)], ['0'])).
% 1.45/1.63  thf('105', plain,
% 1.45/1.63      ((![X0 : $i, X1 : $i]:
% 1.45/1.63          (((X0) != (k1_xboole_0))
% 1.45/1.63           | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.45/1.63           | (zip_tseitin_0 @ X0 @ X1)))
% 1.45/1.63         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['103', '104'])).
% 1.45/1.63  thf('106', plain,
% 1.45/1.63      ((![X1 : $i]:
% 1.45/1.63          ((zip_tseitin_0 @ k1_xboole_0 @ X1)
% 1.45/1.63           | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)))
% 1.45/1.63         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.63      inference('simplify', [status(thm)], ['105'])).
% 1.45/1.63  thf('107', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('108', plain,
% 1.45/1.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.45/1.63         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.45/1.63          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 1.45/1.63          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.45/1.63  thf('109', plain,
% 1.45/1.63      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.45/1.63        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.45/1.63      inference('sup-', [status(thm)], ['107', '108'])).
% 1.45/1.63  thf('110', plain,
% 1.45/1.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('111', plain,
% 1.45/1.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.45/1.63         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 1.45/1.63          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.45/1.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.45/1.63  thf('112', plain,
% 1.45/1.63      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.45/1.63      inference('sup-', [status(thm)], ['110', '111'])).
% 1.45/1.63  thf('113', plain,
% 1.45/1.63      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_E)))),
% 1.45/1.63      inference('demod', [status(thm)], ['109', '112'])).
% 1.45/1.63  thf('114', plain,
% 1.45/1.63      ((![X0 : $i]:
% 1.45/1.63          ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_B) = (k1_relat_1 @ sk_E))))
% 1.45/1.63         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['106', '113'])).
% 1.45/1.63  thf('115', plain,
% 1.45/1.63      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.63          ((zip_tseitin_0 @ X0 @ X1)
% 1.45/1.63           | (zip_tseitin_0 @ X0 @ X2)
% 1.45/1.63           | ((sk_B) = (k1_relat_1 @ sk_E))))
% 1.45/1.63         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup+', [status(thm)], ['96', '114'])).
% 1.45/1.63  thf('116', plain,
% 1.45/1.63      ((![X0 : $i, X1 : $i]:
% 1.45/1.63          (((sk_B) = (k1_relat_1 @ sk_E)) | (zip_tseitin_0 @ X1 @ X0)))
% 1.45/1.63         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.63      inference('condensation', [status(thm)], ['115'])).
% 1.45/1.63  thf('117', plain,
% 1.45/1.63      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.45/1.63      inference('sup-', [status(thm)], ['100', '101'])).
% 1.45/1.63  thf('118', plain,
% 1.45/1.63      (((((sk_B) = (k1_relat_1 @ sk_E)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)))
% 1.45/1.63         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['116', '117'])).
% 1.45/1.63  thf('119', plain,
% 1.45/1.63      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_E)))),
% 1.45/1.63      inference('demod', [status(thm)], ['109', '112'])).
% 1.45/1.63  thf('120', plain,
% 1.45/1.63      ((((sk_B) = (k1_relat_1 @ sk_E))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.63      inference('clc', [status(thm)], ['118', '119'])).
% 1.45/1.63  thf('121', plain,
% 1.45/1.63      (![X3 : $i, X4 : $i]:
% 1.45/1.63         (~ (v1_relat_1 @ X3)
% 1.45/1.63          | ~ (v1_funct_1 @ X3)
% 1.45/1.63          | (v2_funct_1 @ X3)
% 1.45/1.63          | ~ (r1_tarski @ (k2_relat_1 @ X3) @ (k1_relat_1 @ X4))
% 1.45/1.63          | ~ (v2_funct_1 @ (k5_relat_1 @ X3 @ X4))
% 1.45/1.63          | ~ (v1_funct_1 @ X4)
% 1.45/1.63          | ~ (v1_relat_1 @ X4))),
% 1.45/1.63      inference('cnf', [status(esa)], [t47_funct_1])).
% 1.45/1.63  thf('122', plain,
% 1.45/1.63      ((![X0 : $i]:
% 1.45/1.63          (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B)
% 1.45/1.63           | ~ (v1_relat_1 @ sk_E)
% 1.45/1.63           | ~ (v1_funct_1 @ sk_E)
% 1.45/1.63           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.45/1.63           | (v2_funct_1 @ X0)
% 1.45/1.63           | ~ (v1_funct_1 @ X0)
% 1.45/1.63           | ~ (v1_relat_1 @ X0)))
% 1.45/1.63         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['120', '121'])).
% 1.45/1.63  thf('123', plain, ((v1_relat_1 @ sk_E)),
% 1.45/1.63      inference('sup-', [status(thm)], ['32', '33'])).
% 1.45/1.63  thf('124', plain, ((v1_funct_1 @ sk_E)),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('125', plain,
% 1.45/1.63      ((![X0 : $i]:
% 1.45/1.63          (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B)
% 1.45/1.63           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.45/1.63           | (v2_funct_1 @ X0)
% 1.45/1.63           | ~ (v1_funct_1 @ X0)
% 1.45/1.63           | ~ (v1_relat_1 @ X0)))
% 1.45/1.63         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.63      inference('demod', [status(thm)], ['122', '123', '124'])).
% 1.45/1.63  thf('126', plain,
% 1.45/1.63      (((~ (v1_relat_1 @ sk_D)
% 1.45/1.63         | ~ (v1_funct_1 @ sk_D)
% 1.45/1.63         | (v2_funct_1 @ sk_D)
% 1.45/1.63         | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.45/1.63         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.63      inference('sup-', [status(thm)], ['95', '125'])).
% 1.45/1.63  thf('127', plain, ((v1_relat_1 @ sk_D)),
% 1.45/1.63      inference('sup-', [status(thm)], ['38', '39'])).
% 1.45/1.63  thf('128', plain, ((v1_funct_1 @ sk_D)),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('129', plain,
% 1.45/1.63      ((((v2_funct_1 @ sk_D) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.45/1.63         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.63      inference('demod', [status(thm)], ['126', '127', '128'])).
% 1.45/1.63  thf('130', plain, (~ (v2_funct_1 @ sk_D)),
% 1.45/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.63  thf('131', plain,
% 1.45/1.63      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 1.45/1.63         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.63      inference('clc', [status(thm)], ['129', '130'])).
% 1.45/1.63  thf('132', plain, ((((sk_C) = (k1_xboole_0)))),
% 1.45/1.63      inference('sup-', [status(thm)], ['86', '131'])).
% 1.45/1.63  thf('133', plain,
% 1.45/1.63      ((((sk_B) = (k1_xboole_0))) | ~ (((sk_C) = (k1_xboole_0)))),
% 1.45/1.63      inference('split', [status(esa)], ['0'])).
% 1.45/1.63  thf('134', plain, ((((sk_B) = (k1_xboole_0)))),
% 1.45/1.63      inference('sat_resolution*', [status(thm)], ['132', '133'])).
% 1.45/1.63  thf('135', plain, (~ (v2_funct_1 @ (k5_relat_1 @ k1_xboole_0 @ sk_E))),
% 1.45/1.63      inference('simpl_trail', [status(thm)], ['75', '134'])).
% 1.45/1.63  thf('136', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 1.45/1.63      inference('demod', [status(thm)], ['76', '85'])).
% 1.45/1.63  thf('137', plain,
% 1.45/1.63      ((((sk_D) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.45/1.63      inference('clc', [status(thm)], ['72', '73'])).
% 1.45/1.63  thf('138', plain, ((((sk_B) = (k1_xboole_0)))),
% 1.45/1.63      inference('sat_resolution*', [status(thm)], ['132', '133'])).
% 1.45/1.63  thf('139', plain, (((sk_D) = (k1_xboole_0))),
% 1.45/1.63      inference('simpl_trail', [status(thm)], ['137', '138'])).
% 1.45/1.63  thf('140', plain, ((v2_funct_1 @ (k5_relat_1 @ k1_xboole_0 @ sk_E))),
% 1.45/1.63      inference('demod', [status(thm)], ['136', '139'])).
% 1.45/1.63  thf('141', plain, ($false), inference('demod', [status(thm)], ['135', '140'])).
% 1.45/1.63  
% 1.45/1.63  % SZS output end Refutation
% 1.45/1.63  
% 1.45/1.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
