%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mXID0CGuCd

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:54 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 793 expanded)
%              Number of leaves         :   37 ( 228 expanded)
%              Depth                    :   21
%              Number of atoms          : 1555 (14789 expanded)
%              Number of equality atoms :  155 (1001 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('27',plain,(
    ! [X18: $i] :
      ( zip_tseitin_0 @ X18 @ k1_xboole_0 ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X7 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('36',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','36','37'])).

thf('39',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','44','45'])).

thf('47',plain,(
    ~ ( v2_funct_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('51',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 != k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X24 @ k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('59',plain,
    ( ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('60',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('61',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( sk_D = k1_xboole_0 )
        | ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0 )
          = ( k5_relat_1 @ sk_D @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ sk_D ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( sk_D = k1_xboole_0 )
        | ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0 )
          = ( k5_relat_1 @ sk_D @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ~ ( v1_funct_1 @ sk_E )
      | ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E )
        = ( k5_relat_1 @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ( ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E )
        = ( k5_relat_1 @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,(
    v2_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( v2_funct_1 @ ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','73'])).

thf('75',plain,
    ( ( ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','74'])).

thf('76',plain,
    ( ( ( sk_D = k1_xboole_0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('78',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ k1_xboole_0 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','78'])).

thf('80',plain,(
    v2_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['80','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('93',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('95',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('98',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('101',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('102',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('106',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_C = X1 )
      | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('113',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('116',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['113','116'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_B
          = ( k1_relat_1 @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','117'])).

thf('119',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_B
          = ( k1_relat_1 @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','118'])).

thf('120',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B
          = ( k1_relat_1 @ sk_E ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['119'])).

thf('121',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('122',plain,
    ( ( ( sk_B
        = ( k1_relat_1 @ sk_E ) )
      | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['113','116'])).

thf('124',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X7 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('126',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B )
        | ~ ( v1_relat_1 @ sk_E )
        | ~ ( v1_funct_1 @ sk_E )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['34','35'])).

thf('128',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('132',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ~ ( v2_funct_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['90','135'])).

thf('137',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('138',plain,(
    sk_B = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_funct_1 @ ( k5_relat_1 @ k1_xboole_0 @ sk_E ) ) ),
    inference(simpl_trail,[status(thm)],['79','138'])).

thf('140',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['80','89'])).

thf('141',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('142',plain,(
    sk_B = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['136','137'])).

thf('143',plain,(
    sk_D = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['141','142'])).

thf('144',plain,(
    v2_funct_1 @ ( k5_relat_1 @ k1_xboole_0 @ sk_E ) ),
    inference(demod,[status(thm)],['140','143'])).

thf('145',plain,(
    $false ),
    inference(demod,[status(thm)],['139','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mXID0CGuCd
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.60/1.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.60/1.79  % Solved by: fo/fo7.sh
% 1.60/1.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.60/1.79  % done 1275 iterations in 1.333s
% 1.60/1.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.60/1.79  % SZS output start Refutation
% 1.60/1.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.60/1.79  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.60/1.79  thf(sk_C_type, type, sk_C: $i).
% 1.60/1.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.60/1.79  thf(sk_D_type, type, sk_D: $i).
% 1.60/1.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.60/1.79  thf(sk_E_type, type, sk_E: $i).
% 1.60/1.79  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.60/1.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.60/1.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.60/1.79  thf(sk_A_type, type, sk_A: $i).
% 1.60/1.79  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.60/1.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.60/1.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.60/1.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.60/1.79  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.60/1.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.60/1.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.60/1.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.60/1.79  thf(sk_B_type, type, sk_B: $i).
% 1.60/1.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.60/1.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.60/1.79  thf(t26_funct_2, conjecture,
% 1.60/1.79    (![A:$i,B:$i,C:$i,D:$i]:
% 1.60/1.79     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.60/1.79         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.79       ( ![E:$i]:
% 1.60/1.79         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.60/1.79             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.60/1.79           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.60/1.79             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.60/1.79               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 1.60/1.79  thf(zf_stmt_0, negated_conjecture,
% 1.60/1.79    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.60/1.79        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.60/1.79            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.79          ( ![E:$i]:
% 1.60/1.79            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.60/1.79                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.60/1.79              ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.60/1.79                ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.60/1.79                  ( v2_funct_1 @ D ) ) ) ) ) ) )),
% 1.60/1.79    inference('cnf.neg', [status(esa)], [t26_funct_2])).
% 1.60/1.79  thf('0', plain, ((((sk_C) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('1', plain, ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('split', [status(esa)], ['0'])).
% 1.60/1.79  thf('2', plain,
% 1.60/1.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('3', plain,
% 1.60/1.79      (((m1_subset_1 @ sk_D @ 
% 1.60/1.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup+', [status(thm)], ['1', '2'])).
% 1.60/1.79  thf(dt_k2_relset_1, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.79       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.60/1.79  thf('4', plain,
% 1.60/1.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.60/1.79         ((m1_subset_1 @ (k2_relset_1 @ X9 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))
% 1.60/1.79          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.60/1.79      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 1.60/1.79  thf('5', plain,
% 1.60/1.79      (((m1_subset_1 @ (k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ 
% 1.60/1.79         (k1_zfmisc_1 @ k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['3', '4'])).
% 1.60/1.79  thf(t3_subset, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.60/1.79  thf('6', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i]:
% 1.60/1.79         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.60/1.79      inference('cnf', [status(esa)], [t3_subset])).
% 1.60/1.79  thf('7', plain,
% 1.60/1.79      (((r1_tarski @ (k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ k1_xboole_0))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['5', '6'])).
% 1.60/1.79  thf('8', plain,
% 1.60/1.79      (((m1_subset_1 @ sk_D @ 
% 1.60/1.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup+', [status(thm)], ['1', '2'])).
% 1.60/1.79  thf(redefinition_k2_relset_1, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.79       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.60/1.79  thf('9', plain,
% 1.60/1.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.60/1.79         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.60/1.79          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.60/1.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.60/1.79  thf('10', plain,
% 1.60/1.79      ((((k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D) = (k2_relat_1 @ sk_D)))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['8', '9'])).
% 1.60/1.79  thf('11', plain,
% 1.60/1.79      (((r1_tarski @ (k2_relat_1 @ sk_D) @ k1_xboole_0))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('demod', [status(thm)], ['7', '10'])).
% 1.60/1.79  thf('12', plain,
% 1.60/1.79      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('split', [status(esa)], ['0'])).
% 1.60/1.79  thf('13', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('14', plain,
% 1.60/1.79      (((v1_funct_2 @ sk_E @ k1_xboole_0 @ sk_C))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup+', [status(thm)], ['12', '13'])).
% 1.60/1.79  thf(d1_funct_2, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.79       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.60/1.79           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.60/1.79             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.60/1.79         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.60/1.79           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.60/1.79             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.60/1.79  thf(zf_stmt_1, axiom,
% 1.60/1.79    (![C:$i,B:$i,A:$i]:
% 1.60/1.79     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.60/1.79       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.60/1.79  thf('15', plain,
% 1.60/1.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.60/1.79         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 1.60/1.79          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 1.60/1.79          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.60/1.79  thf('16', plain,
% 1.60/1.79      (((~ (zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0)
% 1.60/1.79         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E))))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['14', '15'])).
% 1.60/1.79  thf('17', plain,
% 1.60/1.79      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('split', [status(esa)], ['0'])).
% 1.60/1.79  thf('18', plain,
% 1.60/1.79      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('19', plain,
% 1.60/1.79      (((m1_subset_1 @ sk_E @ 
% 1.60/1.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup+', [status(thm)], ['17', '18'])).
% 1.60/1.79  thf(redefinition_k1_relset_1, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.79       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.60/1.79  thf('20', plain,
% 1.60/1.79      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.60/1.79         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 1.60/1.79          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.60/1.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.60/1.79  thf('21', plain,
% 1.60/1.79      ((((k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E) = (k1_relat_1 @ sk_E)))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['19', '20'])).
% 1.60/1.79  thf('22', plain,
% 1.60/1.79      (((~ (zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0)
% 1.60/1.79         | ((k1_xboole_0) = (k1_relat_1 @ sk_E))))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('demod', [status(thm)], ['16', '21'])).
% 1.60/1.79  thf('23', plain,
% 1.60/1.79      (((m1_subset_1 @ sk_E @ 
% 1.60/1.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup+', [status(thm)], ['17', '18'])).
% 1.60/1.79  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.60/1.79  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.60/1.79  thf(zf_stmt_4, axiom,
% 1.60/1.79    (![B:$i,A:$i]:
% 1.60/1.79     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.60/1.79       ( zip_tseitin_0 @ B @ A ) ))).
% 1.60/1.79  thf(zf_stmt_5, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.79       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.60/1.79         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.60/1.79           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.60/1.79             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.60/1.79  thf('24', plain,
% 1.60/1.79      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.60/1.79         (~ (zip_tseitin_0 @ X23 @ X24)
% 1.60/1.79          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 1.60/1.79          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.60/1.79  thf('25', plain,
% 1.60/1.79      ((((zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0)
% 1.60/1.79         | ~ (zip_tseitin_0 @ sk_C @ k1_xboole_0)))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['23', '24'])).
% 1.60/1.79  thf('26', plain,
% 1.60/1.79      (![X18 : $i, X19 : $i]:
% 1.60/1.79         ((zip_tseitin_0 @ X18 @ X19) | ((X19) != (k1_xboole_0)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.60/1.79  thf('27', plain, (![X18 : $i]: (zip_tseitin_0 @ X18 @ k1_xboole_0)),
% 1.60/1.79      inference('simplify', [status(thm)], ['26'])).
% 1.60/1.79  thf('28', plain,
% 1.60/1.79      (((zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('demod', [status(thm)], ['25', '27'])).
% 1.60/1.79  thf('29', plain,
% 1.60/1.79      ((((k1_xboole_0) = (k1_relat_1 @ sk_E))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('demod', [status(thm)], ['22', '28'])).
% 1.60/1.79  thf(t47_funct_1, axiom,
% 1.60/1.79    (![A:$i]:
% 1.60/1.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.60/1.79       ( ![B:$i]:
% 1.60/1.79         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.60/1.79           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.60/1.79               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 1.60/1.79             ( v2_funct_1 @ B ) ) ) ) ))).
% 1.60/1.79  thf('30', plain,
% 1.60/1.79      (![X7 : $i, X8 : $i]:
% 1.60/1.79         (~ (v1_relat_1 @ X7)
% 1.60/1.79          | ~ (v1_funct_1 @ X7)
% 1.60/1.79          | (v2_funct_1 @ X7)
% 1.60/1.79          | ~ (r1_tarski @ (k2_relat_1 @ X7) @ (k1_relat_1 @ X8))
% 1.60/1.79          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 1.60/1.79          | ~ (v1_funct_1 @ X8)
% 1.60/1.79          | ~ (v1_relat_1 @ X8))),
% 1.60/1.79      inference('cnf', [status(esa)], [t47_funct_1])).
% 1.60/1.79  thf('31', plain,
% 1.60/1.79      ((![X0 : $i]:
% 1.60/1.79          (~ (r1_tarski @ (k2_relat_1 @ X0) @ k1_xboole_0)
% 1.60/1.79           | ~ (v1_relat_1 @ sk_E)
% 1.60/1.79           | ~ (v1_funct_1 @ sk_E)
% 1.60/1.79           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.60/1.79           | (v2_funct_1 @ X0)
% 1.60/1.79           | ~ (v1_funct_1 @ X0)
% 1.60/1.79           | ~ (v1_relat_1 @ X0)))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['29', '30'])).
% 1.60/1.79  thf('32', plain,
% 1.60/1.79      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf(cc2_relat_1, axiom,
% 1.60/1.79    (![A:$i]:
% 1.60/1.79     ( ( v1_relat_1 @ A ) =>
% 1.60/1.79       ( ![B:$i]:
% 1.60/1.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.60/1.79  thf('33', plain,
% 1.60/1.79      (![X3 : $i, X4 : $i]:
% 1.60/1.79         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.60/1.79          | (v1_relat_1 @ X3)
% 1.60/1.79          | ~ (v1_relat_1 @ X4))),
% 1.60/1.79      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.60/1.79  thf('34', plain,
% 1.60/1.79      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 1.60/1.79      inference('sup-', [status(thm)], ['32', '33'])).
% 1.60/1.79  thf(fc6_relat_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.60/1.79  thf('35', plain,
% 1.60/1.79      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 1.60/1.79      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.60/1.79  thf('36', plain, ((v1_relat_1 @ sk_E)),
% 1.60/1.79      inference('demod', [status(thm)], ['34', '35'])).
% 1.60/1.79  thf('37', plain, ((v1_funct_1 @ sk_E)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('38', plain,
% 1.60/1.79      ((![X0 : $i]:
% 1.60/1.79          (~ (r1_tarski @ (k2_relat_1 @ X0) @ k1_xboole_0)
% 1.60/1.79           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.60/1.79           | (v2_funct_1 @ X0)
% 1.60/1.79           | ~ (v1_funct_1 @ X0)
% 1.60/1.79           | ~ (v1_relat_1 @ X0)))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('demod', [status(thm)], ['31', '36', '37'])).
% 1.60/1.79  thf('39', plain,
% 1.60/1.79      (((~ (v1_relat_1 @ sk_D)
% 1.60/1.79         | ~ (v1_funct_1 @ sk_D)
% 1.60/1.79         | (v2_funct_1 @ sk_D)
% 1.60/1.79         | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['11', '38'])).
% 1.60/1.79  thf('40', plain,
% 1.60/1.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('41', plain,
% 1.60/1.79      (![X3 : $i, X4 : $i]:
% 1.60/1.79         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.60/1.79          | (v1_relat_1 @ X3)
% 1.60/1.79          | ~ (v1_relat_1 @ X4))),
% 1.60/1.79      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.60/1.79  thf('42', plain,
% 1.60/1.79      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 1.60/1.79      inference('sup-', [status(thm)], ['40', '41'])).
% 1.60/1.79  thf('43', plain,
% 1.60/1.79      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 1.60/1.79      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.60/1.79  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 1.60/1.79      inference('demod', [status(thm)], ['42', '43'])).
% 1.60/1.79  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('46', plain,
% 1.60/1.79      ((((v2_funct_1 @ sk_D) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('demod', [status(thm)], ['39', '44', '45'])).
% 1.60/1.79  thf('47', plain, (~ (v2_funct_1 @ sk_D)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('48', plain,
% 1.60/1.79      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('clc', [status(thm)], ['46', '47'])).
% 1.60/1.79  thf('49', plain,
% 1.60/1.79      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('50', plain,
% 1.60/1.79      (((m1_subset_1 @ sk_D @ 
% 1.60/1.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup+', [status(thm)], ['1', '2'])).
% 1.60/1.79  thf('51', plain,
% 1.60/1.79      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.60/1.79         (((X23) != (k1_xboole_0))
% 1.60/1.79          | ((X24) = (k1_xboole_0))
% 1.60/1.79          | ((X25) = (k1_xboole_0))
% 1.60/1.79          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 1.60/1.79          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.60/1.79  thf('52', plain,
% 1.60/1.79      (![X24 : $i, X25 : $i]:
% 1.60/1.79         (~ (m1_subset_1 @ X25 @ 
% 1.60/1.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ k1_xboole_0)))
% 1.60/1.79          | ~ (v1_funct_2 @ X25 @ X24 @ k1_xboole_0)
% 1.60/1.79          | ((X25) = (k1_xboole_0))
% 1.60/1.79          | ((X24) = (k1_xboole_0)))),
% 1.60/1.79      inference('simplify', [status(thm)], ['51'])).
% 1.60/1.79  thf('53', plain,
% 1.60/1.79      (((((sk_A) = (k1_xboole_0))
% 1.60/1.79         | ((sk_D) = (k1_xboole_0))
% 1.60/1.79         | ~ (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0)))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['50', '52'])).
% 1.60/1.79  thf('54', plain,
% 1.60/1.79      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('split', [status(esa)], ['0'])).
% 1.60/1.79  thf('55', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('56', plain,
% 1.60/1.79      (((v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup+', [status(thm)], ['54', '55'])).
% 1.60/1.79  thf('57', plain,
% 1.60/1.79      (((((sk_A) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0))))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('demod', [status(thm)], ['53', '56'])).
% 1.60/1.79  thf('58', plain,
% 1.60/1.79      (((m1_subset_1 @ sk_D @ 
% 1.60/1.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup+', [status(thm)], ['1', '2'])).
% 1.60/1.79  thf('59', plain,
% 1.60/1.79      ((((m1_subset_1 @ sk_D @ 
% 1.60/1.79          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))
% 1.60/1.79         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup+', [status(thm)], ['57', '58'])).
% 1.60/1.79  thf(redefinition_k1_partfun1, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.60/1.79     ( ( ( v1_funct_1 @ E ) & 
% 1.60/1.79         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.60/1.79         ( v1_funct_1 @ F ) & 
% 1.60/1.79         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.60/1.79       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.60/1.79  thf('60', plain,
% 1.60/1.79      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.60/1.79         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.60/1.79          | ~ (v1_funct_1 @ X26)
% 1.60/1.79          | ~ (v1_funct_1 @ X29)
% 1.60/1.79          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.60/1.79          | ((k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 1.60/1.79              = (k5_relat_1 @ X26 @ X29)))),
% 1.60/1.79      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.60/1.79  thf('61', plain,
% 1.60/1.79      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.79          (((sk_D) = (k1_xboole_0))
% 1.60/1.79           | ((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0)
% 1.60/1.79               = (k5_relat_1 @ sk_D @ X0))
% 1.60/1.79           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.60/1.79           | ~ (v1_funct_1 @ X0)
% 1.60/1.79           | ~ (v1_funct_1 @ sk_D)))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['59', '60'])).
% 1.60/1.79  thf('62', plain, ((v1_funct_1 @ sk_D)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('63', plain,
% 1.60/1.79      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.79          (((sk_D) = (k1_xboole_0))
% 1.60/1.79           | ((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0)
% 1.60/1.79               = (k5_relat_1 @ sk_D @ X0))
% 1.60/1.79           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.60/1.79           | ~ (v1_funct_1 @ X0)))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('demod', [status(thm)], ['61', '62'])).
% 1.60/1.79  thf('64', plain,
% 1.60/1.79      (((~ (v1_funct_1 @ sk_E)
% 1.60/1.79         | ((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ 
% 1.60/1.79             sk_E) = (k5_relat_1 @ sk_D @ sk_E))
% 1.60/1.79         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['49', '63'])).
% 1.60/1.79  thf('65', plain, ((v1_funct_1 @ sk_E)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('66', plain,
% 1.60/1.79      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('split', [status(esa)], ['0'])).
% 1.60/1.79  thf('67', plain,
% 1.60/1.79      (((((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ 
% 1.60/1.79           sk_D @ sk_E) = (k5_relat_1 @ sk_D @ sk_E))
% 1.60/1.79         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.60/1.79  thf('68', plain,
% 1.60/1.79      (((((sk_A) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0))))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('demod', [status(thm)], ['53', '56'])).
% 1.60/1.79  thf('69', plain,
% 1.60/1.79      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('split', [status(esa)], ['0'])).
% 1.60/1.79  thf('70', plain,
% 1.60/1.79      ((v2_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('71', plain,
% 1.60/1.79      (((v2_funct_1 @ 
% 1.60/1.79         (k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E)))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup+', [status(thm)], ['69', '70'])).
% 1.60/1.79  thf('72', plain,
% 1.60/1.79      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('split', [status(esa)], ['0'])).
% 1.60/1.79  thf('73', plain,
% 1.60/1.79      (((v2_funct_1 @ 
% 1.60/1.79         (k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E)))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('demod', [status(thm)], ['71', '72'])).
% 1.60/1.79  thf('74', plain,
% 1.60/1.79      ((((v2_funct_1 @ 
% 1.60/1.79          (k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ 
% 1.60/1.79           sk_D @ sk_E))
% 1.60/1.79         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup+', [status(thm)], ['68', '73'])).
% 1.60/1.79  thf('75', plain,
% 1.60/1.79      ((((v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))
% 1.60/1.79         | ((sk_D) = (k1_xboole_0))
% 1.60/1.79         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup+', [status(thm)], ['67', '74'])).
% 1.60/1.79  thf('76', plain,
% 1.60/1.79      (((((sk_D) = (k1_xboole_0)) | (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('simplify', [status(thm)], ['75'])).
% 1.60/1.79  thf('77', plain,
% 1.60/1.79      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('clc', [status(thm)], ['46', '47'])).
% 1.60/1.79  thf('78', plain,
% 1.60/1.79      ((((sk_D) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('clc', [status(thm)], ['76', '77'])).
% 1.60/1.79  thf('79', plain,
% 1.60/1.79      ((~ (v2_funct_1 @ (k5_relat_1 @ k1_xboole_0 @ sk_E)))
% 1.60/1.79         <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('demod', [status(thm)], ['48', '78'])).
% 1.60/1.79  thf('80', plain,
% 1.60/1.79      ((v2_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('81', plain,
% 1.60/1.79      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('82', plain,
% 1.60/1.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('83', plain,
% 1.60/1.79      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.60/1.79         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.60/1.79          | ~ (v1_funct_1 @ X26)
% 1.60/1.79          | ~ (v1_funct_1 @ X29)
% 1.60/1.79          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.60/1.79          | ((k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 1.60/1.79              = (k5_relat_1 @ X26 @ X29)))),
% 1.60/1.79      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.60/1.79  thf('84', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.79         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.60/1.79            = (k5_relat_1 @ sk_D @ X0))
% 1.60/1.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.60/1.79          | ~ (v1_funct_1 @ X0)
% 1.60/1.79          | ~ (v1_funct_1 @ sk_D))),
% 1.60/1.79      inference('sup-', [status(thm)], ['82', '83'])).
% 1.60/1.79  thf('85', plain, ((v1_funct_1 @ sk_D)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('86', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.79         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.60/1.79            = (k5_relat_1 @ sk_D @ X0))
% 1.60/1.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.60/1.79          | ~ (v1_funct_1 @ X0))),
% 1.60/1.79      inference('demod', [status(thm)], ['84', '85'])).
% 1.60/1.79  thf('87', plain,
% 1.60/1.79      ((~ (v1_funct_1 @ sk_E)
% 1.60/1.79        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.60/1.79            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['81', '86'])).
% 1.60/1.79  thf('88', plain, ((v1_funct_1 @ sk_E)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('89', plain,
% 1.60/1.79      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.60/1.79         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.60/1.79      inference('demod', [status(thm)], ['87', '88'])).
% 1.60/1.79  thf('90', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 1.60/1.79      inference('demod', [status(thm)], ['80', '89'])).
% 1.60/1.79  thf('91', plain,
% 1.60/1.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('92', plain,
% 1.60/1.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.60/1.79         ((m1_subset_1 @ (k2_relset_1 @ X9 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))
% 1.60/1.79          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.60/1.79      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 1.60/1.79  thf('93', plain,
% 1.60/1.79      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 1.60/1.79      inference('sup-', [status(thm)], ['91', '92'])).
% 1.60/1.79  thf('94', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i]:
% 1.60/1.79         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.60/1.79      inference('cnf', [status(esa)], [t3_subset])).
% 1.60/1.79  thf('95', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_B)),
% 1.60/1.79      inference('sup-', [status(thm)], ['93', '94'])).
% 1.60/1.79  thf('96', plain,
% 1.60/1.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('97', plain,
% 1.60/1.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.60/1.79         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.60/1.79          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.60/1.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.60/1.79  thf('98', plain,
% 1.60/1.79      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.60/1.79      inference('sup-', [status(thm)], ['96', '97'])).
% 1.60/1.79  thf('99', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 1.60/1.79      inference('demod', [status(thm)], ['95', '98'])).
% 1.60/1.79  thf('100', plain,
% 1.60/1.79      (![X18 : $i, X19 : $i]:
% 1.60/1.79         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.60/1.79  thf('101', plain,
% 1.60/1.79      (![X18 : $i, X19 : $i]:
% 1.60/1.79         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.60/1.79  thf('102', plain,
% 1.60/1.79      (![X18 : $i, X19 : $i]:
% 1.60/1.79         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.60/1.79  thf('103', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.60/1.79         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 1.60/1.79      inference('sup+', [status(thm)], ['101', '102'])).
% 1.60/1.79  thf('104', plain,
% 1.60/1.79      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('105', plain,
% 1.60/1.79      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.60/1.79         (~ (zip_tseitin_0 @ X23 @ X24)
% 1.60/1.79          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 1.60/1.79          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.60/1.79  thf('106', plain,
% 1.60/1.79      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.60/1.79      inference('sup-', [status(thm)], ['104', '105'])).
% 1.60/1.79  thf('107', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i]:
% 1.60/1.79         ((zip_tseitin_0 @ X1 @ X0)
% 1.60/1.79          | ((sk_C) = (X1))
% 1.60/1.79          | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.60/1.79      inference('sup-', [status(thm)], ['103', '106'])).
% 1.60/1.79  thf('108', plain,
% 1.60/1.79      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.60/1.79      inference('split', [status(esa)], ['0'])).
% 1.60/1.79  thf('109', plain,
% 1.60/1.79      ((![X0 : $i, X1 : $i]:
% 1.60/1.79          (((X0) != (k1_xboole_0))
% 1.60/1.79           | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.60/1.79           | (zip_tseitin_0 @ X0 @ X1)))
% 1.60/1.79         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['107', '108'])).
% 1.60/1.79  thf('110', plain,
% 1.60/1.79      ((![X1 : $i]:
% 1.60/1.79          ((zip_tseitin_0 @ k1_xboole_0 @ X1)
% 1.60/1.79           | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)))
% 1.60/1.79         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.60/1.79      inference('simplify', [status(thm)], ['109'])).
% 1.60/1.79  thf('111', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('112', plain,
% 1.60/1.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.60/1.79         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 1.60/1.79          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 1.60/1.79          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.60/1.79  thf('113', plain,
% 1.60/1.79      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.60/1.79        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['111', '112'])).
% 1.60/1.79  thf('114', plain,
% 1.60/1.79      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('115', plain,
% 1.60/1.79      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.60/1.79         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 1.60/1.79          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.60/1.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.60/1.79  thf('116', plain,
% 1.60/1.79      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.60/1.79      inference('sup-', [status(thm)], ['114', '115'])).
% 1.60/1.79  thf('117', plain,
% 1.60/1.79      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_E)))),
% 1.60/1.79      inference('demod', [status(thm)], ['113', '116'])).
% 1.60/1.79  thf('118', plain,
% 1.60/1.79      ((![X0 : $i]:
% 1.60/1.79          ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_B) = (k1_relat_1 @ sk_E))))
% 1.60/1.79         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['110', '117'])).
% 1.60/1.79  thf('119', plain,
% 1.60/1.79      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.79          ((zip_tseitin_0 @ X0 @ X1)
% 1.60/1.79           | (zip_tseitin_0 @ X0 @ X2)
% 1.60/1.79           | ((sk_B) = (k1_relat_1 @ sk_E))))
% 1.60/1.79         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup+', [status(thm)], ['100', '118'])).
% 1.60/1.79  thf('120', plain,
% 1.60/1.79      ((![X0 : $i, X1 : $i]:
% 1.60/1.79          (((sk_B) = (k1_relat_1 @ sk_E)) | (zip_tseitin_0 @ X1 @ X0)))
% 1.60/1.79         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.60/1.79      inference('condensation', [status(thm)], ['119'])).
% 1.60/1.79  thf('121', plain,
% 1.60/1.79      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.60/1.79      inference('sup-', [status(thm)], ['104', '105'])).
% 1.60/1.79  thf('122', plain,
% 1.60/1.79      (((((sk_B) = (k1_relat_1 @ sk_E)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)))
% 1.60/1.79         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['120', '121'])).
% 1.60/1.79  thf('123', plain,
% 1.60/1.79      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_E)))),
% 1.60/1.79      inference('demod', [status(thm)], ['113', '116'])).
% 1.60/1.79  thf('124', plain,
% 1.60/1.79      ((((sk_B) = (k1_relat_1 @ sk_E))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.60/1.79      inference('clc', [status(thm)], ['122', '123'])).
% 1.60/1.79  thf('125', plain,
% 1.60/1.79      (![X7 : $i, X8 : $i]:
% 1.60/1.79         (~ (v1_relat_1 @ X7)
% 1.60/1.79          | ~ (v1_funct_1 @ X7)
% 1.60/1.79          | (v2_funct_1 @ X7)
% 1.60/1.79          | ~ (r1_tarski @ (k2_relat_1 @ X7) @ (k1_relat_1 @ X8))
% 1.60/1.79          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 1.60/1.79          | ~ (v1_funct_1 @ X8)
% 1.60/1.79          | ~ (v1_relat_1 @ X8))),
% 1.60/1.79      inference('cnf', [status(esa)], [t47_funct_1])).
% 1.60/1.79  thf('126', plain,
% 1.60/1.79      ((![X0 : $i]:
% 1.60/1.79          (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B)
% 1.60/1.79           | ~ (v1_relat_1 @ sk_E)
% 1.60/1.79           | ~ (v1_funct_1 @ sk_E)
% 1.60/1.79           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.60/1.79           | (v2_funct_1 @ X0)
% 1.60/1.79           | ~ (v1_funct_1 @ X0)
% 1.60/1.79           | ~ (v1_relat_1 @ X0)))
% 1.60/1.79         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['124', '125'])).
% 1.60/1.79  thf('127', plain, ((v1_relat_1 @ sk_E)),
% 1.60/1.79      inference('demod', [status(thm)], ['34', '35'])).
% 1.60/1.79  thf('128', plain, ((v1_funct_1 @ sk_E)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('129', plain,
% 1.60/1.79      ((![X0 : $i]:
% 1.60/1.79          (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B)
% 1.60/1.79           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.60/1.79           | (v2_funct_1 @ X0)
% 1.60/1.79           | ~ (v1_funct_1 @ X0)
% 1.60/1.79           | ~ (v1_relat_1 @ X0)))
% 1.60/1.79         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.60/1.79      inference('demod', [status(thm)], ['126', '127', '128'])).
% 1.60/1.79  thf('130', plain,
% 1.60/1.79      (((~ (v1_relat_1 @ sk_D)
% 1.60/1.79         | ~ (v1_funct_1 @ sk_D)
% 1.60/1.79         | (v2_funct_1 @ sk_D)
% 1.60/1.79         | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.60/1.79         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['99', '129'])).
% 1.60/1.79  thf('131', plain, ((v1_relat_1 @ sk_D)),
% 1.60/1.79      inference('demod', [status(thm)], ['42', '43'])).
% 1.60/1.79  thf('132', plain, ((v1_funct_1 @ sk_D)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('133', plain,
% 1.60/1.79      ((((v2_funct_1 @ sk_D) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.60/1.79         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.60/1.79      inference('demod', [status(thm)], ['130', '131', '132'])).
% 1.60/1.79  thf('134', plain, (~ (v2_funct_1 @ sk_D)),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('135', plain,
% 1.60/1.79      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 1.60/1.79         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.60/1.79      inference('clc', [status(thm)], ['133', '134'])).
% 1.60/1.79  thf('136', plain, ((((sk_C) = (k1_xboole_0)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['90', '135'])).
% 1.60/1.79  thf('137', plain,
% 1.60/1.79      ((((sk_B) = (k1_xboole_0))) | ~ (((sk_C) = (k1_xboole_0)))),
% 1.60/1.79      inference('split', [status(esa)], ['0'])).
% 1.60/1.79  thf('138', plain, ((((sk_B) = (k1_xboole_0)))),
% 1.60/1.79      inference('sat_resolution*', [status(thm)], ['136', '137'])).
% 1.60/1.79  thf('139', plain, (~ (v2_funct_1 @ (k5_relat_1 @ k1_xboole_0 @ sk_E))),
% 1.60/1.79      inference('simpl_trail', [status(thm)], ['79', '138'])).
% 1.60/1.79  thf('140', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 1.60/1.79      inference('demod', [status(thm)], ['80', '89'])).
% 1.60/1.79  thf('141', plain,
% 1.60/1.79      ((((sk_D) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.60/1.79      inference('clc', [status(thm)], ['76', '77'])).
% 1.60/1.79  thf('142', plain, ((((sk_B) = (k1_xboole_0)))),
% 1.60/1.79      inference('sat_resolution*', [status(thm)], ['136', '137'])).
% 1.60/1.79  thf('143', plain, (((sk_D) = (k1_xboole_0))),
% 1.60/1.79      inference('simpl_trail', [status(thm)], ['141', '142'])).
% 1.60/1.79  thf('144', plain, ((v2_funct_1 @ (k5_relat_1 @ k1_xboole_0 @ sk_E))),
% 1.60/1.79      inference('demod', [status(thm)], ['140', '143'])).
% 1.60/1.79  thf('145', plain, ($false), inference('demod', [status(thm)], ['139', '144'])).
% 1.60/1.79  
% 1.60/1.79  % SZS output end Refutation
% 1.60/1.79  
% 1.60/1.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
