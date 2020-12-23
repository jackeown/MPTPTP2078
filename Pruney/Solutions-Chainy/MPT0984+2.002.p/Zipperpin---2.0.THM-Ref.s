%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7zTjq9DThf

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:26 EST 2020

% Result     : Theorem 3.84s
% Output     : Refutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 761 expanded)
%              Number of leaves         :   33 ( 223 expanded)
%              Depth                    :   19
%              Number of atoms          : 1341 (16870 expanded)
%              Number of equality atoms :  139 (1234 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t30_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
              & ( ( k2_relset_1 @ A @ B @ D )
                = B ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( ( v2_funct_1 @ D )
                & ( v2_funct_1 @ E ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                & ( ( k2_relset_1 @ A @ B @ D )
                  = B ) )
             => ( ( ( C = k1_xboole_0 )
                  & ( B != k1_xboole_0 ) )
                | ( ( v2_funct_1 @ D )
                  & ( v2_funct_1 @ E ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_funct_2])).

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_1 @ sk_E )
   <= ~ ( v2_funct_1 @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

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

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_C = X1 )
      | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_B
          = ( k1_relat_1 @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_B
          = ( k1_relat_1 @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','21'])).

thf('23',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B
          = ( k1_relat_1 @ sk_E ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['22'])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('25',plain,
    ( ( ( sk_B
        = ( k1_relat_1 @ sk_E ) )
      | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('27',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    v2_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 )
        = ( k5_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['28','37'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_E ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('42',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('43',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('46',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_E ) )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['40','43','44','49','50','53'])).

thf('55',plain,
    ( ( ( sk_B != sk_B )
      | ( v2_funct_1 @ sk_D ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','54'])).

thf('56',plain,
    ( ( v2_funct_1 @ sk_D )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ~ ( v2_funct_1 @ sk_D )
   <= ~ ( v2_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ( v2_funct_1 @ sk_D )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('60',plain,(
    v2_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('63',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 )
        = ( k5_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('69',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( ( k1_partfun1 @ sk_A @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0 )
          = ( k5_relat_1 @ sk_D @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ sk_D ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( ( k1_partfun1 @ sk_A @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0 )
          = ( k5_relat_1 @ sk_D @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ~ ( v1_funct_1 @ sk_E )
      | ( ( k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E )
        = ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('75',plain,
    ( ( ( k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('78',plain,
    ( ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k2_relat_1 @ sk_D )
       != ( k1_relat_1 @ sk_E ) )
      | ( v2_funct_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['41','42'])).

thf('80',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['47','48'])).

thf('82',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('83',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('84',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v1_funct_2 @ sk_E @ k1_xboole_0 @ sk_C )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('87',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('89',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('92',plain,
    ( ( ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('94',plain,(
    ! [X11: $i] :
      ( zip_tseitin_0 @ X11 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','94'])).

thf('96',plain,
    ( ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('97',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('98',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E )
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','95','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['51','52'])).

thf('102',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_funct_1 @ sk_D ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79','80','81','82','99','100','101'])).

thf('103',plain,
    ( ( v2_funct_1 @ sk_D )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ~ ( v2_funct_1 @ sk_D )
   <= ~ ( v2_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('105',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('107',plain,
    ( ~ ( v2_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('108',plain,(
    ~ ( v2_funct_1 @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['58','105','106','107'])).

thf('109',plain,(
    ~ ( v2_funct_1 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['1','108'])).

thf('110',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('112',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_E ) )
    | ( v2_funct_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['41','42'])).

thf('114',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['47','48'])).

thf('116',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['51','52'])).

thf('118',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_E ) )
    | ( v2_funct_1 @ sk_E ) ),
    inference(demod,[status(thm)],['112','113','114','115','116','117'])).

thf('119',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('120',plain,
    ( ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','75'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('122',plain,
    ( ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k2_relat_1 @ sk_D )
       != ( k1_relat_1 @ sk_E ) )
      | ( v2_funct_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['41','42'])).

thf('124',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['47','48'])).

thf('126',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('127',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','95','98'])).

thf('128',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['51','52'])).

thf('130',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_funct_1 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','123','124','125','126','127','128','129'])).

thf('131',plain,
    ( ( v2_funct_1 @ sk_E )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ~ ( v2_funct_1 @ sk_E )
   <= ~ ( v2_funct_1 @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('133',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( v2_funct_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['58','105','107','133','106'])).

thf('135',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['119','134'])).

thf('136',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_E ) ),
    inference(demod,[status(thm)],['118','135'])).

thf('137',plain,(
    v2_funct_1 @ sk_E ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['109','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7zTjq9DThf
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.84/4.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.84/4.04  % Solved by: fo/fo7.sh
% 3.84/4.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.84/4.04  % done 3301 iterations in 3.576s
% 3.84/4.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.84/4.04  % SZS output start Refutation
% 3.84/4.04  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.84/4.04  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.84/4.04  thf(sk_B_type, type, sk_B: $i).
% 3.84/4.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.84/4.04  thf(sk_D_type, type, sk_D: $i).
% 3.84/4.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.84/4.04  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.84/4.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.84/4.04  thf(sk_C_type, type, sk_C: $i).
% 3.84/4.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.84/4.04  thf(sk_E_type, type, sk_E: $i).
% 3.84/4.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.84/4.04  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.84/4.04  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.84/4.04  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.84/4.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.84/4.04  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.84/4.04  thf(sk_A_type, type, sk_A: $i).
% 3.84/4.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.84/4.04  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.84/4.04  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.84/4.04  thf(t30_funct_2, conjecture,
% 3.84/4.04    (![A:$i,B:$i,C:$i,D:$i]:
% 3.84/4.04     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.84/4.04         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.84/4.04       ( ![E:$i]:
% 3.84/4.04         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.84/4.04             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.84/4.04           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 3.84/4.04               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 3.84/4.04             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.84/4.04               ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ) ) ) ) ))).
% 3.84/4.04  thf(zf_stmt_0, negated_conjecture,
% 3.84/4.04    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.84/4.04        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.84/4.04            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.84/4.04          ( ![E:$i]:
% 3.84/4.04            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.84/4.04                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.84/4.04              ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 3.84/4.04                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 3.84/4.04                ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.84/4.04                  ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ) ) ) ) ) )),
% 3.84/4.04    inference('cnf.neg', [status(esa)], [t30_funct_2])).
% 3.84/4.04  thf('0', plain, ((~ (v2_funct_1 @ sk_D) | ~ (v2_funct_1 @ sk_E))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('1', plain, ((~ (v2_funct_1 @ sk_E)) <= (~ ((v2_funct_1 @ sk_E)))),
% 3.84/4.04      inference('split', [status(esa)], ['0'])).
% 3.84/4.04  thf(d1_funct_2, axiom,
% 3.84/4.04    (![A:$i,B:$i,C:$i]:
% 3.84/4.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.84/4.04       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.84/4.04           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.84/4.04             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.84/4.04         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.84/4.04           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.84/4.04             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.84/4.04  thf(zf_stmt_1, axiom,
% 3.84/4.04    (![B:$i,A:$i]:
% 3.84/4.04     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.84/4.04       ( zip_tseitin_0 @ B @ A ) ))).
% 3.84/4.04  thf('2', plain,
% 3.84/4.04      (![X11 : $i, X12 : $i]:
% 3.84/4.04         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.84/4.04  thf('3', plain,
% 3.84/4.04      (![X11 : $i, X12 : $i]:
% 3.84/4.04         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.84/4.04  thf('4', plain,
% 3.84/4.04      (![X11 : $i, X12 : $i]:
% 3.84/4.04         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.84/4.04  thf('5', plain,
% 3.84/4.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.84/4.04         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 3.84/4.04      inference('sup+', [status(thm)], ['3', '4'])).
% 3.84/4.04  thf('6', plain,
% 3.84/4.04      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.84/4.04  thf(zf_stmt_3, axiom,
% 3.84/4.04    (![C:$i,B:$i,A:$i]:
% 3.84/4.04     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.84/4.04       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.84/4.04  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.84/4.04  thf(zf_stmt_5, axiom,
% 3.84/4.04    (![A:$i,B:$i,C:$i]:
% 3.84/4.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.84/4.04       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.84/4.04         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.84/4.04           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.84/4.04             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.84/4.04  thf('7', plain,
% 3.84/4.04      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.84/4.04         (~ (zip_tseitin_0 @ X16 @ X17)
% 3.84/4.04          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 3.84/4.04          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.84/4.04  thf('8', plain,
% 3.84/4.04      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 3.84/4.04      inference('sup-', [status(thm)], ['6', '7'])).
% 3.84/4.04  thf('9', plain,
% 3.84/4.04      (![X0 : $i, X1 : $i]:
% 3.84/4.04         ((zip_tseitin_0 @ X1 @ X0)
% 3.84/4.04          | ((sk_C) = (X1))
% 3.84/4.04          | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 3.84/4.04      inference('sup-', [status(thm)], ['5', '8'])).
% 3.84/4.04  thf('10', plain, ((((sk_C) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('11', plain,
% 3.84/4.04      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 3.84/4.04      inference('split', [status(esa)], ['10'])).
% 3.84/4.04  thf('12', plain,
% 3.84/4.04      ((![X0 : $i, X1 : $i]:
% 3.84/4.04          (((X0) != (k1_xboole_0))
% 3.84/4.04           | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 3.84/4.04           | (zip_tseitin_0 @ X0 @ X1)))
% 3.84/4.04         <= (~ (((sk_C) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup-', [status(thm)], ['9', '11'])).
% 3.84/4.04  thf('13', plain,
% 3.84/4.04      ((![X1 : $i]:
% 3.84/4.04          ((zip_tseitin_0 @ k1_xboole_0 @ X1)
% 3.84/4.04           | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)))
% 3.84/4.04         <= (~ (((sk_C) = (k1_xboole_0))))),
% 3.84/4.04      inference('simplify', [status(thm)], ['12'])).
% 3.84/4.04  thf('14', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('15', plain,
% 3.84/4.04      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.84/4.04         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 3.84/4.04          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 3.84/4.04          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.84/4.04  thf('16', plain,
% 3.84/4.04      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 3.84/4.04        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 3.84/4.04      inference('sup-', [status(thm)], ['14', '15'])).
% 3.84/4.04  thf('17', plain,
% 3.84/4.04      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf(redefinition_k1_relset_1, axiom,
% 3.84/4.04    (![A:$i,B:$i,C:$i]:
% 3.84/4.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.84/4.04       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.84/4.04  thf('18', plain,
% 3.84/4.04      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.84/4.04         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 3.84/4.04          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 3.84/4.04      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.84/4.04  thf('19', plain,
% 3.84/4.04      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 3.84/4.04      inference('sup-', [status(thm)], ['17', '18'])).
% 3.84/4.04  thf('20', plain,
% 3.84/4.04      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_E)))),
% 3.84/4.04      inference('demod', [status(thm)], ['16', '19'])).
% 3.84/4.04  thf('21', plain,
% 3.84/4.04      ((![X0 : $i]:
% 3.84/4.04          ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_B) = (k1_relat_1 @ sk_E))))
% 3.84/4.04         <= (~ (((sk_C) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup-', [status(thm)], ['13', '20'])).
% 3.84/4.04  thf('22', plain,
% 3.84/4.04      ((![X0 : $i, X1 : $i, X2 : $i]:
% 3.84/4.04          ((zip_tseitin_0 @ X0 @ X1)
% 3.84/4.04           | (zip_tseitin_0 @ X0 @ X2)
% 3.84/4.04           | ((sk_B) = (k1_relat_1 @ sk_E))))
% 3.84/4.04         <= (~ (((sk_C) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup+', [status(thm)], ['2', '21'])).
% 3.84/4.04  thf('23', plain,
% 3.84/4.04      ((![X0 : $i, X1 : $i]:
% 3.84/4.04          (((sk_B) = (k1_relat_1 @ sk_E)) | (zip_tseitin_0 @ X1 @ X0)))
% 3.84/4.04         <= (~ (((sk_C) = (k1_xboole_0))))),
% 3.84/4.04      inference('condensation', [status(thm)], ['22'])).
% 3.84/4.04  thf('24', plain,
% 3.84/4.04      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 3.84/4.04      inference('sup-', [status(thm)], ['6', '7'])).
% 3.84/4.04  thf('25', plain,
% 3.84/4.04      (((((sk_B) = (k1_relat_1 @ sk_E)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)))
% 3.84/4.04         <= (~ (((sk_C) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup-', [status(thm)], ['23', '24'])).
% 3.84/4.04  thf('26', plain,
% 3.84/4.04      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_E)))),
% 3.84/4.04      inference('demod', [status(thm)], ['16', '19'])).
% 3.84/4.04  thf('27', plain,
% 3.84/4.04      ((((sk_B) = (k1_relat_1 @ sk_E))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 3.84/4.04      inference('clc', [status(thm)], ['25', '26'])).
% 3.84/4.04  thf('28', plain,
% 3.84/4.04      ((v2_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('29', plain,
% 3.84/4.04      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('30', plain,
% 3.84/4.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf(redefinition_k1_partfun1, axiom,
% 3.84/4.04    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.84/4.04     ( ( ( v1_funct_1 @ E ) & 
% 3.84/4.04         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.84/4.04         ( v1_funct_1 @ F ) & 
% 3.84/4.04         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.84/4.04       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.84/4.04  thf('31', plain,
% 3.84/4.04      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 3.84/4.04         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 3.84/4.04          | ~ (v1_funct_1 @ X19)
% 3.84/4.04          | ~ (v1_funct_1 @ X22)
% 3.84/4.04          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 3.84/4.04          | ((k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22)
% 3.84/4.04              = (k5_relat_1 @ X19 @ X22)))),
% 3.84/4.04      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.84/4.04  thf('32', plain,
% 3.84/4.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.84/4.04         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 3.84/4.04            = (k5_relat_1 @ sk_D @ X0))
% 3.84/4.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.84/4.04          | ~ (v1_funct_1 @ X0)
% 3.84/4.04          | ~ (v1_funct_1 @ sk_D))),
% 3.84/4.04      inference('sup-', [status(thm)], ['30', '31'])).
% 3.84/4.04  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('34', plain,
% 3.84/4.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.84/4.04         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 3.84/4.04            = (k5_relat_1 @ sk_D @ X0))
% 3.84/4.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.84/4.04          | ~ (v1_funct_1 @ X0))),
% 3.84/4.04      inference('demod', [status(thm)], ['32', '33'])).
% 3.84/4.04  thf('35', plain,
% 3.84/4.04      ((~ (v1_funct_1 @ sk_E)
% 3.84/4.04        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 3.84/4.04            = (k5_relat_1 @ sk_D @ sk_E)))),
% 3.84/4.04      inference('sup-', [status(thm)], ['29', '34'])).
% 3.84/4.04  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('37', plain,
% 3.84/4.04      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 3.84/4.04         = (k5_relat_1 @ sk_D @ sk_E))),
% 3.84/4.04      inference('demod', [status(thm)], ['35', '36'])).
% 3.84/4.04  thf('38', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 3.84/4.04      inference('demod', [status(thm)], ['28', '37'])).
% 3.84/4.04  thf(t48_funct_1, axiom,
% 3.84/4.04    (![A:$i]:
% 3.84/4.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.84/4.04       ( ![B:$i]:
% 3.84/4.04         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.84/4.04           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 3.84/4.04               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 3.84/4.04             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 3.84/4.04  thf('39', plain,
% 3.84/4.04      (![X0 : $i, X1 : $i]:
% 3.84/4.04         (~ (v1_relat_1 @ X0)
% 3.84/4.04          | ~ (v1_funct_1 @ X0)
% 3.84/4.04          | (v2_funct_1 @ X0)
% 3.84/4.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ X1))
% 3.84/4.04          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 3.84/4.04          | ~ (v1_funct_1 @ X1)
% 3.84/4.04          | ~ (v1_relat_1 @ X1))),
% 3.84/4.04      inference('cnf', [status(esa)], [t48_funct_1])).
% 3.84/4.04  thf('40', plain,
% 3.84/4.04      ((~ (v1_relat_1 @ sk_E)
% 3.84/4.04        | ~ (v1_funct_1 @ sk_E)
% 3.84/4.04        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_E))
% 3.84/4.04        | (v2_funct_1 @ sk_D)
% 3.84/4.04        | ~ (v1_funct_1 @ sk_D)
% 3.84/4.04        | ~ (v1_relat_1 @ sk_D))),
% 3.84/4.04      inference('sup-', [status(thm)], ['38', '39'])).
% 3.84/4.04  thf('41', plain,
% 3.84/4.04      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf(cc1_relset_1, axiom,
% 3.84/4.04    (![A:$i,B:$i,C:$i]:
% 3.84/4.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.84/4.04       ( v1_relat_1 @ C ) ))).
% 3.84/4.04  thf('42', plain,
% 3.84/4.04      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.84/4.04         ((v1_relat_1 @ X2)
% 3.84/4.04          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 3.84/4.04      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.84/4.04  thf('43', plain, ((v1_relat_1 @ sk_E)),
% 3.84/4.04      inference('sup-', [status(thm)], ['41', '42'])).
% 3.84/4.04  thf('44', plain, ((v1_funct_1 @ sk_E)),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('45', plain,
% 3.84/4.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf(redefinition_k2_relset_1, axiom,
% 3.84/4.04    (![A:$i,B:$i,C:$i]:
% 3.84/4.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.84/4.04       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.84/4.04  thf('46', plain,
% 3.84/4.04      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.84/4.04         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 3.84/4.04          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 3.84/4.04      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.84/4.04  thf('47', plain,
% 3.84/4.04      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.84/4.04      inference('sup-', [status(thm)], ['45', '46'])).
% 3.84/4.04  thf('48', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('49', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 3.84/4.04      inference('sup+', [status(thm)], ['47', '48'])).
% 3.84/4.04  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('51', plain,
% 3.84/4.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('52', plain,
% 3.84/4.04      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.84/4.04         ((v1_relat_1 @ X2)
% 3.84/4.04          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 3.84/4.04      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.84/4.04  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 3.84/4.04      inference('sup-', [status(thm)], ['51', '52'])).
% 3.84/4.04  thf('54', plain, ((((sk_B) != (k1_relat_1 @ sk_E)) | (v2_funct_1 @ sk_D))),
% 3.84/4.04      inference('demod', [status(thm)], ['40', '43', '44', '49', '50', '53'])).
% 3.84/4.04  thf('55', plain,
% 3.84/4.04      (((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D)))
% 3.84/4.04         <= (~ (((sk_C) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup-', [status(thm)], ['27', '54'])).
% 3.84/4.04  thf('56', plain, (((v2_funct_1 @ sk_D)) <= (~ (((sk_C) = (k1_xboole_0))))),
% 3.84/4.04      inference('simplify', [status(thm)], ['55'])).
% 3.84/4.04  thf('57', plain, ((~ (v2_funct_1 @ sk_D)) <= (~ ((v2_funct_1 @ sk_D)))),
% 3.84/4.04      inference('split', [status(esa)], ['0'])).
% 3.84/4.04  thf('58', plain, (((v2_funct_1 @ sk_D)) | (((sk_C) = (k1_xboole_0)))),
% 3.84/4.04      inference('sup-', [status(thm)], ['56', '57'])).
% 3.84/4.04  thf('59', plain,
% 3.84/4.04      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('split', [status(esa)], ['10'])).
% 3.84/4.04  thf('60', plain,
% 3.84/4.04      ((v2_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('61', plain,
% 3.84/4.04      (((v2_funct_1 @ 
% 3.84/4.04         (k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E)))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup+', [status(thm)], ['59', '60'])).
% 3.84/4.04  thf('62', plain,
% 3.84/4.04      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('split', [status(esa)], ['10'])).
% 3.84/4.04  thf('63', plain,
% 3.84/4.04      (((v2_funct_1 @ 
% 3.84/4.04         (k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E)))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('demod', [status(thm)], ['61', '62'])).
% 3.84/4.04  thf('64', plain,
% 3.84/4.04      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('65', plain,
% 3.84/4.04      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('split', [status(esa)], ['10'])).
% 3.84/4.04  thf('66', plain,
% 3.84/4.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('67', plain,
% 3.84/4.04      (((m1_subset_1 @ sk_D @ 
% 3.84/4.04         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup+', [status(thm)], ['65', '66'])).
% 3.84/4.04  thf('68', plain,
% 3.84/4.04      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 3.84/4.04         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 3.84/4.04          | ~ (v1_funct_1 @ X19)
% 3.84/4.04          | ~ (v1_funct_1 @ X22)
% 3.84/4.04          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 3.84/4.04          | ((k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22)
% 3.84/4.04              = (k5_relat_1 @ X19 @ X22)))),
% 3.84/4.04      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.84/4.04  thf('69', plain,
% 3.84/4.04      ((![X0 : $i, X1 : $i, X2 : $i]:
% 3.84/4.04          (((k1_partfun1 @ sk_A @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0)
% 3.84/4.04             = (k5_relat_1 @ sk_D @ X0))
% 3.84/4.04           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.84/4.04           | ~ (v1_funct_1 @ X0)
% 3.84/4.04           | ~ (v1_funct_1 @ sk_D)))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup-', [status(thm)], ['67', '68'])).
% 3.84/4.04  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('71', plain,
% 3.84/4.04      ((![X0 : $i, X1 : $i, X2 : $i]:
% 3.84/4.04          (((k1_partfun1 @ sk_A @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0)
% 3.84/4.04             = (k5_relat_1 @ sk_D @ X0))
% 3.84/4.04           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.84/4.04           | ~ (v1_funct_1 @ X0)))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('demod', [status(thm)], ['69', '70'])).
% 3.84/4.04  thf('72', plain,
% 3.84/4.04      (((~ (v1_funct_1 @ sk_E)
% 3.84/4.04         | ((k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E)
% 3.84/4.04             = (k5_relat_1 @ sk_D @ sk_E))))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup-', [status(thm)], ['64', '71'])).
% 3.84/4.04  thf('73', plain, ((v1_funct_1 @ sk_E)),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('74', plain,
% 3.84/4.04      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('split', [status(esa)], ['10'])).
% 3.84/4.04  thf('75', plain,
% 3.84/4.04      ((((k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E)
% 3.84/4.04          = (k5_relat_1 @ sk_D @ sk_E)))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('demod', [status(thm)], ['72', '73', '74'])).
% 3.84/4.04  thf('76', plain,
% 3.84/4.04      (((v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('demod', [status(thm)], ['63', '75'])).
% 3.84/4.04  thf('77', plain,
% 3.84/4.04      (![X0 : $i, X1 : $i]:
% 3.84/4.04         (~ (v1_relat_1 @ X0)
% 3.84/4.04          | ~ (v1_funct_1 @ X0)
% 3.84/4.04          | (v2_funct_1 @ X0)
% 3.84/4.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ X1))
% 3.84/4.04          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 3.84/4.04          | ~ (v1_funct_1 @ X1)
% 3.84/4.04          | ~ (v1_relat_1 @ X1))),
% 3.84/4.04      inference('cnf', [status(esa)], [t48_funct_1])).
% 3.84/4.04  thf('78', plain,
% 3.84/4.04      (((~ (v1_relat_1 @ sk_E)
% 3.84/4.04         | ~ (v1_funct_1 @ sk_E)
% 3.84/4.04         | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_E))
% 3.84/4.04         | (v2_funct_1 @ sk_D)
% 3.84/4.04         | ~ (v1_funct_1 @ sk_D)
% 3.84/4.04         | ~ (v1_relat_1 @ sk_D))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup-', [status(thm)], ['76', '77'])).
% 3.84/4.04  thf('79', plain, ((v1_relat_1 @ sk_E)),
% 3.84/4.04      inference('sup-', [status(thm)], ['41', '42'])).
% 3.84/4.04  thf('80', plain, ((v1_funct_1 @ sk_E)),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('81', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 3.84/4.04      inference('sup+', [status(thm)], ['47', '48'])).
% 3.84/4.04  thf('82', plain,
% 3.84/4.04      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('split', [status(esa)], ['10'])).
% 3.84/4.04  thf('83', plain,
% 3.84/4.04      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('split', [status(esa)], ['10'])).
% 3.84/4.04  thf('84', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('85', plain,
% 3.84/4.04      (((v1_funct_2 @ sk_E @ k1_xboole_0 @ sk_C))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup+', [status(thm)], ['83', '84'])).
% 3.84/4.04  thf('86', plain,
% 3.84/4.04      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.84/4.04         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 3.84/4.04          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 3.84/4.04          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.84/4.04  thf('87', plain,
% 3.84/4.04      (((~ (zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0)
% 3.84/4.04         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E))))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup-', [status(thm)], ['85', '86'])).
% 3.84/4.04  thf('88', plain,
% 3.84/4.04      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('split', [status(esa)], ['10'])).
% 3.84/4.04  thf('89', plain,
% 3.84/4.04      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('90', plain,
% 3.84/4.04      (((m1_subset_1 @ sk_E @ 
% 3.84/4.04         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup+', [status(thm)], ['88', '89'])).
% 3.84/4.04  thf('91', plain,
% 3.84/4.04      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.84/4.04         (~ (zip_tseitin_0 @ X16 @ X17)
% 3.84/4.04          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 3.84/4.04          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.84/4.04  thf('92', plain,
% 3.84/4.04      ((((zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0)
% 3.84/4.04         | ~ (zip_tseitin_0 @ sk_C @ k1_xboole_0)))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup-', [status(thm)], ['90', '91'])).
% 3.84/4.04  thf('93', plain,
% 3.84/4.04      (![X11 : $i, X12 : $i]:
% 3.84/4.04         ((zip_tseitin_0 @ X11 @ X12) | ((X12) != (k1_xboole_0)))),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.84/4.04  thf('94', plain, (![X11 : $i]: (zip_tseitin_0 @ X11 @ k1_xboole_0)),
% 3.84/4.04      inference('simplify', [status(thm)], ['93'])).
% 3.84/4.04  thf('95', plain,
% 3.84/4.04      (((zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('demod', [status(thm)], ['92', '94'])).
% 3.84/4.04  thf('96', plain,
% 3.84/4.04      (((m1_subset_1 @ sk_E @ 
% 3.84/4.04         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup+', [status(thm)], ['88', '89'])).
% 3.84/4.04  thf('97', plain,
% 3.84/4.04      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.84/4.04         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 3.84/4.04          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 3.84/4.04      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.84/4.04  thf('98', plain,
% 3.84/4.04      ((((k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E) = (k1_relat_1 @ sk_E)))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup-', [status(thm)], ['96', '97'])).
% 3.84/4.04  thf('99', plain,
% 3.84/4.04      ((((k1_xboole_0) = (k1_relat_1 @ sk_E))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('demod', [status(thm)], ['87', '95', '98'])).
% 3.84/4.04  thf('100', plain, ((v1_funct_1 @ sk_D)),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('101', plain, ((v1_relat_1 @ sk_D)),
% 3.84/4.04      inference('sup-', [status(thm)], ['51', '52'])).
% 3.84/4.04  thf('102', plain,
% 3.84/4.04      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_funct_1 @ sk_D)))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('demod', [status(thm)],
% 3.84/4.04                ['78', '79', '80', '81', '82', '99', '100', '101'])).
% 3.84/4.04  thf('103', plain, (((v2_funct_1 @ sk_D)) <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('simplify', [status(thm)], ['102'])).
% 3.84/4.04  thf('104', plain, ((~ (v2_funct_1 @ sk_D)) <= (~ ((v2_funct_1 @ sk_D)))),
% 3.84/4.04      inference('split', [status(esa)], ['0'])).
% 3.84/4.04  thf('105', plain, (~ (((sk_B) = (k1_xboole_0))) | ((v2_funct_1 @ sk_D))),
% 3.84/4.04      inference('sup-', [status(thm)], ['103', '104'])).
% 3.84/4.04  thf('106', plain,
% 3.84/4.04      (~ (((sk_C) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0)))),
% 3.84/4.04      inference('split', [status(esa)], ['10'])).
% 3.84/4.04  thf('107', plain, (~ ((v2_funct_1 @ sk_E)) | ~ ((v2_funct_1 @ sk_D))),
% 3.84/4.04      inference('split', [status(esa)], ['0'])).
% 3.84/4.04  thf('108', plain, (~ ((v2_funct_1 @ sk_E))),
% 3.84/4.04      inference('sat_resolution*', [status(thm)], ['58', '105', '106', '107'])).
% 3.84/4.04  thf('109', plain, (~ (v2_funct_1 @ sk_E)),
% 3.84/4.04      inference('simpl_trail', [status(thm)], ['1', '108'])).
% 3.84/4.04  thf('110', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 3.84/4.04      inference('demod', [status(thm)], ['28', '37'])).
% 3.84/4.04  thf('111', plain,
% 3.84/4.04      (![X0 : $i, X1 : $i]:
% 3.84/4.04         (~ (v1_relat_1 @ X0)
% 3.84/4.04          | ~ (v1_funct_1 @ X0)
% 3.84/4.04          | (v2_funct_1 @ X1)
% 3.84/4.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ X1))
% 3.84/4.04          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 3.84/4.04          | ~ (v1_funct_1 @ X1)
% 3.84/4.04          | ~ (v1_relat_1 @ X1))),
% 3.84/4.04      inference('cnf', [status(esa)], [t48_funct_1])).
% 3.84/4.04  thf('112', plain,
% 3.84/4.04      ((~ (v1_relat_1 @ sk_E)
% 3.84/4.04        | ~ (v1_funct_1 @ sk_E)
% 3.84/4.04        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_E))
% 3.84/4.04        | (v2_funct_1 @ sk_E)
% 3.84/4.04        | ~ (v1_funct_1 @ sk_D)
% 3.84/4.04        | ~ (v1_relat_1 @ sk_D))),
% 3.84/4.04      inference('sup-', [status(thm)], ['110', '111'])).
% 3.84/4.04  thf('113', plain, ((v1_relat_1 @ sk_E)),
% 3.84/4.04      inference('sup-', [status(thm)], ['41', '42'])).
% 3.84/4.04  thf('114', plain, ((v1_funct_1 @ sk_E)),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('115', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 3.84/4.04      inference('sup+', [status(thm)], ['47', '48'])).
% 3.84/4.04  thf('116', plain, ((v1_funct_1 @ sk_D)),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('117', plain, ((v1_relat_1 @ sk_D)),
% 3.84/4.04      inference('sup-', [status(thm)], ['51', '52'])).
% 3.84/4.04  thf('118', plain, ((((sk_B) != (k1_relat_1 @ sk_E)) | (v2_funct_1 @ sk_E))),
% 3.84/4.04      inference('demod', [status(thm)],
% 3.84/4.04                ['112', '113', '114', '115', '116', '117'])).
% 3.84/4.04  thf('119', plain,
% 3.84/4.04      ((((sk_B) = (k1_relat_1 @ sk_E))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 3.84/4.04      inference('clc', [status(thm)], ['25', '26'])).
% 3.84/4.04  thf('120', plain,
% 3.84/4.04      (((v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('demod', [status(thm)], ['63', '75'])).
% 3.84/4.04  thf('121', plain,
% 3.84/4.04      (![X0 : $i, X1 : $i]:
% 3.84/4.04         (~ (v1_relat_1 @ X0)
% 3.84/4.04          | ~ (v1_funct_1 @ X0)
% 3.84/4.04          | (v2_funct_1 @ X1)
% 3.84/4.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ X1))
% 3.84/4.04          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 3.84/4.04          | ~ (v1_funct_1 @ X1)
% 3.84/4.04          | ~ (v1_relat_1 @ X1))),
% 3.84/4.04      inference('cnf', [status(esa)], [t48_funct_1])).
% 3.84/4.04  thf('122', plain,
% 3.84/4.04      (((~ (v1_relat_1 @ sk_E)
% 3.84/4.04         | ~ (v1_funct_1 @ sk_E)
% 3.84/4.04         | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_E))
% 3.84/4.04         | (v2_funct_1 @ sk_E)
% 3.84/4.04         | ~ (v1_funct_1 @ sk_D)
% 3.84/4.04         | ~ (v1_relat_1 @ sk_D))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('sup-', [status(thm)], ['120', '121'])).
% 3.84/4.04  thf('123', plain, ((v1_relat_1 @ sk_E)),
% 3.84/4.04      inference('sup-', [status(thm)], ['41', '42'])).
% 3.84/4.04  thf('124', plain, ((v1_funct_1 @ sk_E)),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('125', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 3.84/4.04      inference('sup+', [status(thm)], ['47', '48'])).
% 3.84/4.04  thf('126', plain,
% 3.84/4.04      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('split', [status(esa)], ['10'])).
% 3.84/4.04  thf('127', plain,
% 3.84/4.04      ((((k1_xboole_0) = (k1_relat_1 @ sk_E))) <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('demod', [status(thm)], ['87', '95', '98'])).
% 3.84/4.04  thf('128', plain, ((v1_funct_1 @ sk_D)),
% 3.84/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.84/4.04  thf('129', plain, ((v1_relat_1 @ sk_D)),
% 3.84/4.04      inference('sup-', [status(thm)], ['51', '52'])).
% 3.84/4.04  thf('130', plain,
% 3.84/4.04      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_funct_1 @ sk_E)))
% 3.84/4.04         <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('demod', [status(thm)],
% 3.84/4.04                ['122', '123', '124', '125', '126', '127', '128', '129'])).
% 3.84/4.04  thf('131', plain, (((v2_funct_1 @ sk_E)) <= ((((sk_B) = (k1_xboole_0))))),
% 3.84/4.04      inference('simplify', [status(thm)], ['130'])).
% 3.84/4.04  thf('132', plain, ((~ (v2_funct_1 @ sk_E)) <= (~ ((v2_funct_1 @ sk_E)))),
% 3.84/4.04      inference('split', [status(esa)], ['0'])).
% 3.84/4.04  thf('133', plain, (~ (((sk_B) = (k1_xboole_0))) | ((v2_funct_1 @ sk_E))),
% 3.84/4.04      inference('sup-', [status(thm)], ['131', '132'])).
% 3.84/4.04  thf('134', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 3.84/4.04      inference('sat_resolution*', [status(thm)],
% 3.84/4.04                ['58', '105', '107', '133', '106'])).
% 3.84/4.04  thf('135', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 3.84/4.04      inference('simpl_trail', [status(thm)], ['119', '134'])).
% 3.84/4.04  thf('136', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_E))),
% 3.84/4.04      inference('demod', [status(thm)], ['118', '135'])).
% 3.84/4.04  thf('137', plain, ((v2_funct_1 @ sk_E)),
% 3.84/4.04      inference('simplify', [status(thm)], ['136'])).
% 3.84/4.04  thf('138', plain, ($false), inference('demod', [status(thm)], ['109', '137'])).
% 3.84/4.04  
% 3.84/4.04  % SZS output end Refutation
% 3.84/4.04  
% 3.84/4.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
