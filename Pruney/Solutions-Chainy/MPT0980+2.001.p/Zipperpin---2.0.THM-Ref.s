%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tYilLdt7of

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:54 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 985 expanded)
%              Number of leaves         :   36 ( 272 expanded)
%              Depth                    :   24
%              Number of atoms          : 1611 (19303 expanded)
%              Number of equality atoms :  165 (1371 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v5_relat_1 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

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

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_C = X1 )
      | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_B
          = ( k1_relat_1 @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_B
          = ( k1_relat_1 @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','28'])).

thf('30',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B
          = ( k1_relat_1 @ sk_E ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['29'])).

thf('31',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('32',plain,
    ( ( ( sk_B
        = ( k1_relat_1 @ sk_E ) )
      | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('34',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['32','33'])).

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

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_funct_1 @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X2 ) @ ( k1_relat_1 @ X3 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B )
        | ~ ( v1_relat_1 @ sk_E )
        | ~ ( v1_funct_1 @ sk_E )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','39','40'])).

thf('42',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_funct_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v5_relat_1 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,
    ( ( v5_relat_1 @ sk_D @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('54',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('56',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('58',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_funct_2 @ sk_E @ k1_xboole_0 @ sk_C )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('66',plain,
    ( ( ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('68',plain,(
    ! [X13: $i] :
      ( zip_tseitin_0 @ X13 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','68'])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('71',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('72',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E )
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','69','72'])).

thf('74',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_funct_1 @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X2 ) @ ( k1_relat_1 @ X3 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_E )
        | ~ ( v1_funct_1 @ sk_E )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['37','38'])).

thf('77',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ~ ( v2_funct_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('87',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('88',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X19 @ k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('91',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','92'])).

thf('94',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('95',plain,
    ( ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('96',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('97',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( sk_D = k1_xboole_0 )
        | ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0 )
          = ( k5_relat_1 @ sk_D @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ sk_D ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( sk_D = k1_xboole_0 )
        | ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0 )
          = ( k5_relat_1 @ sk_D @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ~ ( v1_funct_1 @ sk_E )
      | ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E )
        = ( k5_relat_1 @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('103',plain,
    ( ( ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E )
        = ( k5_relat_1 @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','92'])).

thf('105',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('106',plain,(
    v2_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('109',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( v2_funct_1 @ ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['104','109'])).

thf('111',plain,
    ( ( ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['103','110'])).

thf('112',plain,
    ( ( ( sk_D = k1_xboole_0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('114',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ k1_xboole_0 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','114'])).

thf('116',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('117',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('118',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('121',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('122',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('124',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( ( k1_partfun1 @ sk_A @ k1_xboole_0 @ X2 @ X1 @ k1_xboole_0 @ X0 )
          = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('126',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( ( k1_partfun1 @ sk_A @ k1_xboole_0 @ X2 @ X1 @ k1_xboole_0 @ X0 )
          = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['124','127'])).

thf('129',plain,
    ( ( ~ ( v1_funct_1 @ sk_E )
      | ( ( k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0 @ sk_E )
        = ( k5_relat_1 @ k1_xboole_0 @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['119','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('132',plain,
    ( ( ( k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0 @ sk_E )
      = ( k5_relat_1 @ k1_xboole_0 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( v2_funct_1 @ ( k5_relat_1 @ k1_xboole_0 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['118','132'])).

thf('134',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['115','133'])).

thf('135',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('136',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference(simpl_trail,[status(thm)],['47','136'])).

thf('138',plain,(
    v2_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['139','144'])).

thf('146',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['138','147'])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['137','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tYilLdt7of
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.05/1.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.23  % Solved by: fo/fo7.sh
% 1.05/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.23  % done 1025 iterations in 0.779s
% 1.05/1.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.23  % SZS output start Refutation
% 1.05/1.23  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.23  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.05/1.23  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.05/1.23  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.05/1.23  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.23  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.05/1.23  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.05/1.23  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.05/1.23  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.05/1.23  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.05/1.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.23  thf(sk_D_type, type, sk_D: $i).
% 1.05/1.23  thf(sk_C_type, type, sk_C: $i).
% 1.05/1.23  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.05/1.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.23  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.05/1.23  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.05/1.23  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.05/1.23  thf(sk_E_type, type, sk_E: $i).
% 1.05/1.23  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.05/1.23  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.05/1.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.23  thf(t26_funct_2, conjecture,
% 1.05/1.23    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.23     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.05/1.23         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.23       ( ![E:$i]:
% 1.05/1.23         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.05/1.23             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.05/1.23           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.05/1.23             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.05/1.23               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 1.05/1.23  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.23    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.23        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.05/1.23            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.23          ( ![E:$i]:
% 1.05/1.23            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.05/1.23                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.05/1.23              ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.05/1.23                ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.05/1.23                  ( v2_funct_1 @ D ) ) ) ) ) ) )),
% 1.05/1.23    inference('cnf.neg', [status(esa)], [t26_funct_2])).
% 1.05/1.23  thf('0', plain,
% 1.05/1.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf(cc2_relset_1, axiom,
% 1.05/1.23    (![A:$i,B:$i,C:$i]:
% 1.05/1.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.23       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.05/1.23  thf('1', plain,
% 1.05/1.23      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.05/1.23         ((v5_relat_1 @ X7 @ X9)
% 1.05/1.23          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.05/1.23      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.05/1.23  thf('2', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 1.05/1.23      inference('sup-', [status(thm)], ['0', '1'])).
% 1.05/1.23  thf(d19_relat_1, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ( v1_relat_1 @ B ) =>
% 1.05/1.23       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.05/1.23  thf('3', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         (~ (v5_relat_1 @ X0 @ X1)
% 1.05/1.23          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.05/1.23          | ~ (v1_relat_1 @ X0))),
% 1.05/1.23      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.05/1.23  thf('4', plain,
% 1.05/1.23      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 1.05/1.23      inference('sup-', [status(thm)], ['2', '3'])).
% 1.05/1.23  thf('5', plain,
% 1.05/1.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf(cc1_relset_1, axiom,
% 1.05/1.23    (![A:$i,B:$i,C:$i]:
% 1.05/1.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.23       ( v1_relat_1 @ C ) ))).
% 1.05/1.23  thf('6', plain,
% 1.05/1.23      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.05/1.23         ((v1_relat_1 @ X4)
% 1.05/1.23          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.05/1.23      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.05/1.23  thf('7', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.23      inference('sup-', [status(thm)], ['5', '6'])).
% 1.05/1.23  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 1.05/1.23      inference('demod', [status(thm)], ['4', '7'])).
% 1.05/1.23  thf(d1_funct_2, axiom,
% 1.05/1.23    (![A:$i,B:$i,C:$i]:
% 1.05/1.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.23       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.05/1.23           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.05/1.23             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.05/1.23         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.05/1.23           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.05/1.23             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.05/1.23  thf(zf_stmt_1, axiom,
% 1.05/1.23    (![B:$i,A:$i]:
% 1.05/1.23     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.05/1.23       ( zip_tseitin_0 @ B @ A ) ))).
% 1.05/1.23  thf('9', plain,
% 1.05/1.23      (![X13 : $i, X14 : $i]:
% 1.05/1.23         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.05/1.23  thf('10', plain,
% 1.05/1.23      (![X13 : $i, X14 : $i]:
% 1.05/1.23         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.05/1.23  thf('11', plain,
% 1.05/1.23      (![X13 : $i, X14 : $i]:
% 1.05/1.23         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.05/1.23  thf('12', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.05/1.23         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 1.05/1.23      inference('sup+', [status(thm)], ['10', '11'])).
% 1.05/1.23  thf('13', plain,
% 1.05/1.23      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.05/1.23  thf(zf_stmt_3, axiom,
% 1.05/1.23    (![C:$i,B:$i,A:$i]:
% 1.05/1.23     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.05/1.23       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.05/1.23  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.05/1.23  thf(zf_stmt_5, axiom,
% 1.05/1.23    (![A:$i,B:$i,C:$i]:
% 1.05/1.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.23       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.05/1.23         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.05/1.23           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.05/1.23             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.05/1.23  thf('14', plain,
% 1.05/1.23      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.23         (~ (zip_tseitin_0 @ X18 @ X19)
% 1.05/1.23          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 1.05/1.23          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.05/1.23  thf('15', plain,
% 1.05/1.23      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.05/1.23      inference('sup-', [status(thm)], ['13', '14'])).
% 1.05/1.23  thf('16', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((zip_tseitin_0 @ X1 @ X0)
% 1.05/1.23          | ((sk_C) = (X1))
% 1.05/1.23          | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.05/1.23      inference('sup-', [status(thm)], ['12', '15'])).
% 1.05/1.23  thf('17', plain, ((((sk_C) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('18', plain,
% 1.05/1.23      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.05/1.23      inference('split', [status(esa)], ['17'])).
% 1.05/1.23  thf('19', plain,
% 1.05/1.23      ((![X0 : $i, X1 : $i]:
% 1.05/1.23          (((X0) != (k1_xboole_0))
% 1.05/1.23           | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.05/1.23           | (zip_tseitin_0 @ X0 @ X1)))
% 1.05/1.23         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['16', '18'])).
% 1.05/1.23  thf('20', plain,
% 1.05/1.23      ((![X1 : $i]:
% 1.05/1.23          ((zip_tseitin_0 @ k1_xboole_0 @ X1)
% 1.05/1.23           | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)))
% 1.05/1.23         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.05/1.23      inference('simplify', [status(thm)], ['19'])).
% 1.05/1.23  thf('21', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('22', plain,
% 1.05/1.23      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.05/1.23         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 1.05/1.23          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 1.05/1.23          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.05/1.23  thf('23', plain,
% 1.05/1.23      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.05/1.23        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['21', '22'])).
% 1.05/1.23  thf('24', plain,
% 1.05/1.23      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf(redefinition_k1_relset_1, axiom,
% 1.05/1.23    (![A:$i,B:$i,C:$i]:
% 1.05/1.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.23       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.05/1.23  thf('25', plain,
% 1.05/1.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.05/1.23         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 1.05/1.23          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.05/1.23      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.05/1.23  thf('26', plain,
% 1.05/1.23      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.05/1.23      inference('sup-', [status(thm)], ['24', '25'])).
% 1.05/1.23  thf('27', plain,
% 1.05/1.23      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_E)))),
% 1.05/1.23      inference('demod', [status(thm)], ['23', '26'])).
% 1.05/1.23  thf('28', plain,
% 1.05/1.23      ((![X0 : $i]:
% 1.05/1.23          ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_B) = (k1_relat_1 @ sk_E))))
% 1.05/1.23         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['20', '27'])).
% 1.05/1.23  thf('29', plain,
% 1.05/1.23      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.23          ((zip_tseitin_0 @ X0 @ X1)
% 1.05/1.23           | (zip_tseitin_0 @ X0 @ X2)
% 1.05/1.23           | ((sk_B) = (k1_relat_1 @ sk_E))))
% 1.05/1.23         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['9', '28'])).
% 1.05/1.23  thf('30', plain,
% 1.05/1.23      ((![X0 : $i, X1 : $i]:
% 1.05/1.23          (((sk_B) = (k1_relat_1 @ sk_E)) | (zip_tseitin_0 @ X1 @ X0)))
% 1.05/1.23         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.05/1.23      inference('condensation', [status(thm)], ['29'])).
% 1.05/1.23  thf('31', plain,
% 1.05/1.23      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.05/1.23      inference('sup-', [status(thm)], ['13', '14'])).
% 1.05/1.23  thf('32', plain,
% 1.05/1.23      (((((sk_B) = (k1_relat_1 @ sk_E)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)))
% 1.05/1.23         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['30', '31'])).
% 1.05/1.23  thf('33', plain,
% 1.05/1.23      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_E)))),
% 1.05/1.23      inference('demod', [status(thm)], ['23', '26'])).
% 1.05/1.23  thf('34', plain,
% 1.05/1.23      ((((sk_B) = (k1_relat_1 @ sk_E))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.05/1.23      inference('clc', [status(thm)], ['32', '33'])).
% 1.05/1.23  thf(t47_funct_1, axiom,
% 1.05/1.23    (![A:$i]:
% 1.05/1.23     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.05/1.23       ( ![B:$i]:
% 1.05/1.23         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.05/1.23           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.05/1.23               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 1.05/1.23             ( v2_funct_1 @ B ) ) ) ) ))).
% 1.05/1.23  thf('35', plain,
% 1.05/1.23      (![X2 : $i, X3 : $i]:
% 1.05/1.23         (~ (v1_relat_1 @ X2)
% 1.05/1.23          | ~ (v1_funct_1 @ X2)
% 1.05/1.23          | (v2_funct_1 @ X2)
% 1.05/1.23          | ~ (r1_tarski @ (k2_relat_1 @ X2) @ (k1_relat_1 @ X3))
% 1.05/1.23          | ~ (v2_funct_1 @ (k5_relat_1 @ X2 @ X3))
% 1.05/1.23          | ~ (v1_funct_1 @ X3)
% 1.05/1.23          | ~ (v1_relat_1 @ X3))),
% 1.05/1.23      inference('cnf', [status(esa)], [t47_funct_1])).
% 1.05/1.23  thf('36', plain,
% 1.05/1.23      ((![X0 : $i]:
% 1.05/1.23          (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B)
% 1.05/1.23           | ~ (v1_relat_1 @ sk_E)
% 1.05/1.23           | ~ (v1_funct_1 @ sk_E)
% 1.05/1.23           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.05/1.23           | (v2_funct_1 @ X0)
% 1.05/1.23           | ~ (v1_funct_1 @ X0)
% 1.05/1.23           | ~ (v1_relat_1 @ X0)))
% 1.05/1.23         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['34', '35'])).
% 1.05/1.23  thf('37', plain,
% 1.05/1.23      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('38', plain,
% 1.05/1.23      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.05/1.23         ((v1_relat_1 @ X4)
% 1.05/1.23          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.05/1.23      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.05/1.23  thf('39', plain, ((v1_relat_1 @ sk_E)),
% 1.05/1.23      inference('sup-', [status(thm)], ['37', '38'])).
% 1.05/1.23  thf('40', plain, ((v1_funct_1 @ sk_E)),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('41', plain,
% 1.05/1.23      ((![X0 : $i]:
% 1.05/1.23          (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B)
% 1.05/1.23           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.05/1.23           | (v2_funct_1 @ X0)
% 1.05/1.23           | ~ (v1_funct_1 @ X0)
% 1.05/1.23           | ~ (v1_relat_1 @ X0)))
% 1.05/1.23         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['36', '39', '40'])).
% 1.05/1.23  thf('42', plain,
% 1.05/1.23      (((~ (v1_relat_1 @ sk_D)
% 1.05/1.23         | ~ (v1_funct_1 @ sk_D)
% 1.05/1.23         | (v2_funct_1 @ sk_D)
% 1.05/1.23         | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.05/1.23         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['8', '41'])).
% 1.05/1.23  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.23      inference('sup-', [status(thm)], ['5', '6'])).
% 1.05/1.23  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('45', plain,
% 1.05/1.23      ((((v2_funct_1 @ sk_D) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.05/1.23         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['42', '43', '44'])).
% 1.05/1.23  thf('46', plain, (~ (v2_funct_1 @ sk_D)),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('47', plain,
% 1.05/1.23      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 1.05/1.23         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.05/1.23      inference('clc', [status(thm)], ['45', '46'])).
% 1.05/1.23  thf('48', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('split', [status(esa)], ['17'])).
% 1.05/1.23  thf('49', plain,
% 1.05/1.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('50', plain,
% 1.05/1.23      (((m1_subset_1 @ sk_D @ 
% 1.05/1.23         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['48', '49'])).
% 1.05/1.23  thf('51', plain,
% 1.05/1.23      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.05/1.23         ((v5_relat_1 @ X7 @ X9)
% 1.05/1.23          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.05/1.23      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.05/1.23  thf('52', plain,
% 1.05/1.23      (((v5_relat_1 @ sk_D @ k1_xboole_0)) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['50', '51'])).
% 1.05/1.23  thf('53', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         (~ (v5_relat_1 @ X0 @ X1)
% 1.05/1.23          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.05/1.23          | ~ (v1_relat_1 @ X0))),
% 1.05/1.23      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.05/1.23  thf('54', plain,
% 1.05/1.23      (((~ (v1_relat_1 @ sk_D)
% 1.05/1.23         | (r1_tarski @ (k2_relat_1 @ sk_D) @ k1_xboole_0)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['52', '53'])).
% 1.05/1.23  thf('55', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.23      inference('sup-', [status(thm)], ['5', '6'])).
% 1.05/1.23  thf('56', plain,
% 1.05/1.23      (((r1_tarski @ (k2_relat_1 @ sk_D) @ k1_xboole_0))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['54', '55'])).
% 1.05/1.23  thf('57', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('split', [status(esa)], ['17'])).
% 1.05/1.23  thf('58', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('59', plain,
% 1.05/1.23      (((v1_funct_2 @ sk_E @ k1_xboole_0 @ sk_C))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['57', '58'])).
% 1.05/1.23  thf('60', plain,
% 1.05/1.23      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.05/1.23         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 1.05/1.23          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 1.05/1.23          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.05/1.23  thf('61', plain,
% 1.05/1.23      (((~ (zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0)
% 1.05/1.23         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E))))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['59', '60'])).
% 1.05/1.23  thf('62', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('split', [status(esa)], ['17'])).
% 1.05/1.23  thf('63', plain,
% 1.05/1.23      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('64', plain,
% 1.05/1.23      (((m1_subset_1 @ sk_E @ 
% 1.05/1.23         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['62', '63'])).
% 1.05/1.23  thf('65', plain,
% 1.05/1.23      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.23         (~ (zip_tseitin_0 @ X18 @ X19)
% 1.05/1.23          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 1.05/1.23          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.05/1.23  thf('66', plain,
% 1.05/1.23      ((((zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0)
% 1.05/1.23         | ~ (zip_tseitin_0 @ sk_C @ k1_xboole_0)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['64', '65'])).
% 1.05/1.23  thf('67', plain,
% 1.05/1.23      (![X13 : $i, X14 : $i]:
% 1.05/1.23         ((zip_tseitin_0 @ X13 @ X14) | ((X14) != (k1_xboole_0)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.05/1.23  thf('68', plain, (![X13 : $i]: (zip_tseitin_0 @ X13 @ k1_xboole_0)),
% 1.05/1.23      inference('simplify', [status(thm)], ['67'])).
% 1.05/1.23  thf('69', plain,
% 1.05/1.23      (((zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['66', '68'])).
% 1.05/1.23  thf('70', plain,
% 1.05/1.23      (((m1_subset_1 @ sk_E @ 
% 1.05/1.23         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['62', '63'])).
% 1.05/1.23  thf('71', plain,
% 1.05/1.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.05/1.23         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 1.05/1.23          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.05/1.23      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.05/1.23  thf('72', plain,
% 1.05/1.23      ((((k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_E) = (k1_relat_1 @ sk_E)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['70', '71'])).
% 1.05/1.23  thf('73', plain,
% 1.05/1.23      ((((k1_xboole_0) = (k1_relat_1 @ sk_E))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['61', '69', '72'])).
% 1.05/1.23  thf('74', plain,
% 1.05/1.23      (![X2 : $i, X3 : $i]:
% 1.05/1.23         (~ (v1_relat_1 @ X2)
% 1.05/1.23          | ~ (v1_funct_1 @ X2)
% 1.05/1.23          | (v2_funct_1 @ X2)
% 1.05/1.23          | ~ (r1_tarski @ (k2_relat_1 @ X2) @ (k1_relat_1 @ X3))
% 1.05/1.23          | ~ (v2_funct_1 @ (k5_relat_1 @ X2 @ X3))
% 1.05/1.23          | ~ (v1_funct_1 @ X3)
% 1.05/1.23          | ~ (v1_relat_1 @ X3))),
% 1.05/1.23      inference('cnf', [status(esa)], [t47_funct_1])).
% 1.05/1.23  thf('75', plain,
% 1.05/1.23      ((![X0 : $i]:
% 1.05/1.23          (~ (r1_tarski @ (k2_relat_1 @ X0) @ k1_xboole_0)
% 1.05/1.23           | ~ (v1_relat_1 @ sk_E)
% 1.05/1.23           | ~ (v1_funct_1 @ sk_E)
% 1.05/1.23           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.05/1.23           | (v2_funct_1 @ X0)
% 1.05/1.23           | ~ (v1_funct_1 @ X0)
% 1.05/1.23           | ~ (v1_relat_1 @ X0)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['73', '74'])).
% 1.05/1.23  thf('76', plain, ((v1_relat_1 @ sk_E)),
% 1.05/1.23      inference('sup-', [status(thm)], ['37', '38'])).
% 1.05/1.23  thf('77', plain, ((v1_funct_1 @ sk_E)),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('78', plain,
% 1.05/1.23      ((![X0 : $i]:
% 1.05/1.23          (~ (r1_tarski @ (k2_relat_1 @ X0) @ k1_xboole_0)
% 1.05/1.23           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_E))
% 1.05/1.23           | (v2_funct_1 @ X0)
% 1.05/1.23           | ~ (v1_funct_1 @ X0)
% 1.05/1.23           | ~ (v1_relat_1 @ X0)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.05/1.23  thf('79', plain,
% 1.05/1.23      (((~ (v1_relat_1 @ sk_D)
% 1.05/1.23         | ~ (v1_funct_1 @ sk_D)
% 1.05/1.23         | (v2_funct_1 @ sk_D)
% 1.05/1.23         | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['56', '78'])).
% 1.05/1.23  thf('80', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.23      inference('sup-', [status(thm)], ['5', '6'])).
% 1.05/1.23  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('82', plain,
% 1.05/1.23      ((((v2_funct_1 @ sk_D) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['79', '80', '81'])).
% 1.05/1.23  thf('83', plain, (~ (v2_funct_1 @ sk_D)),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('84', plain,
% 1.05/1.23      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('clc', [status(thm)], ['82', '83'])).
% 1.05/1.23  thf('85', plain,
% 1.05/1.23      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('86', plain,
% 1.05/1.23      (((m1_subset_1 @ sk_D @ 
% 1.05/1.23         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['48', '49'])).
% 1.05/1.23  thf('87', plain,
% 1.05/1.23      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.23         (((X18) != (k1_xboole_0))
% 1.05/1.23          | ((X19) = (k1_xboole_0))
% 1.05/1.23          | ((X20) = (k1_xboole_0))
% 1.05/1.23          | ~ (v1_funct_2 @ X20 @ X19 @ X18)
% 1.05/1.23          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.05/1.23  thf('88', plain,
% 1.05/1.23      (![X19 : $i, X20 : $i]:
% 1.05/1.23         (~ (m1_subset_1 @ X20 @ 
% 1.05/1.23             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ k1_xboole_0)))
% 1.05/1.23          | ~ (v1_funct_2 @ X20 @ X19 @ k1_xboole_0)
% 1.05/1.23          | ((X20) = (k1_xboole_0))
% 1.05/1.23          | ((X19) = (k1_xboole_0)))),
% 1.05/1.23      inference('simplify', [status(thm)], ['87'])).
% 1.05/1.23  thf('89', plain,
% 1.05/1.23      (((((sk_A) = (k1_xboole_0))
% 1.05/1.23         | ((sk_D) = (k1_xboole_0))
% 1.05/1.23         | ~ (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['86', '88'])).
% 1.05/1.23  thf('90', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('split', [status(esa)], ['17'])).
% 1.05/1.23  thf('91', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('92', plain,
% 1.05/1.23      (((v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['90', '91'])).
% 1.05/1.23  thf('93', plain,
% 1.05/1.23      (((((sk_A) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0))))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['89', '92'])).
% 1.05/1.23  thf('94', plain,
% 1.05/1.23      (((m1_subset_1 @ sk_D @ 
% 1.05/1.23         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['48', '49'])).
% 1.05/1.23  thf('95', plain,
% 1.05/1.23      ((((m1_subset_1 @ sk_D @ 
% 1.05/1.23          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))
% 1.05/1.23         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['93', '94'])).
% 1.05/1.23  thf(redefinition_k1_partfun1, axiom,
% 1.05/1.23    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.05/1.23     ( ( ( v1_funct_1 @ E ) & 
% 1.05/1.23         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.05/1.23         ( v1_funct_1 @ F ) & 
% 1.05/1.23         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.05/1.23       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.05/1.23  thf('96', plain,
% 1.05/1.23      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.05/1.23         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.05/1.23          | ~ (v1_funct_1 @ X21)
% 1.05/1.23          | ~ (v1_funct_1 @ X24)
% 1.05/1.23          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.05/1.23          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 1.05/1.23              = (k5_relat_1 @ X21 @ X24)))),
% 1.05/1.23      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.05/1.23  thf('97', plain,
% 1.05/1.23      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.23          (((sk_D) = (k1_xboole_0))
% 1.05/1.23           | ((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0)
% 1.05/1.23               = (k5_relat_1 @ sk_D @ X0))
% 1.05/1.23           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.05/1.23           | ~ (v1_funct_1 @ X0)
% 1.05/1.23           | ~ (v1_funct_1 @ sk_D)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['95', '96'])).
% 1.05/1.23  thf('98', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('99', plain,
% 1.05/1.23      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.23          (((sk_D) = (k1_xboole_0))
% 1.05/1.23           | ((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0)
% 1.05/1.23               = (k5_relat_1 @ sk_D @ X0))
% 1.05/1.23           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.05/1.23           | ~ (v1_funct_1 @ X0)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['97', '98'])).
% 1.05/1.23  thf('100', plain,
% 1.05/1.23      (((~ (v1_funct_1 @ sk_E)
% 1.05/1.23         | ((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ 
% 1.05/1.23             sk_E) = (k5_relat_1 @ sk_D @ sk_E))
% 1.05/1.23         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['85', '99'])).
% 1.05/1.23  thf('101', plain, ((v1_funct_1 @ sk_E)),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('102', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('split', [status(esa)], ['17'])).
% 1.05/1.23  thf('103', plain,
% 1.05/1.23      (((((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ 
% 1.05/1.23           sk_D @ sk_E) = (k5_relat_1 @ sk_D @ sk_E))
% 1.05/1.23         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['100', '101', '102'])).
% 1.05/1.23  thf('104', plain,
% 1.05/1.23      (((((sk_A) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0))))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['89', '92'])).
% 1.05/1.23  thf('105', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('split', [status(esa)], ['17'])).
% 1.05/1.23  thf('106', plain,
% 1.05/1.23      ((v2_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('107', plain,
% 1.05/1.23      (((v2_funct_1 @ 
% 1.05/1.23         (k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['105', '106'])).
% 1.05/1.23  thf('108', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('split', [status(esa)], ['17'])).
% 1.05/1.23  thf('109', plain,
% 1.05/1.23      (((v2_funct_1 @ 
% 1.05/1.23         (k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['107', '108'])).
% 1.05/1.23  thf('110', plain,
% 1.05/1.23      ((((v2_funct_1 @ 
% 1.05/1.23          (k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ 
% 1.05/1.23           sk_D @ sk_E))
% 1.05/1.23         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['104', '109'])).
% 1.05/1.23  thf('111', plain,
% 1.05/1.23      ((((v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))
% 1.05/1.23         | ((sk_D) = (k1_xboole_0))
% 1.05/1.23         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['103', '110'])).
% 1.05/1.23  thf('112', plain,
% 1.05/1.23      (((((sk_D) = (k1_xboole_0)) | (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('simplify', [status(thm)], ['111'])).
% 1.05/1.23  thf('113', plain,
% 1.05/1.23      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('clc', [status(thm)], ['82', '83'])).
% 1.05/1.23  thf('114', plain,
% 1.05/1.23      ((((sk_D) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('clc', [status(thm)], ['112', '113'])).
% 1.05/1.23  thf('115', plain,
% 1.05/1.23      ((~ (v2_funct_1 @ (k5_relat_1 @ k1_xboole_0 @ sk_E)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['84', '114'])).
% 1.05/1.23  thf('116', plain,
% 1.05/1.23      (((v2_funct_1 @ 
% 1.05/1.23         (k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['107', '108'])).
% 1.05/1.23  thf('117', plain,
% 1.05/1.23      ((((sk_D) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('clc', [status(thm)], ['112', '113'])).
% 1.05/1.23  thf('118', plain,
% 1.05/1.23      (((v2_funct_1 @ 
% 1.05/1.23         (k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ 
% 1.05/1.23          k1_xboole_0 @ sk_E)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['116', '117'])).
% 1.05/1.23  thf('119', plain,
% 1.05/1.23      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('120', plain,
% 1.05/1.23      (((m1_subset_1 @ sk_D @ 
% 1.05/1.23         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['48', '49'])).
% 1.05/1.23  thf('121', plain,
% 1.05/1.23      ((((sk_D) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('clc', [status(thm)], ['112', '113'])).
% 1.05/1.23  thf('122', plain,
% 1.05/1.23      (((m1_subset_1 @ k1_xboole_0 @ 
% 1.05/1.23         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['120', '121'])).
% 1.05/1.23  thf('123', plain,
% 1.05/1.23      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.05/1.23         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.05/1.23          | ~ (v1_funct_1 @ X21)
% 1.05/1.23          | ~ (v1_funct_1 @ X24)
% 1.05/1.23          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.05/1.23          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 1.05/1.23              = (k5_relat_1 @ X21 @ X24)))),
% 1.05/1.23      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.05/1.23  thf('124', plain,
% 1.05/1.23      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.23          (((k1_partfun1 @ sk_A @ k1_xboole_0 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 1.05/1.23             = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.05/1.23           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.05/1.23           | ~ (v1_funct_1 @ X0)
% 1.05/1.23           | ~ (v1_funct_1 @ k1_xboole_0)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['122', '123'])).
% 1.05/1.23  thf('125', plain,
% 1.05/1.23      ((((sk_D) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('clc', [status(thm)], ['112', '113'])).
% 1.05/1.23  thf('126', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('127', plain,
% 1.05/1.23      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['125', '126'])).
% 1.05/1.23  thf('128', plain,
% 1.05/1.23      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.23          (((k1_partfun1 @ sk_A @ k1_xboole_0 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 1.05/1.23             = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.05/1.23           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.05/1.23           | ~ (v1_funct_1 @ X0)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['124', '127'])).
% 1.05/1.23  thf('129', plain,
% 1.05/1.23      (((~ (v1_funct_1 @ sk_E)
% 1.05/1.23         | ((k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0 @ 
% 1.05/1.23             sk_E) = (k5_relat_1 @ k1_xboole_0 @ sk_E))))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['119', '128'])).
% 1.05/1.23  thf('130', plain, ((v1_funct_1 @ sk_E)),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('131', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('split', [status(esa)], ['17'])).
% 1.05/1.23  thf('132', plain,
% 1.05/1.23      ((((k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ 
% 1.05/1.23          k1_xboole_0 @ sk_E) = (k5_relat_1 @ k1_xboole_0 @ sk_E)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['129', '130', '131'])).
% 1.05/1.23  thf('133', plain,
% 1.05/1.23      (((v2_funct_1 @ (k5_relat_1 @ k1_xboole_0 @ sk_E)))
% 1.05/1.23         <= ((((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('demod', [status(thm)], ['118', '132'])).
% 1.05/1.23  thf('134', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('demod', [status(thm)], ['115', '133'])).
% 1.05/1.23  thf('135', plain,
% 1.05/1.23      (~ (((sk_C) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('split', [status(esa)], ['17'])).
% 1.05/1.23  thf('136', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 1.05/1.23      inference('sat_resolution*', [status(thm)], ['134', '135'])).
% 1.05/1.23  thf('137', plain, (~ (v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 1.05/1.23      inference('simpl_trail', [status(thm)], ['47', '136'])).
% 1.05/1.23  thf('138', plain,
% 1.05/1.23      ((v2_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('139', plain,
% 1.05/1.23      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('140', plain,
% 1.05/1.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('141', plain,
% 1.05/1.23      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.05/1.23         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.05/1.23          | ~ (v1_funct_1 @ X21)
% 1.05/1.23          | ~ (v1_funct_1 @ X24)
% 1.05/1.23          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.05/1.23          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 1.05/1.23              = (k5_relat_1 @ X21 @ X24)))),
% 1.05/1.23      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.05/1.23  thf('142', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.23         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.05/1.23            = (k5_relat_1 @ sk_D @ X0))
% 1.05/1.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.05/1.23          | ~ (v1_funct_1 @ X0)
% 1.05/1.23          | ~ (v1_funct_1 @ sk_D))),
% 1.05/1.23      inference('sup-', [status(thm)], ['140', '141'])).
% 1.05/1.23  thf('143', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('144', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.23         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.05/1.23            = (k5_relat_1 @ sk_D @ X0))
% 1.05/1.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.05/1.23          | ~ (v1_funct_1 @ X0))),
% 1.05/1.23      inference('demod', [status(thm)], ['142', '143'])).
% 1.05/1.23  thf('145', plain,
% 1.05/1.23      ((~ (v1_funct_1 @ sk_E)
% 1.05/1.23        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.05/1.23            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['139', '144'])).
% 1.05/1.23  thf('146', plain, ((v1_funct_1 @ sk_E)),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('147', plain,
% 1.05/1.23      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.05/1.23         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.05/1.23      inference('demod', [status(thm)], ['145', '146'])).
% 1.05/1.23  thf('148', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 1.05/1.23      inference('demod', [status(thm)], ['138', '147'])).
% 1.05/1.23  thf('149', plain, ($false), inference('demod', [status(thm)], ['137', '148'])).
% 1.05/1.23  
% 1.05/1.23  % SZS output end Refutation
% 1.05/1.23  
% 1.10/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
