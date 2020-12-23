%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bbayh8mO4E

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:58 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 379 expanded)
%              Number of leaves         :   51 ( 136 expanded)
%              Depth                    :   13
%              Number of atoms          : 1301 (6775 expanded)
%              Number of equality atoms :   89 ( 424 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t28_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C )
              & ( v2_funct_1 @ E ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ B @ D )
                = B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C )
                & ( v2_funct_1 @ E ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ B @ D )
                  = B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
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

thf('1',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('5',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ( ( k10_relat_1 @ X16 @ ( k9_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ sk_B ) )
      = ( k1_relat_1 @ sk_E ) )
    | ~ ( v2_funct_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['13','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v4_relat_1 @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_E )
      = ( k9_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_E )
    = ( k9_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('38',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_E ) @ sk_C )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k10_relat_1 @ X11 @ X12 )
        = ( k10_relat_1 @ X11 @ ( k3_xboole_0 @ ( k2_relat_1 @ X11 ) @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ X0 )
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_E @ sk_B ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('47',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('48',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('49',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_E @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_E )
    = ( k9_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_E ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['40','52'])).

thf('54',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('55',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('58',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['18','31','53','54','55','56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('66',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('69',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ( ( k10_relat_1 @ X16 @ ( k9_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('72',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,
    ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('76',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k9_relat_1 @ X9 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('79',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('84',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k4_relset_1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['81','86'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('88',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('89',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
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

thf('93',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ( ( k1_partfun1 @ X50 @ X51 @ X53 @ X54 @ X49 @ X52 )
        = ( k5_relat_1 @ X49 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['90','99'])).

thf('101',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['89','100'])).

thf('102',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['76','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['64','65'])).

thf('104',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('105',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['75','105'])).

thf('107',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['58','106'])).

thf('108',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('111',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['108','111'])).

thf('113',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['107','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bbayh8mO4E
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:39:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.06/2.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.06/2.28  % Solved by: fo/fo7.sh
% 2.06/2.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.06/2.28  % done 761 iterations in 1.801s
% 2.06/2.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.06/2.28  % SZS output start Refutation
% 2.06/2.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.06/2.28  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.06/2.28  thf(sk_B_type, type, sk_B: $i).
% 2.06/2.28  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.06/2.28  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.06/2.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.06/2.28  thf(sk_A_type, type, sk_A: $i).
% 2.06/2.28  thf(sk_E_type, type, sk_E: $i).
% 2.06/2.28  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.06/2.28  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.06/2.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.06/2.28  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.06/2.28  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.06/2.28  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.06/2.28  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.06/2.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.06/2.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.06/2.28  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.06/2.28  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.06/2.28  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.06/2.28  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.06/2.28  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 2.06/2.28  thf(sk_C_type, type, sk_C: $i).
% 2.06/2.28  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.06/2.28  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.06/2.28  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.06/2.28  thf(sk_D_type, type, sk_D: $i).
% 2.06/2.28  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.06/2.28  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.06/2.28  thf(t28_funct_2, conjecture,
% 2.06/2.28    (![A:$i,B:$i,C:$i,D:$i]:
% 2.06/2.28     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.06/2.28         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.06/2.28       ( ![E:$i]:
% 2.06/2.28         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.06/2.28             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.06/2.28           ( ( ( ( k2_relset_1 @
% 2.06/2.28                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.06/2.28                 ( C ) ) & 
% 2.06/2.28               ( v2_funct_1 @ E ) ) =>
% 2.06/2.28             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.06/2.28               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 2.06/2.28  thf(zf_stmt_0, negated_conjecture,
% 2.06/2.28    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.06/2.28        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.06/2.28            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.06/2.28          ( ![E:$i]:
% 2.06/2.28            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.06/2.28                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.06/2.28              ( ( ( ( k2_relset_1 @
% 2.06/2.28                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.06/2.28                    ( C ) ) & 
% 2.06/2.28                  ( v2_funct_1 @ E ) ) =>
% 2.06/2.28                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.06/2.28                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 2.06/2.28    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 2.06/2.28  thf('0', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf(d1_funct_2, axiom,
% 2.06/2.28    (![A:$i,B:$i,C:$i]:
% 2.06/2.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.06/2.28       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.06/2.28           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.06/2.28             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.06/2.28         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.06/2.28           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.06/2.28             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.06/2.28  thf(zf_stmt_1, axiom,
% 2.06/2.28    (![C:$i,B:$i,A:$i]:
% 2.06/2.28     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.06/2.28       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.06/2.28  thf('1', plain,
% 2.06/2.28      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.06/2.28         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 2.06/2.28          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 2.06/2.28          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.06/2.28  thf('2', plain,
% 2.06/2.28      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 2.06/2.28        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['0', '1'])).
% 2.06/2.28  thf(zf_stmt_2, axiom,
% 2.06/2.28    (![B:$i,A:$i]:
% 2.06/2.28     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.06/2.28       ( zip_tseitin_0 @ B @ A ) ))).
% 2.06/2.28  thf('3', plain,
% 2.06/2.28      (![X41 : $i, X42 : $i]:
% 2.06/2.28         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.06/2.28  thf('4', plain,
% 2.06/2.28      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.06/2.28  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.06/2.28  thf(zf_stmt_5, axiom,
% 2.06/2.28    (![A:$i,B:$i,C:$i]:
% 2.06/2.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.06/2.28       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.06/2.28         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.06/2.28           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.06/2.28             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.06/2.28  thf('5', plain,
% 2.06/2.28      (![X46 : $i, X47 : $i, X48 : $i]:
% 2.06/2.28         (~ (zip_tseitin_0 @ X46 @ X47)
% 2.06/2.28          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 2.06/2.28          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.06/2.28  thf('6', plain,
% 2.06/2.28      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 2.06/2.28      inference('sup-', [status(thm)], ['4', '5'])).
% 2.06/2.28  thf('7', plain,
% 2.06/2.28      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 2.06/2.28      inference('sup-', [status(thm)], ['3', '6'])).
% 2.06/2.28  thf('8', plain, (((sk_C) != (k1_xboole_0))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('9', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 2.06/2.28      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 2.06/2.28  thf('10', plain,
% 2.06/2.28      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf(redefinition_k1_relset_1, axiom,
% 2.06/2.28    (![A:$i,B:$i,C:$i]:
% 2.06/2.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.06/2.28       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.06/2.28  thf('11', plain,
% 2.06/2.28      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.06/2.28         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 2.06/2.28          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 2.06/2.28      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.06/2.28  thf('12', plain,
% 2.06/2.28      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 2.06/2.28      inference('sup-', [status(thm)], ['10', '11'])).
% 2.06/2.28  thf('13', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.06/2.28      inference('demod', [status(thm)], ['2', '9', '12'])).
% 2.06/2.28  thf(d10_xboole_0, axiom,
% 2.06/2.28    (![A:$i,B:$i]:
% 2.06/2.28     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.06/2.28  thf('14', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.06/2.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.06/2.28  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.06/2.28      inference('simplify', [status(thm)], ['14'])).
% 2.06/2.28  thf(t164_funct_1, axiom,
% 2.06/2.28    (![A:$i,B:$i]:
% 2.06/2.28     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.06/2.28       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 2.06/2.28         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 2.06/2.28  thf('16', plain,
% 2.06/2.28      (![X15 : $i, X16 : $i]:
% 2.06/2.28         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 2.06/2.28          | ~ (v2_funct_1 @ X16)
% 2.06/2.28          | ((k10_relat_1 @ X16 @ (k9_relat_1 @ X16 @ X15)) = (X15))
% 2.06/2.28          | ~ (v1_funct_1 @ X16)
% 2.06/2.28          | ~ (v1_relat_1 @ X16))),
% 2.06/2.28      inference('cnf', [status(esa)], [t164_funct_1])).
% 2.06/2.28  thf('17', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (~ (v1_relat_1 @ X0)
% 2.06/2.28          | ~ (v1_funct_1 @ X0)
% 2.06/2.28          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 2.06/2.28              = (k1_relat_1 @ X0))
% 2.06/2.28          | ~ (v2_funct_1 @ X0))),
% 2.06/2.28      inference('sup-', [status(thm)], ['15', '16'])).
% 2.06/2.28  thf('18', plain,
% 2.06/2.28      ((((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ sk_B))
% 2.06/2.28          = (k1_relat_1 @ sk_E))
% 2.06/2.28        | ~ (v2_funct_1 @ sk_E)
% 2.06/2.28        | ~ (v1_funct_1 @ sk_E)
% 2.06/2.28        | ~ (v1_relat_1 @ sk_E))),
% 2.06/2.28      inference('sup+', [status(thm)], ['13', '17'])).
% 2.06/2.28  thf('19', plain,
% 2.06/2.28      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf(cc2_relset_1, axiom,
% 2.06/2.28    (![A:$i,B:$i,C:$i]:
% 2.06/2.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.06/2.28       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.06/2.28  thf('20', plain,
% 2.06/2.28      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.06/2.28         ((v4_relat_1 @ X20 @ X21)
% 2.06/2.28          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.06/2.28      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.06/2.28  thf('21', plain, ((v4_relat_1 @ sk_E @ sk_B)),
% 2.06/2.28      inference('sup-', [status(thm)], ['19', '20'])).
% 2.06/2.28  thf(t209_relat_1, axiom,
% 2.06/2.28    (![A:$i,B:$i]:
% 2.06/2.28     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.06/2.28       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 2.06/2.28  thf('22', plain,
% 2.06/2.28      (![X13 : $i, X14 : $i]:
% 2.06/2.28         (((X13) = (k7_relat_1 @ X13 @ X14))
% 2.06/2.28          | ~ (v4_relat_1 @ X13 @ X14)
% 2.06/2.28          | ~ (v1_relat_1 @ X13))),
% 2.06/2.28      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.06/2.28  thf('23', plain,
% 2.06/2.28      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_B)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['21', '22'])).
% 2.06/2.28  thf('24', plain,
% 2.06/2.28      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf(cc1_relset_1, axiom,
% 2.06/2.28    (![A:$i,B:$i,C:$i]:
% 2.06/2.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.06/2.28       ( v1_relat_1 @ C ) ))).
% 2.06/2.28  thf('25', plain,
% 2.06/2.28      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.06/2.28         ((v1_relat_1 @ X17)
% 2.06/2.28          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 2.06/2.28      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.06/2.28  thf('26', plain, ((v1_relat_1 @ sk_E)),
% 2.06/2.28      inference('sup-', [status(thm)], ['24', '25'])).
% 2.06/2.28  thf('27', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 2.06/2.28      inference('demod', [status(thm)], ['23', '26'])).
% 2.06/2.28  thf(t148_relat_1, axiom,
% 2.06/2.28    (![A:$i,B:$i]:
% 2.06/2.28     ( ( v1_relat_1 @ B ) =>
% 2.06/2.28       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.06/2.28  thf('28', plain,
% 2.06/2.28      (![X7 : $i, X8 : $i]:
% 2.06/2.28         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 2.06/2.28          | ~ (v1_relat_1 @ X7))),
% 2.06/2.28      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.06/2.28  thf('29', plain,
% 2.06/2.28      ((((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))
% 2.06/2.28        | ~ (v1_relat_1 @ sk_E))),
% 2.06/2.28      inference('sup+', [status(thm)], ['27', '28'])).
% 2.06/2.28  thf('30', plain, ((v1_relat_1 @ sk_E)),
% 2.06/2.28      inference('sup-', [status(thm)], ['24', '25'])).
% 2.06/2.28  thf('31', plain, (((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))),
% 2.06/2.28      inference('demod', [status(thm)], ['29', '30'])).
% 2.06/2.28  thf('32', plain,
% 2.06/2.28      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('33', plain,
% 2.06/2.28      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.06/2.28         ((v5_relat_1 @ X20 @ X22)
% 2.06/2.28          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.06/2.28      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.06/2.28  thf('34', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 2.06/2.28      inference('sup-', [status(thm)], ['32', '33'])).
% 2.06/2.28  thf(d19_relat_1, axiom,
% 2.06/2.28    (![A:$i,B:$i]:
% 2.06/2.28     ( ( v1_relat_1 @ B ) =>
% 2.06/2.28       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.06/2.28  thf('35', plain,
% 2.06/2.28      (![X5 : $i, X6 : $i]:
% 2.06/2.28         (~ (v5_relat_1 @ X5 @ X6)
% 2.06/2.28          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 2.06/2.28          | ~ (v1_relat_1 @ X5))),
% 2.06/2.28      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.06/2.28  thf('36', plain,
% 2.06/2.28      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 2.06/2.28      inference('sup-', [status(thm)], ['34', '35'])).
% 2.06/2.28  thf('37', plain, ((v1_relat_1 @ sk_E)),
% 2.06/2.28      inference('sup-', [status(thm)], ['24', '25'])).
% 2.06/2.28  thf('38', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 2.06/2.28      inference('demod', [status(thm)], ['36', '37'])).
% 2.06/2.28  thf(t28_xboole_1, axiom,
% 2.06/2.28    (![A:$i,B:$i]:
% 2.06/2.28     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.06/2.28  thf('39', plain,
% 2.06/2.28      (![X3 : $i, X4 : $i]:
% 2.06/2.28         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 2.06/2.28      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.06/2.28  thf('40', plain,
% 2.06/2.28      (((k3_xboole_0 @ (k2_relat_1 @ sk_E) @ sk_C) = (k2_relat_1 @ sk_E))),
% 2.06/2.28      inference('sup-', [status(thm)], ['38', '39'])).
% 2.06/2.28  thf('41', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 2.06/2.28      inference('demod', [status(thm)], ['23', '26'])).
% 2.06/2.28  thf('42', plain,
% 2.06/2.28      (![X7 : $i, X8 : $i]:
% 2.06/2.28         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 2.06/2.28          | ~ (v1_relat_1 @ X7))),
% 2.06/2.28      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.06/2.28  thf(t168_relat_1, axiom,
% 2.06/2.28    (![A:$i,B:$i]:
% 2.06/2.28     ( ( v1_relat_1 @ B ) =>
% 2.06/2.28       ( ( k10_relat_1 @ B @ A ) =
% 2.06/2.28         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 2.06/2.28  thf('43', plain,
% 2.06/2.28      (![X11 : $i, X12 : $i]:
% 2.06/2.28         (((k10_relat_1 @ X11 @ X12)
% 2.06/2.28            = (k10_relat_1 @ X11 @ (k3_xboole_0 @ (k2_relat_1 @ X11) @ X12)))
% 2.06/2.28          | ~ (v1_relat_1 @ X11))),
% 2.06/2.28      inference('cnf', [status(esa)], [t168_relat_1])).
% 2.06/2.28  thf('44', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.28         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.06/2.28            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 2.06/2.28               (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X2)))
% 2.06/2.28          | ~ (v1_relat_1 @ X1)
% 2.06/2.28          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.06/2.28      inference('sup+', [status(thm)], ['42', '43'])).
% 2.06/2.28  thf('45', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (~ (v1_relat_1 @ sk_E)
% 2.06/2.28          | ~ (v1_relat_1 @ sk_E)
% 2.06/2.28          | ((k10_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ X0)
% 2.06/2.28              = (k10_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 2.06/2.28                 (k3_xboole_0 @ (k9_relat_1 @ sk_E @ sk_B) @ X0))))),
% 2.06/2.28      inference('sup-', [status(thm)], ['41', '44'])).
% 2.06/2.28  thf('46', plain, ((v1_relat_1 @ sk_E)),
% 2.06/2.28      inference('sup-', [status(thm)], ['24', '25'])).
% 2.06/2.28  thf('47', plain, ((v1_relat_1 @ sk_E)),
% 2.06/2.28      inference('sup-', [status(thm)], ['24', '25'])).
% 2.06/2.28  thf('48', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 2.06/2.28      inference('demod', [status(thm)], ['23', '26'])).
% 2.06/2.28  thf('49', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 2.06/2.28      inference('demod', [status(thm)], ['23', '26'])).
% 2.06/2.28  thf('50', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         ((k10_relat_1 @ sk_E @ X0)
% 2.06/2.28           = (k10_relat_1 @ sk_E @ 
% 2.06/2.28              (k3_xboole_0 @ (k9_relat_1 @ sk_E @ sk_B) @ X0)))),
% 2.06/2.28      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 2.06/2.28  thf('51', plain, (((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))),
% 2.06/2.28      inference('demod', [status(thm)], ['29', '30'])).
% 2.06/2.28  thf('52', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         ((k10_relat_1 @ sk_E @ X0)
% 2.06/2.28           = (k10_relat_1 @ sk_E @ (k3_xboole_0 @ (k2_relat_1 @ sk_E) @ X0)))),
% 2.06/2.28      inference('demod', [status(thm)], ['50', '51'])).
% 2.06/2.28  thf('53', plain,
% 2.06/2.28      (((k10_relat_1 @ sk_E @ sk_C)
% 2.06/2.28         = (k10_relat_1 @ sk_E @ (k2_relat_1 @ sk_E)))),
% 2.06/2.28      inference('sup+', [status(thm)], ['40', '52'])).
% 2.06/2.28  thf('54', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.06/2.28      inference('demod', [status(thm)], ['2', '9', '12'])).
% 2.06/2.28  thf('55', plain, ((v2_funct_1 @ sk_E)),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('56', plain, ((v1_funct_1 @ sk_E)),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('57', plain, ((v1_relat_1 @ sk_E)),
% 2.06/2.28      inference('sup-', [status(thm)], ['24', '25'])).
% 2.06/2.28  thf('58', plain, (((k10_relat_1 @ sk_E @ sk_C) = (sk_B))),
% 2.06/2.28      inference('demod', [status(thm)],
% 2.06/2.28                ['18', '31', '53', '54', '55', '56', '57'])).
% 2.06/2.28  thf('59', plain,
% 2.06/2.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('60', plain,
% 2.06/2.28      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.06/2.28         ((v5_relat_1 @ X20 @ X22)
% 2.06/2.28          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.06/2.28      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.06/2.28  thf('61', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 2.06/2.28      inference('sup-', [status(thm)], ['59', '60'])).
% 2.06/2.28  thf('62', plain,
% 2.06/2.28      (![X5 : $i, X6 : $i]:
% 2.06/2.28         (~ (v5_relat_1 @ X5 @ X6)
% 2.06/2.28          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 2.06/2.28          | ~ (v1_relat_1 @ X5))),
% 2.06/2.28      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.06/2.28  thf('63', plain,
% 2.06/2.28      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 2.06/2.28      inference('sup-', [status(thm)], ['61', '62'])).
% 2.06/2.28  thf('64', plain,
% 2.06/2.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('65', plain,
% 2.06/2.28      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.06/2.28         ((v1_relat_1 @ X17)
% 2.06/2.28          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 2.06/2.28      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.06/2.28  thf('66', plain, ((v1_relat_1 @ sk_D)),
% 2.06/2.28      inference('sup-', [status(thm)], ['64', '65'])).
% 2.06/2.28  thf('67', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 2.06/2.28      inference('demod', [status(thm)], ['63', '66'])).
% 2.06/2.28  thf('68', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.06/2.28      inference('demod', [status(thm)], ['2', '9', '12'])).
% 2.06/2.28  thf('69', plain,
% 2.06/2.28      (![X15 : $i, X16 : $i]:
% 2.06/2.28         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 2.06/2.28          | ~ (v2_funct_1 @ X16)
% 2.06/2.28          | ((k10_relat_1 @ X16 @ (k9_relat_1 @ X16 @ X15)) = (X15))
% 2.06/2.28          | ~ (v1_funct_1 @ X16)
% 2.06/2.28          | ~ (v1_relat_1 @ X16))),
% 2.06/2.28      inference('cnf', [status(esa)], [t164_funct_1])).
% 2.06/2.28  thf('70', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (~ (r1_tarski @ X0 @ sk_B)
% 2.06/2.28          | ~ (v1_relat_1 @ sk_E)
% 2.06/2.28          | ~ (v1_funct_1 @ sk_E)
% 2.06/2.28          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0))
% 2.06/2.28          | ~ (v2_funct_1 @ sk_E))),
% 2.06/2.28      inference('sup-', [status(thm)], ['68', '69'])).
% 2.06/2.28  thf('71', plain, ((v1_relat_1 @ sk_E)),
% 2.06/2.28      inference('sup-', [status(thm)], ['24', '25'])).
% 2.06/2.28  thf('72', plain, ((v1_funct_1 @ sk_E)),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('73', plain, ((v2_funct_1 @ sk_E)),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('74', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (~ (r1_tarski @ X0 @ sk_B)
% 2.06/2.28          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0)))),
% 2.06/2.28      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 2.06/2.28  thf('75', plain,
% 2.06/2.28      (((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 2.06/2.28         = (k2_relat_1 @ sk_D))),
% 2.06/2.28      inference('sup-', [status(thm)], ['67', '74'])).
% 2.06/2.28  thf(t160_relat_1, axiom,
% 2.06/2.28    (![A:$i]:
% 2.06/2.28     ( ( v1_relat_1 @ A ) =>
% 2.06/2.28       ( ![B:$i]:
% 2.06/2.28         ( ( v1_relat_1 @ B ) =>
% 2.06/2.28           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.06/2.28             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.06/2.28  thf('76', plain,
% 2.06/2.28      (![X9 : $i, X10 : $i]:
% 2.06/2.28         (~ (v1_relat_1 @ X9)
% 2.06/2.28          | ((k2_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 2.06/2.28              = (k9_relat_1 @ X9 @ (k2_relat_1 @ X10)))
% 2.06/2.28          | ~ (v1_relat_1 @ X10))),
% 2.06/2.28      inference('cnf', [status(esa)], [t160_relat_1])).
% 2.06/2.28  thf('77', plain,
% 2.06/2.28      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('78', plain,
% 2.06/2.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf(dt_k4_relset_1, axiom,
% 2.06/2.28    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.06/2.28     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.06/2.28         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.06/2.28       ( m1_subset_1 @
% 2.06/2.28         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.06/2.28         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 2.06/2.28  thf('79', plain,
% 2.06/2.28      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 2.06/2.28         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 2.06/2.28          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 2.06/2.28          | (m1_subset_1 @ (k4_relset_1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 2.06/2.28             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 2.06/2.28      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 2.06/2.28  thf('80', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.28         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.06/2.28           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.06/2.28          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 2.06/2.28      inference('sup-', [status(thm)], ['78', '79'])).
% 2.06/2.28  thf('81', plain,
% 2.06/2.28      ((m1_subset_1 @ 
% 2.06/2.28        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 2.06/2.28        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['77', '80'])).
% 2.06/2.28  thf('82', plain,
% 2.06/2.28      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('83', plain,
% 2.06/2.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf(redefinition_k4_relset_1, axiom,
% 2.06/2.28    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.06/2.28     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.06/2.28         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.06/2.28       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.06/2.28  thf('84', plain,
% 2.06/2.28      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.06/2.28         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 2.06/2.28          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 2.06/2.28          | ((k4_relset_1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 2.06/2.28              = (k5_relat_1 @ X35 @ X38)))),
% 2.06/2.28      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 2.06/2.28  thf('85', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.28         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.06/2.28            = (k5_relat_1 @ sk_D @ X0))
% 2.06/2.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.06/2.28      inference('sup-', [status(thm)], ['83', '84'])).
% 2.06/2.28  thf('86', plain,
% 2.06/2.28      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.06/2.28         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.06/2.28      inference('sup-', [status(thm)], ['82', '85'])).
% 2.06/2.28  thf('87', plain,
% 2.06/2.28      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 2.06/2.28        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.06/2.28      inference('demod', [status(thm)], ['81', '86'])).
% 2.06/2.28  thf(redefinition_k2_relset_1, axiom,
% 2.06/2.28    (![A:$i,B:$i,C:$i]:
% 2.06/2.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.06/2.28       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.06/2.28  thf('88', plain,
% 2.06/2.28      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.06/2.28         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 2.06/2.28          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 2.06/2.28      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.06/2.28  thf('89', plain,
% 2.06/2.28      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 2.06/2.28         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['87', '88'])).
% 2.06/2.28  thf('90', plain,
% 2.06/2.28      (((k2_relset_1 @ sk_A @ sk_C @ 
% 2.06/2.28         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('91', plain,
% 2.06/2.28      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('92', plain,
% 2.06/2.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf(redefinition_k1_partfun1, axiom,
% 2.06/2.28    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.06/2.28     ( ( ( v1_funct_1 @ E ) & 
% 2.06/2.28         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.06/2.28         ( v1_funct_1 @ F ) & 
% 2.06/2.28         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.06/2.28       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.06/2.28  thf('93', plain,
% 2.06/2.28      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 2.06/2.28         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 2.06/2.28          | ~ (v1_funct_1 @ X49)
% 2.06/2.28          | ~ (v1_funct_1 @ X52)
% 2.06/2.28          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 2.06/2.28          | ((k1_partfun1 @ X50 @ X51 @ X53 @ X54 @ X49 @ X52)
% 2.06/2.28              = (k5_relat_1 @ X49 @ X52)))),
% 2.06/2.28      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.06/2.28  thf('94', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.28         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.06/2.28            = (k5_relat_1 @ sk_D @ X0))
% 2.06/2.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.06/2.28          | ~ (v1_funct_1 @ X0)
% 2.06/2.28          | ~ (v1_funct_1 @ sk_D))),
% 2.06/2.28      inference('sup-', [status(thm)], ['92', '93'])).
% 2.06/2.28  thf('95', plain, ((v1_funct_1 @ sk_D)),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('96', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.28         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.06/2.28            = (k5_relat_1 @ sk_D @ X0))
% 2.06/2.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.06/2.28          | ~ (v1_funct_1 @ X0))),
% 2.06/2.28      inference('demod', [status(thm)], ['94', '95'])).
% 2.06/2.28  thf('97', plain,
% 2.06/2.28      ((~ (v1_funct_1 @ sk_E)
% 2.06/2.28        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.06/2.28            = (k5_relat_1 @ sk_D @ sk_E)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['91', '96'])).
% 2.06/2.28  thf('98', plain, ((v1_funct_1 @ sk_E)),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('99', plain,
% 2.06/2.28      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.06/2.28         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.06/2.28      inference('demod', [status(thm)], ['97', '98'])).
% 2.06/2.28  thf('100', plain,
% 2.06/2.28      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.06/2.28      inference('demod', [status(thm)], ['90', '99'])).
% 2.06/2.28  thf('101', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.06/2.28      inference('sup+', [status(thm)], ['89', '100'])).
% 2.06/2.28  thf('102', plain,
% 2.06/2.28      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))
% 2.06/2.28        | ~ (v1_relat_1 @ sk_D)
% 2.06/2.28        | ~ (v1_relat_1 @ sk_E))),
% 2.06/2.28      inference('sup+', [status(thm)], ['76', '101'])).
% 2.06/2.28  thf('103', plain, ((v1_relat_1 @ sk_D)),
% 2.06/2.28      inference('sup-', [status(thm)], ['64', '65'])).
% 2.06/2.28  thf('104', plain, ((v1_relat_1 @ sk_E)),
% 2.06/2.28      inference('sup-', [status(thm)], ['24', '25'])).
% 2.06/2.28  thf('105', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 2.06/2.28      inference('demod', [status(thm)], ['102', '103', '104'])).
% 2.06/2.28  thf('106', plain, (((k10_relat_1 @ sk_E @ sk_C) = (k2_relat_1 @ sk_D))),
% 2.06/2.28      inference('demod', [status(thm)], ['75', '105'])).
% 2.06/2.28  thf('107', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 2.06/2.28      inference('sup+', [status(thm)], ['58', '106'])).
% 2.06/2.28  thf('108', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('109', plain,
% 2.06/2.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('110', plain,
% 2.06/2.28      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.06/2.28         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 2.06/2.28          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 2.06/2.28      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.06/2.28  thf('111', plain,
% 2.06/2.28      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.06/2.28      inference('sup-', [status(thm)], ['109', '110'])).
% 2.06/2.28  thf('112', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 2.06/2.28      inference('demod', [status(thm)], ['108', '111'])).
% 2.06/2.28  thf('113', plain, ($false),
% 2.06/2.28      inference('simplify_reflect-', [status(thm)], ['107', '112'])).
% 2.06/2.28  
% 2.06/2.28  % SZS output end Refutation
% 2.06/2.28  
% 2.06/2.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
