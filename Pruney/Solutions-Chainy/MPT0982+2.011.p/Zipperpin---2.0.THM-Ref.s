%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wjInqXGbu1

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:56 EST 2020

% Result     : Theorem 3.39s
% Output     : Refutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 974 expanded)
%              Number of leaves         :   48 ( 301 expanded)
%              Depth                    :   21
%              Number of atoms          : 1507 (21638 expanded)
%              Number of equality atoms :   95 (1200 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v4_relat_1 @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X10: $i] :
      ( ( ( k10_relat_1 @ X10 @ ( k2_relat_1 @ X10 ) )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k9_relat_1 @ sk_E @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['5','6'])).

thf('14',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['5','6'])).

thf('15',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('16',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('17',plain,
    ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ sk_B ) )
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('20',plain,
    ( ( ( k2_relat_1 @ sk_E )
      = ( k9_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['5','6'])).

thf('22',plain,
    ( ( k2_relat_1 @ sk_E )
    = ( k9_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ sk_E ) )
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('30',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['26','33','36'])).

thf('38',plain,
    ( ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ sk_E ) )
    = sk_B ),
    inference(demod,[status(thm)],['23','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('41',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['5','6'])).

thf('45',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relat_1 @ sk_E ) )
    | ( sk_C
      = ( k2_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('50',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ( ( k1_partfun1 @ X51 @ X52 @ X54 @ X55 @ X50 @ X53 )
        = ( k5_relat_1 @ X50 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55','64'])).

thf('66',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('68',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('69',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ( v5_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['5','6'])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['71','72','75'])).

thf('77',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) @ ( k2_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('80',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) @ ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['78','79'])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('81',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k9_relat_1 @ X7 @ ( k9_relat_1 @ X8 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('82',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55','64'])).

thf('83',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('84',plain,(
    v4_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( ( k5_relat_1 @ sk_D @ sk_E )
      = ( k7_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('88',plain,
    ( ( k5_relat_1 @ sk_D @ sk_E )
    = ( k7_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('90',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      = ( k9_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('92',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k9_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      = ( k9_relat_1 @ sk_E @ ( k9_relat_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['81','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('96',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('100',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('102',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('106',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['5','6'])).

thf('107',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['93','104','105','106'])).

thf('108',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) @ ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['80','107'])).

thf('109',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55','64'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('110',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('111',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['93','104','105','106'])).

thf('113',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('116',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = sk_C ),
    inference('sup+',[status(thm)],['113','116'])).

thf('118',plain,(
    r1_tarski @ sk_C @ ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['108','117'])).

thf('119',plain,
    ( sk_C
    = ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['47','118'])).

thf('120',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['38','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('123',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('125',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('127',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['26','33','36'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('129',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ( ( k10_relat_1 @ X16 @ ( k9_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['5','6'])).

thf('132',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf('135',plain,
    ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['127','134'])).

thf('136',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = sk_C ),
    inference('sup+',[status(thm)],['113','116'])).

thf('137',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['120','137'])).

thf('139',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('142',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['139','142'])).

thf('144',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['138','143'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wjInqXGbu1
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:31:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.39/3.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.39/3.62  % Solved by: fo/fo7.sh
% 3.39/3.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.39/3.62  % done 978 iterations in 3.197s
% 3.39/3.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.39/3.62  % SZS output start Refutation
% 3.39/3.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.39/3.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.39/3.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.39/3.62  thf(sk_B_type, type, sk_B: $i).
% 3.39/3.62  thf(sk_E_type, type, sk_E: $i).
% 3.39/3.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.39/3.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.39/3.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.39/3.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.39/3.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.39/3.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.39/3.62  thf(sk_C_type, type, sk_C: $i).
% 3.39/3.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.39/3.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.39/3.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.39/3.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.39/3.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.39/3.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.39/3.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.39/3.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.39/3.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.39/3.62  thf(sk_D_type, type, sk_D: $i).
% 3.39/3.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.39/3.62  thf(sk_A_type, type, sk_A: $i).
% 3.39/3.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.39/3.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.39/3.62  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.39/3.62  thf(t28_funct_2, conjecture,
% 3.39/3.62    (![A:$i,B:$i,C:$i,D:$i]:
% 3.39/3.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.39/3.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.39/3.62       ( ![E:$i]:
% 3.39/3.62         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.39/3.62             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.39/3.62           ( ( ( ( k2_relset_1 @
% 3.39/3.62                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 3.39/3.62                 ( C ) ) & 
% 3.39/3.62               ( v2_funct_1 @ E ) ) =>
% 3.39/3.62             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 3.39/3.62               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 3.39/3.62  thf(zf_stmt_0, negated_conjecture,
% 3.39/3.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.39/3.62        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.39/3.62            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.39/3.62          ( ![E:$i]:
% 3.39/3.62            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.39/3.62                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.39/3.62              ( ( ( ( k2_relset_1 @
% 3.39/3.62                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 3.39/3.62                    ( C ) ) & 
% 3.39/3.62                  ( v2_funct_1 @ E ) ) =>
% 3.39/3.62                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 3.39/3.62                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 3.39/3.62    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 3.39/3.62  thf('0', plain,
% 3.39/3.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf(cc2_relset_1, axiom,
% 3.39/3.62    (![A:$i,B:$i,C:$i]:
% 3.39/3.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.39/3.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.39/3.62  thf('1', plain,
% 3.39/3.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.39/3.62         ((v4_relat_1 @ X20 @ X21)
% 3.39/3.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.39/3.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.39/3.62  thf('2', plain, ((v4_relat_1 @ sk_E @ sk_B)),
% 3.39/3.62      inference('sup-', [status(thm)], ['0', '1'])).
% 3.39/3.62  thf(t209_relat_1, axiom,
% 3.39/3.62    (![A:$i,B:$i]:
% 3.39/3.62     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 3.39/3.62       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 3.39/3.62  thf('3', plain,
% 3.39/3.62      (![X11 : $i, X12 : $i]:
% 3.39/3.62         (((X11) = (k7_relat_1 @ X11 @ X12))
% 3.39/3.62          | ~ (v4_relat_1 @ X11 @ X12)
% 3.39/3.62          | ~ (v1_relat_1 @ X11))),
% 3.39/3.62      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.39/3.62  thf('4', plain,
% 3.39/3.62      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_B)))),
% 3.39/3.62      inference('sup-', [status(thm)], ['2', '3'])).
% 3.39/3.62  thf('5', plain,
% 3.39/3.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf(cc1_relset_1, axiom,
% 3.39/3.62    (![A:$i,B:$i,C:$i]:
% 3.39/3.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.39/3.62       ( v1_relat_1 @ C ) ))).
% 3.39/3.62  thf('6', plain,
% 3.39/3.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.39/3.62         ((v1_relat_1 @ X17)
% 3.39/3.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.39/3.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.39/3.62  thf('7', plain, ((v1_relat_1 @ sk_E)),
% 3.39/3.62      inference('sup-', [status(thm)], ['5', '6'])).
% 3.39/3.62  thf('8', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 3.39/3.62      inference('demod', [status(thm)], ['4', '7'])).
% 3.39/3.62  thf(t148_relat_1, axiom,
% 3.39/3.62    (![A:$i,B:$i]:
% 3.39/3.62     ( ( v1_relat_1 @ B ) =>
% 3.39/3.62       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 3.39/3.62  thf('9', plain,
% 3.39/3.62      (![X5 : $i, X6 : $i]:
% 3.39/3.62         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 3.39/3.62          | ~ (v1_relat_1 @ X5))),
% 3.39/3.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.39/3.62  thf(t169_relat_1, axiom,
% 3.39/3.62    (![A:$i]:
% 3.39/3.62     ( ( v1_relat_1 @ A ) =>
% 3.39/3.62       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 3.39/3.62  thf('10', plain,
% 3.39/3.62      (![X10 : $i]:
% 3.39/3.62         (((k10_relat_1 @ X10 @ (k2_relat_1 @ X10)) = (k1_relat_1 @ X10))
% 3.39/3.62          | ~ (v1_relat_1 @ X10))),
% 3.39/3.62      inference('cnf', [status(esa)], [t169_relat_1])).
% 3.39/3.62  thf('11', plain,
% 3.39/3.62      (![X0 : $i, X1 : $i]:
% 3.39/3.62         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 3.39/3.62            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 3.39/3.62          | ~ (v1_relat_1 @ X1)
% 3.39/3.62          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 3.39/3.62      inference('sup+', [status(thm)], ['9', '10'])).
% 3.39/3.62  thf('12', plain,
% 3.39/3.62      ((~ (v1_relat_1 @ sk_E)
% 3.39/3.62        | ~ (v1_relat_1 @ sk_E)
% 3.39/3.62        | ((k10_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 3.39/3.62            (k9_relat_1 @ sk_E @ sk_B))
% 3.39/3.62            = (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))))),
% 3.39/3.62      inference('sup-', [status(thm)], ['8', '11'])).
% 3.39/3.62  thf('13', plain, ((v1_relat_1 @ sk_E)),
% 3.39/3.62      inference('sup-', [status(thm)], ['5', '6'])).
% 3.39/3.62  thf('14', plain, ((v1_relat_1 @ sk_E)),
% 3.39/3.62      inference('sup-', [status(thm)], ['5', '6'])).
% 3.39/3.62  thf('15', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 3.39/3.62      inference('demod', [status(thm)], ['4', '7'])).
% 3.39/3.62  thf('16', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 3.39/3.62      inference('demod', [status(thm)], ['4', '7'])).
% 3.39/3.62  thf('17', plain,
% 3.39/3.62      (((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ sk_B)) = (k1_relat_1 @ sk_E))),
% 3.39/3.62      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 3.39/3.62  thf('18', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 3.39/3.62      inference('demod', [status(thm)], ['4', '7'])).
% 3.39/3.62  thf('19', plain,
% 3.39/3.62      (![X5 : $i, X6 : $i]:
% 3.39/3.62         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 3.39/3.62          | ~ (v1_relat_1 @ X5))),
% 3.39/3.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.39/3.62  thf('20', plain,
% 3.39/3.62      ((((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))
% 3.39/3.62        | ~ (v1_relat_1 @ sk_E))),
% 3.39/3.62      inference('sup+', [status(thm)], ['18', '19'])).
% 3.39/3.62  thf('21', plain, ((v1_relat_1 @ sk_E)),
% 3.39/3.62      inference('sup-', [status(thm)], ['5', '6'])).
% 3.39/3.62  thf('22', plain, (((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))),
% 3.39/3.62      inference('demod', [status(thm)], ['20', '21'])).
% 3.39/3.62  thf('23', plain,
% 3.39/3.62      (((k10_relat_1 @ sk_E @ (k2_relat_1 @ sk_E)) = (k1_relat_1 @ sk_E))),
% 3.39/3.62      inference('demod', [status(thm)], ['17', '22'])).
% 3.39/3.62  thf('24', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf(d1_funct_2, axiom,
% 3.39/3.62    (![A:$i,B:$i,C:$i]:
% 3.39/3.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.39/3.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.39/3.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.39/3.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.39/3.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.39/3.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.39/3.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.39/3.62  thf(zf_stmt_1, axiom,
% 3.39/3.62    (![C:$i,B:$i,A:$i]:
% 3.39/3.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.39/3.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.39/3.62  thf('25', plain,
% 3.39/3.62      (![X38 : $i, X39 : $i, X40 : $i]:
% 3.39/3.62         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 3.39/3.62          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 3.39/3.62          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.39/3.62  thf('26', plain,
% 3.39/3.62      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 3.39/3.62        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 3.39/3.62      inference('sup-', [status(thm)], ['24', '25'])).
% 3.39/3.62  thf(zf_stmt_2, axiom,
% 3.39/3.62    (![B:$i,A:$i]:
% 3.39/3.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.39/3.62       ( zip_tseitin_0 @ B @ A ) ))).
% 3.39/3.62  thf('27', plain,
% 3.39/3.62      (![X36 : $i, X37 : $i]:
% 3.39/3.62         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.39/3.62  thf('28', plain,
% 3.39/3.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.39/3.62  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.39/3.62  thf(zf_stmt_5, axiom,
% 3.39/3.62    (![A:$i,B:$i,C:$i]:
% 3.39/3.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.39/3.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.39/3.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.39/3.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.39/3.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.39/3.62  thf('29', plain,
% 3.39/3.62      (![X41 : $i, X42 : $i, X43 : $i]:
% 3.39/3.62         (~ (zip_tseitin_0 @ X41 @ X42)
% 3.39/3.62          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 3.39/3.62          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.39/3.62  thf('30', plain,
% 3.39/3.62      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 3.39/3.62      inference('sup-', [status(thm)], ['28', '29'])).
% 3.39/3.62  thf('31', plain,
% 3.39/3.62      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 3.39/3.62      inference('sup-', [status(thm)], ['27', '30'])).
% 3.39/3.62  thf('32', plain, (((sk_C) != (k1_xboole_0))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('33', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 3.39/3.62      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 3.39/3.62  thf('34', plain,
% 3.39/3.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf(redefinition_k1_relset_1, axiom,
% 3.39/3.62    (![A:$i,B:$i,C:$i]:
% 3.39/3.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.39/3.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.39/3.62  thf('35', plain,
% 3.39/3.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.39/3.62         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 3.39/3.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 3.39/3.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.39/3.62  thf('36', plain,
% 3.39/3.62      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 3.39/3.62      inference('sup-', [status(thm)], ['34', '35'])).
% 3.39/3.62  thf('37', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 3.39/3.62      inference('demod', [status(thm)], ['26', '33', '36'])).
% 3.39/3.62  thf('38', plain, (((k10_relat_1 @ sk_E @ (k2_relat_1 @ sk_E)) = (sk_B))),
% 3.39/3.62      inference('demod', [status(thm)], ['23', '37'])).
% 3.39/3.62  thf('39', plain,
% 3.39/3.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('40', plain,
% 3.39/3.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.39/3.62         ((v5_relat_1 @ X20 @ X22)
% 3.39/3.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.39/3.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.39/3.62  thf('41', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 3.39/3.62      inference('sup-', [status(thm)], ['39', '40'])).
% 3.39/3.62  thf(d19_relat_1, axiom,
% 3.39/3.62    (![A:$i,B:$i]:
% 3.39/3.62     ( ( v1_relat_1 @ B ) =>
% 3.39/3.62       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.39/3.62  thf('42', plain,
% 3.39/3.62      (![X3 : $i, X4 : $i]:
% 3.39/3.62         (~ (v5_relat_1 @ X3 @ X4)
% 3.39/3.62          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 3.39/3.62          | ~ (v1_relat_1 @ X3))),
% 3.39/3.62      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.39/3.62  thf('43', plain,
% 3.39/3.62      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 3.39/3.62      inference('sup-', [status(thm)], ['41', '42'])).
% 3.39/3.62  thf('44', plain, ((v1_relat_1 @ sk_E)),
% 3.39/3.62      inference('sup-', [status(thm)], ['5', '6'])).
% 3.39/3.62  thf('45', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 3.39/3.62      inference('demod', [status(thm)], ['43', '44'])).
% 3.39/3.62  thf(d10_xboole_0, axiom,
% 3.39/3.62    (![A:$i,B:$i]:
% 3.39/3.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.39/3.62  thf('46', plain,
% 3.39/3.62      (![X0 : $i, X2 : $i]:
% 3.39/3.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.39/3.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.39/3.62  thf('47', plain,
% 3.39/3.62      ((~ (r1_tarski @ sk_C @ (k2_relat_1 @ sk_E))
% 3.39/3.62        | ((sk_C) = (k2_relat_1 @ sk_E)))),
% 3.39/3.62      inference('sup-', [status(thm)], ['45', '46'])).
% 3.39/3.62  thf('48', plain,
% 3.39/3.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('49', plain,
% 3.39/3.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf(dt_k1_partfun1, axiom,
% 3.39/3.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.39/3.62     ( ( ( v1_funct_1 @ E ) & 
% 3.39/3.62         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.39/3.62         ( v1_funct_1 @ F ) & 
% 3.39/3.62         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.39/3.62       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.39/3.62         ( m1_subset_1 @
% 3.39/3.62           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.39/3.62           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.39/3.62  thf('50', plain,
% 3.39/3.62      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 3.39/3.62         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 3.39/3.62          | ~ (v1_funct_1 @ X44)
% 3.39/3.62          | ~ (v1_funct_1 @ X47)
% 3.39/3.62          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 3.39/3.62          | (m1_subset_1 @ (k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47) @ 
% 3.39/3.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X49))))),
% 3.39/3.62      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.39/3.62  thf('51', plain,
% 3.39/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.39/3.62         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 3.39/3.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.39/3.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.39/3.62          | ~ (v1_funct_1 @ X1)
% 3.39/3.62          | ~ (v1_funct_1 @ sk_D))),
% 3.39/3.62      inference('sup-', [status(thm)], ['49', '50'])).
% 3.39/3.62  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('53', plain,
% 3.39/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.39/3.62         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 3.39/3.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.39/3.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.39/3.62          | ~ (v1_funct_1 @ X1))),
% 3.39/3.62      inference('demod', [status(thm)], ['51', '52'])).
% 3.39/3.62  thf('54', plain,
% 3.39/3.62      ((~ (v1_funct_1 @ sk_E)
% 3.39/3.62        | (m1_subset_1 @ 
% 3.39/3.62           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 3.39/3.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 3.39/3.62      inference('sup-', [status(thm)], ['48', '53'])).
% 3.39/3.62  thf('55', plain, ((v1_funct_1 @ sk_E)),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('56', plain,
% 3.39/3.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('57', plain,
% 3.39/3.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf(redefinition_k1_partfun1, axiom,
% 3.39/3.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.39/3.62     ( ( ( v1_funct_1 @ E ) & 
% 3.39/3.62         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.39/3.62         ( v1_funct_1 @ F ) & 
% 3.39/3.62         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.39/3.62       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.39/3.62  thf('58', plain,
% 3.39/3.62      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 3.39/3.62         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 3.39/3.62          | ~ (v1_funct_1 @ X50)
% 3.39/3.62          | ~ (v1_funct_1 @ X53)
% 3.39/3.62          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 3.39/3.62          | ((k1_partfun1 @ X51 @ X52 @ X54 @ X55 @ X50 @ X53)
% 3.39/3.62              = (k5_relat_1 @ X50 @ X53)))),
% 3.39/3.62      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.39/3.62  thf('59', plain,
% 3.39/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.39/3.62         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 3.39/3.62            = (k5_relat_1 @ sk_D @ X0))
% 3.39/3.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.39/3.62          | ~ (v1_funct_1 @ X0)
% 3.39/3.62          | ~ (v1_funct_1 @ sk_D))),
% 3.39/3.62      inference('sup-', [status(thm)], ['57', '58'])).
% 3.39/3.62  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('61', plain,
% 3.39/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.39/3.62         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 3.39/3.62            = (k5_relat_1 @ sk_D @ X0))
% 3.39/3.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.39/3.62          | ~ (v1_funct_1 @ X0))),
% 3.39/3.62      inference('demod', [status(thm)], ['59', '60'])).
% 3.39/3.62  thf('62', plain,
% 3.39/3.62      ((~ (v1_funct_1 @ sk_E)
% 3.39/3.62        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 3.39/3.62            = (k5_relat_1 @ sk_D @ sk_E)))),
% 3.39/3.62      inference('sup-', [status(thm)], ['56', '61'])).
% 3.39/3.62  thf('63', plain, ((v1_funct_1 @ sk_E)),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('64', plain,
% 3.39/3.62      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 3.39/3.62         = (k5_relat_1 @ sk_D @ sk_E))),
% 3.39/3.62      inference('demod', [status(thm)], ['62', '63'])).
% 3.39/3.62  thf('65', plain,
% 3.39/3.62      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 3.39/3.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 3.39/3.62      inference('demod', [status(thm)], ['54', '55', '64'])).
% 3.39/3.62  thf('66', plain,
% 3.39/3.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.39/3.62         ((v1_relat_1 @ X17)
% 3.39/3.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.39/3.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.39/3.62  thf('67', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 3.39/3.62      inference('sup-', [status(thm)], ['65', '66'])).
% 3.39/3.62  thf(t45_relat_1, axiom,
% 3.39/3.62    (![A:$i]:
% 3.39/3.62     ( ( v1_relat_1 @ A ) =>
% 3.39/3.62       ( ![B:$i]:
% 3.39/3.62         ( ( v1_relat_1 @ B ) =>
% 3.39/3.62           ( r1_tarski @
% 3.39/3.62             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 3.39/3.62  thf('68', plain,
% 3.39/3.62      (![X13 : $i, X14 : $i]:
% 3.39/3.62         (~ (v1_relat_1 @ X13)
% 3.39/3.62          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X14 @ X13)) @ 
% 3.39/3.62             (k2_relat_1 @ X13))
% 3.39/3.62          | ~ (v1_relat_1 @ X14))),
% 3.39/3.62      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.39/3.62  thf('69', plain,
% 3.39/3.62      (![X3 : $i, X4 : $i]:
% 3.39/3.62         (~ (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 3.39/3.62          | (v5_relat_1 @ X3 @ X4)
% 3.39/3.62          | ~ (v1_relat_1 @ X3))),
% 3.39/3.62      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.39/3.62  thf('70', plain,
% 3.39/3.62      (![X0 : $i, X1 : $i]:
% 3.39/3.62         (~ (v1_relat_1 @ X1)
% 3.39/3.62          | ~ (v1_relat_1 @ X0)
% 3.39/3.62          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 3.39/3.62          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.39/3.62      inference('sup-', [status(thm)], ['68', '69'])).
% 3.39/3.62  thf('71', plain,
% 3.39/3.62      (((v5_relat_1 @ (k5_relat_1 @ sk_D @ sk_E) @ (k2_relat_1 @ sk_E))
% 3.39/3.62        | ~ (v1_relat_1 @ sk_E)
% 3.39/3.62        | ~ (v1_relat_1 @ sk_D))),
% 3.39/3.62      inference('sup-', [status(thm)], ['67', '70'])).
% 3.39/3.62  thf('72', plain, ((v1_relat_1 @ sk_E)),
% 3.39/3.62      inference('sup-', [status(thm)], ['5', '6'])).
% 3.39/3.62  thf('73', plain,
% 3.39/3.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('74', plain,
% 3.39/3.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.39/3.62         ((v1_relat_1 @ X17)
% 3.39/3.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.39/3.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.39/3.62  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 3.39/3.62      inference('sup-', [status(thm)], ['73', '74'])).
% 3.39/3.62  thf('76', plain,
% 3.39/3.62      ((v5_relat_1 @ (k5_relat_1 @ sk_D @ sk_E) @ (k2_relat_1 @ sk_E))),
% 3.39/3.62      inference('demod', [status(thm)], ['71', '72', '75'])).
% 3.39/3.62  thf('77', plain,
% 3.39/3.62      (![X3 : $i, X4 : $i]:
% 3.39/3.62         (~ (v5_relat_1 @ X3 @ X4)
% 3.39/3.62          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 3.39/3.62          | ~ (v1_relat_1 @ X3))),
% 3.39/3.62      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.39/3.62  thf('78', plain,
% 3.39/3.62      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))
% 3.39/3.62        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) @ 
% 3.39/3.62           (k2_relat_1 @ sk_E)))),
% 3.39/3.62      inference('sup-', [status(thm)], ['76', '77'])).
% 3.39/3.62  thf('79', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 3.39/3.62      inference('sup-', [status(thm)], ['65', '66'])).
% 3.39/3.62  thf('80', plain,
% 3.39/3.62      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) @ 
% 3.39/3.62        (k2_relat_1 @ sk_E))),
% 3.39/3.62      inference('demod', [status(thm)], ['78', '79'])).
% 3.39/3.62  thf(t159_relat_1, axiom,
% 3.39/3.62    (![A:$i,B:$i]:
% 3.39/3.62     ( ( v1_relat_1 @ B ) =>
% 3.39/3.62       ( ![C:$i]:
% 3.39/3.62         ( ( v1_relat_1 @ C ) =>
% 3.39/3.62           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 3.39/3.62             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 3.39/3.62  thf('81', plain,
% 3.39/3.62      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.39/3.62         (~ (v1_relat_1 @ X7)
% 3.39/3.62          | ((k9_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 3.39/3.62              = (k9_relat_1 @ X7 @ (k9_relat_1 @ X8 @ X9)))
% 3.39/3.62          | ~ (v1_relat_1 @ X8))),
% 3.39/3.62      inference('cnf', [status(esa)], [t159_relat_1])).
% 3.39/3.62  thf('82', plain,
% 3.39/3.62      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 3.39/3.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 3.39/3.62      inference('demod', [status(thm)], ['54', '55', '64'])).
% 3.39/3.62  thf('83', plain,
% 3.39/3.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.39/3.62         ((v4_relat_1 @ X20 @ X21)
% 3.39/3.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.39/3.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.39/3.62  thf('84', plain, ((v4_relat_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_A)),
% 3.39/3.62      inference('sup-', [status(thm)], ['82', '83'])).
% 3.39/3.62  thf('85', plain,
% 3.39/3.62      (![X11 : $i, X12 : $i]:
% 3.39/3.62         (((X11) = (k7_relat_1 @ X11 @ X12))
% 3.39/3.62          | ~ (v4_relat_1 @ X11 @ X12)
% 3.39/3.62          | ~ (v1_relat_1 @ X11))),
% 3.39/3.62      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.39/3.62  thf('86', plain,
% 3.39/3.62      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))
% 3.39/3.62        | ((k5_relat_1 @ sk_D @ sk_E)
% 3.39/3.62            = (k7_relat_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_A)))),
% 3.39/3.62      inference('sup-', [status(thm)], ['84', '85'])).
% 3.39/3.62  thf('87', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 3.39/3.62      inference('sup-', [status(thm)], ['65', '66'])).
% 3.39/3.62  thf('88', plain,
% 3.39/3.62      (((k5_relat_1 @ sk_D @ sk_E)
% 3.39/3.62         = (k7_relat_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_A))),
% 3.39/3.62      inference('demod', [status(thm)], ['86', '87'])).
% 3.39/3.62  thf('89', plain,
% 3.39/3.62      (![X5 : $i, X6 : $i]:
% 3.39/3.62         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 3.39/3.62          | ~ (v1_relat_1 @ X5))),
% 3.39/3.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.39/3.62  thf('90', plain,
% 3.39/3.62      ((((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))
% 3.39/3.62          = (k9_relat_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_A))
% 3.39/3.62        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 3.39/3.62      inference('sup+', [status(thm)], ['88', '89'])).
% 3.39/3.62  thf('91', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 3.39/3.62      inference('sup-', [status(thm)], ['65', '66'])).
% 3.39/3.62  thf('92', plain,
% 3.39/3.62      (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))
% 3.39/3.62         = (k9_relat_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_A))),
% 3.39/3.62      inference('demod', [status(thm)], ['90', '91'])).
% 3.39/3.62  thf('93', plain,
% 3.39/3.62      ((((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))
% 3.39/3.62          = (k9_relat_1 @ sk_E @ (k9_relat_1 @ sk_D @ sk_A)))
% 3.39/3.62        | ~ (v1_relat_1 @ sk_D)
% 3.39/3.62        | ~ (v1_relat_1 @ sk_E))),
% 3.39/3.62      inference('sup+', [status(thm)], ['81', '92'])).
% 3.39/3.62  thf('94', plain,
% 3.39/3.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('95', plain,
% 3.39/3.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.39/3.62         ((v4_relat_1 @ X20 @ X21)
% 3.39/3.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.39/3.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.39/3.62  thf('96', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 3.39/3.62      inference('sup-', [status(thm)], ['94', '95'])).
% 3.39/3.62  thf('97', plain,
% 3.39/3.62      (![X11 : $i, X12 : $i]:
% 3.39/3.62         (((X11) = (k7_relat_1 @ X11 @ X12))
% 3.39/3.62          | ~ (v4_relat_1 @ X11 @ X12)
% 3.39/3.62          | ~ (v1_relat_1 @ X11))),
% 3.39/3.62      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.39/3.62  thf('98', plain,
% 3.39/3.62      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_A)))),
% 3.39/3.62      inference('sup-', [status(thm)], ['96', '97'])).
% 3.39/3.62  thf('99', plain, ((v1_relat_1 @ sk_D)),
% 3.39/3.62      inference('sup-', [status(thm)], ['73', '74'])).
% 3.39/3.62  thf('100', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 3.39/3.62      inference('demod', [status(thm)], ['98', '99'])).
% 3.39/3.62  thf('101', plain,
% 3.39/3.62      (![X5 : $i, X6 : $i]:
% 3.39/3.62         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 3.39/3.62          | ~ (v1_relat_1 @ X5))),
% 3.39/3.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.39/3.62  thf('102', plain,
% 3.39/3.62      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_A))
% 3.39/3.62        | ~ (v1_relat_1 @ sk_D))),
% 3.39/3.62      inference('sup+', [status(thm)], ['100', '101'])).
% 3.39/3.62  thf('103', plain, ((v1_relat_1 @ sk_D)),
% 3.39/3.62      inference('sup-', [status(thm)], ['73', '74'])).
% 3.39/3.62  thf('104', plain, (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_A))),
% 3.39/3.62      inference('demod', [status(thm)], ['102', '103'])).
% 3.39/3.62  thf('105', plain, ((v1_relat_1 @ sk_D)),
% 3.39/3.62      inference('sup-', [status(thm)], ['73', '74'])).
% 3.39/3.62  thf('106', plain, ((v1_relat_1 @ sk_E)),
% 3.39/3.62      inference('sup-', [status(thm)], ['5', '6'])).
% 3.39/3.62  thf('107', plain,
% 3.39/3.62      (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))
% 3.39/3.62         = (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))),
% 3.39/3.62      inference('demod', [status(thm)], ['93', '104', '105', '106'])).
% 3.39/3.62  thf('108', plain,
% 3.39/3.62      ((r1_tarski @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) @ 
% 3.39/3.62        (k2_relat_1 @ sk_E))),
% 3.39/3.62      inference('demod', [status(thm)], ['80', '107'])).
% 3.39/3.62  thf('109', plain,
% 3.39/3.62      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 3.39/3.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 3.39/3.62      inference('demod', [status(thm)], ['54', '55', '64'])).
% 3.39/3.62  thf(redefinition_k2_relset_1, axiom,
% 3.39/3.62    (![A:$i,B:$i,C:$i]:
% 3.39/3.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.39/3.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.39/3.62  thf('110', plain,
% 3.39/3.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.39/3.62         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 3.39/3.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 3.39/3.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.39/3.62  thf('111', plain,
% 3.39/3.62      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 3.39/3.62         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 3.39/3.62      inference('sup-', [status(thm)], ['109', '110'])).
% 3.39/3.62  thf('112', plain,
% 3.39/3.62      (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))
% 3.39/3.62         = (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))),
% 3.39/3.62      inference('demod', [status(thm)], ['93', '104', '105', '106'])).
% 3.39/3.62  thf('113', plain,
% 3.39/3.62      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 3.39/3.62         = (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))),
% 3.39/3.62      inference('demod', [status(thm)], ['111', '112'])).
% 3.39/3.62  thf('114', plain,
% 3.39/3.62      (((k2_relset_1 @ sk_A @ sk_C @ 
% 3.39/3.62         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('115', plain,
% 3.39/3.62      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 3.39/3.62         = (k5_relat_1 @ sk_D @ sk_E))),
% 3.39/3.62      inference('demod', [status(thm)], ['62', '63'])).
% 3.39/3.62  thf('116', plain,
% 3.39/3.62      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 3.39/3.62      inference('demod', [status(thm)], ['114', '115'])).
% 3.39/3.62  thf('117', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 3.39/3.62      inference('sup+', [status(thm)], ['113', '116'])).
% 3.39/3.62  thf('118', plain, ((r1_tarski @ sk_C @ (k2_relat_1 @ sk_E))),
% 3.39/3.62      inference('demod', [status(thm)], ['108', '117'])).
% 3.39/3.62  thf('119', plain, (((sk_C) = (k2_relat_1 @ sk_E))),
% 3.39/3.62      inference('demod', [status(thm)], ['47', '118'])).
% 3.39/3.62  thf('120', plain, (((k10_relat_1 @ sk_E @ sk_C) = (sk_B))),
% 3.39/3.62      inference('demod', [status(thm)], ['38', '119'])).
% 3.39/3.62  thf('121', plain,
% 3.39/3.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('122', plain,
% 3.39/3.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.39/3.62         ((v5_relat_1 @ X20 @ X22)
% 3.39/3.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.39/3.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.39/3.62  thf('123', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 3.39/3.62      inference('sup-', [status(thm)], ['121', '122'])).
% 3.39/3.62  thf('124', plain,
% 3.39/3.62      (![X3 : $i, X4 : $i]:
% 3.39/3.62         (~ (v5_relat_1 @ X3 @ X4)
% 3.39/3.62          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 3.39/3.62          | ~ (v1_relat_1 @ X3))),
% 3.39/3.62      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.39/3.62  thf('125', plain,
% 3.39/3.62      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 3.39/3.62      inference('sup-', [status(thm)], ['123', '124'])).
% 3.39/3.62  thf('126', plain, ((v1_relat_1 @ sk_D)),
% 3.39/3.62      inference('sup-', [status(thm)], ['73', '74'])).
% 3.39/3.62  thf('127', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 3.39/3.62      inference('demod', [status(thm)], ['125', '126'])).
% 3.39/3.62  thf('128', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 3.39/3.62      inference('demod', [status(thm)], ['26', '33', '36'])).
% 3.39/3.62  thf(t164_funct_1, axiom,
% 3.39/3.62    (![A:$i,B:$i]:
% 3.39/3.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.39/3.62       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 3.39/3.62         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 3.39/3.62  thf('129', plain,
% 3.39/3.62      (![X15 : $i, X16 : $i]:
% 3.39/3.62         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 3.39/3.62          | ~ (v2_funct_1 @ X16)
% 3.39/3.62          | ((k10_relat_1 @ X16 @ (k9_relat_1 @ X16 @ X15)) = (X15))
% 3.39/3.62          | ~ (v1_funct_1 @ X16)
% 3.39/3.62          | ~ (v1_relat_1 @ X16))),
% 3.39/3.62      inference('cnf', [status(esa)], [t164_funct_1])).
% 3.39/3.62  thf('130', plain,
% 3.39/3.62      (![X0 : $i]:
% 3.39/3.62         (~ (r1_tarski @ X0 @ sk_B)
% 3.39/3.62          | ~ (v1_relat_1 @ sk_E)
% 3.39/3.62          | ~ (v1_funct_1 @ sk_E)
% 3.39/3.62          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0))
% 3.39/3.62          | ~ (v2_funct_1 @ sk_E))),
% 3.39/3.62      inference('sup-', [status(thm)], ['128', '129'])).
% 3.39/3.62  thf('131', plain, ((v1_relat_1 @ sk_E)),
% 3.39/3.62      inference('sup-', [status(thm)], ['5', '6'])).
% 3.39/3.62  thf('132', plain, ((v1_funct_1 @ sk_E)),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('133', plain, ((v2_funct_1 @ sk_E)),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('134', plain,
% 3.39/3.62      (![X0 : $i]:
% 3.39/3.62         (~ (r1_tarski @ X0 @ sk_B)
% 3.39/3.62          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0)))),
% 3.39/3.62      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 3.39/3.62  thf('135', plain,
% 3.39/3.62      (((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 3.39/3.62         = (k2_relat_1 @ sk_D))),
% 3.39/3.62      inference('sup-', [status(thm)], ['127', '134'])).
% 3.39/3.62  thf('136', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 3.39/3.62      inference('sup+', [status(thm)], ['113', '116'])).
% 3.39/3.62  thf('137', plain, (((k10_relat_1 @ sk_E @ sk_C) = (k2_relat_1 @ sk_D))),
% 3.39/3.62      inference('demod', [status(thm)], ['135', '136'])).
% 3.39/3.62  thf('138', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 3.39/3.62      inference('sup+', [status(thm)], ['120', '137'])).
% 3.39/3.62  thf('139', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('140', plain,
% 3.39/3.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.39/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.62  thf('141', plain,
% 3.39/3.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.39/3.62         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 3.39/3.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 3.39/3.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.39/3.62  thf('142', plain,
% 3.39/3.62      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.39/3.62      inference('sup-', [status(thm)], ['140', '141'])).
% 3.39/3.62  thf('143', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 3.39/3.62      inference('demod', [status(thm)], ['139', '142'])).
% 3.39/3.62  thf('144', plain, ($false),
% 3.39/3.62      inference('simplify_reflect-', [status(thm)], ['138', '143'])).
% 3.39/3.62  
% 3.39/3.62  % SZS output end Refutation
% 3.39/3.62  
% 3.39/3.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
