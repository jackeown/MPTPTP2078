%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H1idyb68ok

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:57 EST 2020

% Result     : Theorem 4.90s
% Output     : Refutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 625 expanded)
%              Number of leaves         :   50 ( 206 expanded)
%              Depth                    :   16
%              Number of atoms          : 1518 (12365 expanded)
%              Number of equality atoms :  103 ( 731 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X11: $i] :
      ( ( ( k10_relat_1 @ X11 @ ( k2_relat_1 @ X11 ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('41',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k9_relat_1 @ X9 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k9_relat_1 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_D @ sk_A ) @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k9_relat_1 @ sk_D @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['44','45'])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['44','45'])).

thf('54',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('55',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('56',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('57',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['44','45'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','59'])).

thf('61',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X5 @ X6 ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_relat_1 @ sk_E )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ X0 ) @ ( k9_relat_1 @ sk_E @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['5','6'])).

thf('67',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['5','6'])).

thf('68',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_E )
    = ( k9_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_E @ X0 ) @ ( k2_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) @ ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['60','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['5','6'])).

thf('73',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) @ ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('74',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
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

thf('78',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
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

thf('86',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 )
        = ( k5_relat_1 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['82','83','92'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('94',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('95',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('98',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['95','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('102',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['100','101'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('103',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['5','6'])).

thf('106',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['95','98'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['75','99','106','107'])).

thf('109',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['38','108'])).

thf('110',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k9_relat_1 @ X9 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('111',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k10_relat_1 @ X14 @ X15 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X14 ) @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('112',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('114',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('116',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['44','45'])).

thf('118',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['26','33','36'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('120',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X17 ) @ ( k9_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v2_funct_1 @ sk_E )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['5','6'])).

thf('123',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['118','125'])).

thf('127',plain,
    ( ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
      = ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['111','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['5','6'])).

thf('129',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,
    ( ( ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
      = ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['110','131'])).

thf('133',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['44','45'])).

thf('134',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['5','6'])).

thf('135',plain,
    ( ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['95','98'])).

thf('137',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['109','137'])).

thf('139',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H1idyb68ok
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:21:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.90/5.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.90/5.09  % Solved by: fo/fo7.sh
% 4.90/5.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.90/5.09  % done 1244 iterations in 4.623s
% 4.90/5.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.90/5.09  % SZS output start Refutation
% 4.90/5.09  thf(sk_B_type, type, sk_B: $i).
% 4.90/5.09  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.90/5.09  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.90/5.09  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.90/5.09  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.90/5.09  thf(sk_E_type, type, sk_E: $i).
% 4.90/5.09  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.90/5.09  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.90/5.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.90/5.09  thf(sk_D_type, type, sk_D: $i).
% 4.90/5.09  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.90/5.09  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.90/5.09  thf(sk_C_type, type, sk_C: $i).
% 4.90/5.09  thf(sk_A_type, type, sk_A: $i).
% 4.90/5.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.90/5.09  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.90/5.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.90/5.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.90/5.09  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.90/5.09  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 4.90/5.09  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.90/5.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.90/5.09  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.90/5.09  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 4.90/5.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.90/5.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.90/5.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.90/5.09  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.90/5.09  thf(t28_funct_2, conjecture,
% 4.90/5.09    (![A:$i,B:$i,C:$i,D:$i]:
% 4.90/5.09     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.90/5.09         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.90/5.09       ( ![E:$i]:
% 4.90/5.09         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.90/5.09             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.90/5.09           ( ( ( ( k2_relset_1 @
% 4.90/5.09                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 4.90/5.09                 ( C ) ) & 
% 4.90/5.09               ( v2_funct_1 @ E ) ) =>
% 4.90/5.09             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 4.90/5.09               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 4.90/5.09  thf(zf_stmt_0, negated_conjecture,
% 4.90/5.09    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.90/5.09        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.90/5.09            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.90/5.09          ( ![E:$i]:
% 4.90/5.09            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.90/5.09                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.90/5.09              ( ( ( ( k2_relset_1 @
% 4.90/5.09                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 4.90/5.09                    ( C ) ) & 
% 4.90/5.09                  ( v2_funct_1 @ E ) ) =>
% 4.90/5.09                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 4.90/5.09                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 4.90/5.09    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 4.90/5.09  thf('0', plain,
% 4.90/5.09      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf(cc2_relset_1, axiom,
% 4.90/5.09    (![A:$i,B:$i,C:$i]:
% 4.90/5.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.90/5.09       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.90/5.09  thf('1', plain,
% 4.90/5.09      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.90/5.09         ((v4_relat_1 @ X21 @ X22)
% 4.90/5.09          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.90/5.09      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.90/5.09  thf('2', plain, ((v4_relat_1 @ sk_E @ sk_B)),
% 4.90/5.09      inference('sup-', [status(thm)], ['0', '1'])).
% 4.90/5.09  thf(t209_relat_1, axiom,
% 4.90/5.09    (![A:$i,B:$i]:
% 4.90/5.09     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 4.90/5.09       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 4.90/5.09  thf('3', plain,
% 4.90/5.09      (![X12 : $i, X13 : $i]:
% 4.90/5.09         (((X12) = (k7_relat_1 @ X12 @ X13))
% 4.90/5.09          | ~ (v4_relat_1 @ X12 @ X13)
% 4.90/5.09          | ~ (v1_relat_1 @ X12))),
% 4.90/5.09      inference('cnf', [status(esa)], [t209_relat_1])).
% 4.90/5.09  thf('4', plain,
% 4.90/5.09      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_B)))),
% 4.90/5.09      inference('sup-', [status(thm)], ['2', '3'])).
% 4.90/5.09  thf('5', plain,
% 4.90/5.09      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf(cc1_relset_1, axiom,
% 4.90/5.09    (![A:$i,B:$i,C:$i]:
% 4.90/5.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.90/5.09       ( v1_relat_1 @ C ) ))).
% 4.90/5.09  thf('6', plain,
% 4.90/5.09      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.90/5.09         ((v1_relat_1 @ X18)
% 4.90/5.09          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 4.90/5.09      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.90/5.09  thf('7', plain, ((v1_relat_1 @ sk_E)),
% 4.90/5.09      inference('sup-', [status(thm)], ['5', '6'])).
% 4.90/5.09  thf('8', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 4.90/5.09      inference('demod', [status(thm)], ['4', '7'])).
% 4.90/5.09  thf(t148_relat_1, axiom,
% 4.90/5.09    (![A:$i,B:$i]:
% 4.90/5.09     ( ( v1_relat_1 @ B ) =>
% 4.90/5.09       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 4.90/5.09  thf('9', plain,
% 4.90/5.09      (![X7 : $i, X8 : $i]:
% 4.90/5.09         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 4.90/5.09          | ~ (v1_relat_1 @ X7))),
% 4.90/5.09      inference('cnf', [status(esa)], [t148_relat_1])).
% 4.90/5.09  thf(t169_relat_1, axiom,
% 4.90/5.09    (![A:$i]:
% 4.90/5.09     ( ( v1_relat_1 @ A ) =>
% 4.90/5.09       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 4.90/5.09  thf('10', plain,
% 4.90/5.09      (![X11 : $i]:
% 4.90/5.09         (((k10_relat_1 @ X11 @ (k2_relat_1 @ X11)) = (k1_relat_1 @ X11))
% 4.90/5.09          | ~ (v1_relat_1 @ X11))),
% 4.90/5.09      inference('cnf', [status(esa)], [t169_relat_1])).
% 4.90/5.09  thf('11', plain,
% 4.90/5.09      (![X0 : $i, X1 : $i]:
% 4.90/5.09         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 4.90/5.09            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 4.90/5.09          | ~ (v1_relat_1 @ X1)
% 4.90/5.09          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 4.90/5.09      inference('sup+', [status(thm)], ['9', '10'])).
% 4.90/5.09  thf('12', plain,
% 4.90/5.09      ((~ (v1_relat_1 @ sk_E)
% 4.90/5.09        | ~ (v1_relat_1 @ sk_E)
% 4.90/5.09        | ((k10_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 4.90/5.09            (k9_relat_1 @ sk_E @ sk_B))
% 4.90/5.09            = (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))))),
% 4.90/5.09      inference('sup-', [status(thm)], ['8', '11'])).
% 4.90/5.09  thf('13', plain, ((v1_relat_1 @ sk_E)),
% 4.90/5.09      inference('sup-', [status(thm)], ['5', '6'])).
% 4.90/5.09  thf('14', plain, ((v1_relat_1 @ sk_E)),
% 4.90/5.09      inference('sup-', [status(thm)], ['5', '6'])).
% 4.90/5.09  thf('15', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 4.90/5.09      inference('demod', [status(thm)], ['4', '7'])).
% 4.90/5.09  thf('16', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 4.90/5.09      inference('demod', [status(thm)], ['4', '7'])).
% 4.90/5.09  thf('17', plain,
% 4.90/5.09      (((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ sk_B)) = (k1_relat_1 @ sk_E))),
% 4.90/5.09      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 4.90/5.09  thf('18', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 4.90/5.09      inference('demod', [status(thm)], ['4', '7'])).
% 4.90/5.09  thf('19', plain,
% 4.90/5.09      (![X7 : $i, X8 : $i]:
% 4.90/5.09         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 4.90/5.09          | ~ (v1_relat_1 @ X7))),
% 4.90/5.09      inference('cnf', [status(esa)], [t148_relat_1])).
% 4.90/5.09  thf('20', plain,
% 4.90/5.09      ((((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))
% 4.90/5.09        | ~ (v1_relat_1 @ sk_E))),
% 4.90/5.09      inference('sup+', [status(thm)], ['18', '19'])).
% 4.90/5.09  thf('21', plain, ((v1_relat_1 @ sk_E)),
% 4.90/5.09      inference('sup-', [status(thm)], ['5', '6'])).
% 4.90/5.09  thf('22', plain, (((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))),
% 4.90/5.09      inference('demod', [status(thm)], ['20', '21'])).
% 4.90/5.09  thf('23', plain,
% 4.90/5.09      (((k10_relat_1 @ sk_E @ (k2_relat_1 @ sk_E)) = (k1_relat_1 @ sk_E))),
% 4.90/5.09      inference('demod', [status(thm)], ['17', '22'])).
% 4.90/5.09  thf('24', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf(d1_funct_2, axiom,
% 4.90/5.09    (![A:$i,B:$i,C:$i]:
% 4.90/5.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.90/5.09       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.90/5.09           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.90/5.09             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.90/5.09         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.90/5.09           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.90/5.09             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.90/5.09  thf(zf_stmt_1, axiom,
% 4.90/5.09    (![C:$i,B:$i,A:$i]:
% 4.90/5.09     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.90/5.09       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.90/5.09  thf('25', plain,
% 4.90/5.09      (![X32 : $i, X33 : $i, X34 : $i]:
% 4.90/5.09         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 4.90/5.09          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 4.90/5.09          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.90/5.09  thf('26', plain,
% 4.90/5.09      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 4.90/5.09        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 4.90/5.09      inference('sup-', [status(thm)], ['24', '25'])).
% 4.90/5.09  thf(zf_stmt_2, axiom,
% 4.90/5.09    (![B:$i,A:$i]:
% 4.90/5.09     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.90/5.09       ( zip_tseitin_0 @ B @ A ) ))).
% 4.90/5.09  thf('27', plain,
% 4.90/5.09      (![X30 : $i, X31 : $i]:
% 4.90/5.09         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.90/5.09  thf('28', plain,
% 4.90/5.09      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.90/5.09  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.90/5.09  thf(zf_stmt_5, axiom,
% 4.90/5.09    (![A:$i,B:$i,C:$i]:
% 4.90/5.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.90/5.09       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.90/5.09         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.90/5.09           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.90/5.09             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.90/5.09  thf('29', plain,
% 4.90/5.09      (![X35 : $i, X36 : $i, X37 : $i]:
% 4.90/5.09         (~ (zip_tseitin_0 @ X35 @ X36)
% 4.90/5.09          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 4.90/5.09          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.90/5.09  thf('30', plain,
% 4.90/5.09      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 4.90/5.09      inference('sup-', [status(thm)], ['28', '29'])).
% 4.90/5.09  thf('31', plain,
% 4.90/5.09      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 4.90/5.09      inference('sup-', [status(thm)], ['27', '30'])).
% 4.90/5.09  thf('32', plain, (((sk_C) != (k1_xboole_0))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('33', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 4.90/5.09      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 4.90/5.09  thf('34', plain,
% 4.90/5.09      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf(redefinition_k1_relset_1, axiom,
% 4.90/5.09    (![A:$i,B:$i,C:$i]:
% 4.90/5.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.90/5.09       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.90/5.09  thf('35', plain,
% 4.90/5.09      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.90/5.09         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 4.90/5.09          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 4.90/5.09      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.90/5.09  thf('36', plain,
% 4.90/5.09      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 4.90/5.09      inference('sup-', [status(thm)], ['34', '35'])).
% 4.90/5.09  thf('37', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 4.90/5.09      inference('demod', [status(thm)], ['26', '33', '36'])).
% 4.90/5.09  thf('38', plain, (((k10_relat_1 @ sk_E @ (k2_relat_1 @ sk_E)) = (sk_B))),
% 4.90/5.09      inference('demod', [status(thm)], ['23', '37'])).
% 4.90/5.09  thf('39', plain,
% 4.90/5.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('40', plain,
% 4.90/5.09      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.90/5.09         ((v4_relat_1 @ X21 @ X22)
% 4.90/5.09          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.90/5.09      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.90/5.09  thf('41', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 4.90/5.09      inference('sup-', [status(thm)], ['39', '40'])).
% 4.90/5.09  thf('42', plain,
% 4.90/5.09      (![X12 : $i, X13 : $i]:
% 4.90/5.09         (((X12) = (k7_relat_1 @ X12 @ X13))
% 4.90/5.09          | ~ (v4_relat_1 @ X12 @ X13)
% 4.90/5.09          | ~ (v1_relat_1 @ X12))),
% 4.90/5.09      inference('cnf', [status(esa)], [t209_relat_1])).
% 4.90/5.09  thf('43', plain,
% 4.90/5.09      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_A)))),
% 4.90/5.09      inference('sup-', [status(thm)], ['41', '42'])).
% 4.90/5.09  thf('44', plain,
% 4.90/5.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('45', plain,
% 4.90/5.09      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.90/5.09         ((v1_relat_1 @ X18)
% 4.90/5.09          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 4.90/5.09      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.90/5.09  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 4.90/5.09      inference('sup-', [status(thm)], ['44', '45'])).
% 4.90/5.09  thf('47', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 4.90/5.09      inference('demod', [status(thm)], ['43', '46'])).
% 4.90/5.09  thf('48', plain,
% 4.90/5.09      (![X7 : $i, X8 : $i]:
% 4.90/5.09         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 4.90/5.09          | ~ (v1_relat_1 @ X7))),
% 4.90/5.09      inference('cnf', [status(esa)], [t148_relat_1])).
% 4.90/5.09  thf(t160_relat_1, axiom,
% 4.90/5.09    (![A:$i]:
% 4.90/5.09     ( ( v1_relat_1 @ A ) =>
% 4.90/5.09       ( ![B:$i]:
% 4.90/5.09         ( ( v1_relat_1 @ B ) =>
% 4.90/5.09           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 4.90/5.09             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 4.90/5.09  thf('49', plain,
% 4.90/5.09      (![X9 : $i, X10 : $i]:
% 4.90/5.09         (~ (v1_relat_1 @ X9)
% 4.90/5.09          | ((k2_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 4.90/5.09              = (k9_relat_1 @ X9 @ (k2_relat_1 @ X10)))
% 4.90/5.09          | ~ (v1_relat_1 @ X10))),
% 4.90/5.09      inference('cnf', [status(esa)], [t160_relat_1])).
% 4.90/5.09  thf('50', plain,
% 4.90/5.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.90/5.09         (((k2_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 4.90/5.09            = (k9_relat_1 @ X2 @ (k9_relat_1 @ X1 @ X0)))
% 4.90/5.09          | ~ (v1_relat_1 @ X1)
% 4.90/5.09          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 4.90/5.09          | ~ (v1_relat_1 @ X2))),
% 4.90/5.09      inference('sup+', [status(thm)], ['48', '49'])).
% 4.90/5.09  thf('51', plain,
% 4.90/5.09      (![X0 : $i]:
% 4.90/5.09         (~ (v1_relat_1 @ sk_D)
% 4.90/5.09          | ~ (v1_relat_1 @ X0)
% 4.90/5.09          | ~ (v1_relat_1 @ sk_D)
% 4.90/5.09          | ((k2_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_D @ sk_A) @ X0))
% 4.90/5.09              = (k9_relat_1 @ X0 @ (k9_relat_1 @ sk_D @ sk_A))))),
% 4.90/5.09      inference('sup-', [status(thm)], ['47', '50'])).
% 4.90/5.09  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 4.90/5.09      inference('sup-', [status(thm)], ['44', '45'])).
% 4.90/5.09  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 4.90/5.09      inference('sup-', [status(thm)], ['44', '45'])).
% 4.90/5.09  thf('54', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 4.90/5.09      inference('demod', [status(thm)], ['43', '46'])).
% 4.90/5.09  thf('55', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 4.90/5.09      inference('demod', [status(thm)], ['43', '46'])).
% 4.90/5.09  thf('56', plain,
% 4.90/5.09      (![X7 : $i, X8 : $i]:
% 4.90/5.09         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 4.90/5.09          | ~ (v1_relat_1 @ X7))),
% 4.90/5.09      inference('cnf', [status(esa)], [t148_relat_1])).
% 4.90/5.09  thf('57', plain,
% 4.90/5.09      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_A))
% 4.90/5.09        | ~ (v1_relat_1 @ sk_D))),
% 4.90/5.09      inference('sup+', [status(thm)], ['55', '56'])).
% 4.90/5.09  thf('58', plain, ((v1_relat_1 @ sk_D)),
% 4.90/5.09      inference('sup-', [status(thm)], ['44', '45'])).
% 4.90/5.09  thf('59', plain, (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_A))),
% 4.90/5.09      inference('demod', [status(thm)], ['57', '58'])).
% 4.90/5.09  thf('60', plain,
% 4.90/5.09      (![X0 : $i]:
% 4.90/5.09         (~ (v1_relat_1 @ X0)
% 4.90/5.09          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0))
% 4.90/5.09              = (k9_relat_1 @ X0 @ (k2_relat_1 @ sk_D))))),
% 4.90/5.09      inference('demod', [status(thm)], ['51', '52', '53', '54', '59'])).
% 4.90/5.09  thf('61', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 4.90/5.09      inference('demod', [status(thm)], ['4', '7'])).
% 4.90/5.09  thf('62', plain,
% 4.90/5.09      (![X7 : $i, X8 : $i]:
% 4.90/5.09         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 4.90/5.09          | ~ (v1_relat_1 @ X7))),
% 4.90/5.09      inference('cnf', [status(esa)], [t148_relat_1])).
% 4.90/5.09  thf(t144_relat_1, axiom,
% 4.90/5.09    (![A:$i,B:$i]:
% 4.90/5.09     ( ( v1_relat_1 @ B ) =>
% 4.90/5.09       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 4.90/5.09  thf('63', plain,
% 4.90/5.09      (![X5 : $i, X6 : $i]:
% 4.90/5.09         ((r1_tarski @ (k9_relat_1 @ X5 @ X6) @ (k2_relat_1 @ X5))
% 4.90/5.09          | ~ (v1_relat_1 @ X5))),
% 4.90/5.09      inference('cnf', [status(esa)], [t144_relat_1])).
% 4.90/5.09  thf('64', plain,
% 4.90/5.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.90/5.09         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 4.90/5.09           (k9_relat_1 @ X1 @ X0))
% 4.90/5.09          | ~ (v1_relat_1 @ X1)
% 4.90/5.09          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 4.90/5.09      inference('sup+', [status(thm)], ['62', '63'])).
% 4.90/5.09  thf('65', plain,
% 4.90/5.09      (![X0 : $i]:
% 4.90/5.09         (~ (v1_relat_1 @ sk_E)
% 4.90/5.09          | ~ (v1_relat_1 @ sk_E)
% 4.90/5.09          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ X0) @ 
% 4.90/5.09             (k9_relat_1 @ sk_E @ sk_B)))),
% 4.90/5.09      inference('sup-', [status(thm)], ['61', '64'])).
% 4.90/5.09  thf('66', plain, ((v1_relat_1 @ sk_E)),
% 4.90/5.09      inference('sup-', [status(thm)], ['5', '6'])).
% 4.90/5.09  thf('67', plain, ((v1_relat_1 @ sk_E)),
% 4.90/5.09      inference('sup-', [status(thm)], ['5', '6'])).
% 4.90/5.09  thf('68', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 4.90/5.09      inference('demod', [status(thm)], ['4', '7'])).
% 4.90/5.09  thf('69', plain, (((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))),
% 4.90/5.09      inference('demod', [status(thm)], ['20', '21'])).
% 4.90/5.09  thf('70', plain,
% 4.90/5.09      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_E @ X0) @ (k2_relat_1 @ sk_E))),
% 4.90/5.09      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 4.90/5.09  thf('71', plain,
% 4.90/5.09      (((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) @ 
% 4.90/5.09         (k2_relat_1 @ sk_E))
% 4.90/5.09        | ~ (v1_relat_1 @ sk_E))),
% 4.90/5.09      inference('sup+', [status(thm)], ['60', '70'])).
% 4.90/5.09  thf('72', plain, ((v1_relat_1 @ sk_E)),
% 4.90/5.09      inference('sup-', [status(thm)], ['5', '6'])).
% 4.90/5.09  thf('73', plain,
% 4.90/5.09      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) @ 
% 4.90/5.09        (k2_relat_1 @ sk_E))),
% 4.90/5.09      inference('demod', [status(thm)], ['71', '72'])).
% 4.90/5.09  thf(d10_xboole_0, axiom,
% 4.90/5.09    (![A:$i,B:$i]:
% 4.90/5.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.90/5.09  thf('74', plain,
% 4.90/5.09      (![X0 : $i, X2 : $i]:
% 4.90/5.09         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.90/5.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.90/5.09  thf('75', plain,
% 4.90/5.09      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ 
% 4.90/5.09           (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 4.90/5.09        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))))),
% 4.90/5.09      inference('sup-', [status(thm)], ['73', '74'])).
% 4.90/5.09  thf('76', plain,
% 4.90/5.09      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('77', plain,
% 4.90/5.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf(dt_k1_partfun1, axiom,
% 4.90/5.09    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.90/5.09     ( ( ( v1_funct_1 @ E ) & 
% 4.90/5.09         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.90/5.09         ( v1_funct_1 @ F ) & 
% 4.90/5.09         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.90/5.09       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.90/5.09         ( m1_subset_1 @
% 4.90/5.09           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.90/5.09           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.90/5.09  thf('78', plain,
% 4.90/5.09      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 4.90/5.09         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 4.90/5.09          | ~ (v1_funct_1 @ X38)
% 4.90/5.09          | ~ (v1_funct_1 @ X41)
% 4.90/5.09          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 4.90/5.09          | (m1_subset_1 @ (k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41) @ 
% 4.90/5.09             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X43))))),
% 4.90/5.09      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.90/5.09  thf('79', plain,
% 4.90/5.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.90/5.09         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 4.90/5.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.90/5.09          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.90/5.09          | ~ (v1_funct_1 @ X1)
% 4.90/5.09          | ~ (v1_funct_1 @ sk_D))),
% 4.90/5.09      inference('sup-', [status(thm)], ['77', '78'])).
% 4.90/5.09  thf('80', plain, ((v1_funct_1 @ sk_D)),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('81', plain,
% 4.90/5.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.90/5.09         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 4.90/5.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.90/5.09          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.90/5.09          | ~ (v1_funct_1 @ X1))),
% 4.90/5.09      inference('demod', [status(thm)], ['79', '80'])).
% 4.90/5.09  thf('82', plain,
% 4.90/5.09      ((~ (v1_funct_1 @ sk_E)
% 4.90/5.09        | (m1_subset_1 @ 
% 4.90/5.09           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 4.90/5.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 4.90/5.09      inference('sup-', [status(thm)], ['76', '81'])).
% 4.90/5.09  thf('83', plain, ((v1_funct_1 @ sk_E)),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('84', plain,
% 4.90/5.09      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('85', plain,
% 4.90/5.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf(redefinition_k1_partfun1, axiom,
% 4.90/5.09    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.90/5.09     ( ( ( v1_funct_1 @ E ) & 
% 4.90/5.09         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.90/5.09         ( v1_funct_1 @ F ) & 
% 4.90/5.09         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.90/5.09       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 4.90/5.09  thf('86', plain,
% 4.90/5.09      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 4.90/5.09         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 4.90/5.09          | ~ (v1_funct_1 @ X44)
% 4.90/5.09          | ~ (v1_funct_1 @ X47)
% 4.90/5.09          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 4.90/5.09          | ((k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47)
% 4.90/5.09              = (k5_relat_1 @ X44 @ X47)))),
% 4.90/5.09      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 4.90/5.09  thf('87', plain,
% 4.90/5.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.90/5.09         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 4.90/5.09            = (k5_relat_1 @ sk_D @ X0))
% 4.90/5.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.90/5.09          | ~ (v1_funct_1 @ X0)
% 4.90/5.09          | ~ (v1_funct_1 @ sk_D))),
% 4.90/5.09      inference('sup-', [status(thm)], ['85', '86'])).
% 4.90/5.09  thf('88', plain, ((v1_funct_1 @ sk_D)),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('89', plain,
% 4.90/5.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.90/5.09         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 4.90/5.09            = (k5_relat_1 @ sk_D @ X0))
% 4.90/5.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.90/5.09          | ~ (v1_funct_1 @ X0))),
% 4.90/5.09      inference('demod', [status(thm)], ['87', '88'])).
% 4.90/5.09  thf('90', plain,
% 4.90/5.09      ((~ (v1_funct_1 @ sk_E)
% 4.90/5.09        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 4.90/5.09            = (k5_relat_1 @ sk_D @ sk_E)))),
% 4.90/5.09      inference('sup-', [status(thm)], ['84', '89'])).
% 4.90/5.09  thf('91', plain, ((v1_funct_1 @ sk_E)),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('92', plain,
% 4.90/5.09      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 4.90/5.09         = (k5_relat_1 @ sk_D @ sk_E))),
% 4.90/5.09      inference('demod', [status(thm)], ['90', '91'])).
% 4.90/5.09  thf('93', plain,
% 4.90/5.09      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 4.90/5.09        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 4.90/5.09      inference('demod', [status(thm)], ['82', '83', '92'])).
% 4.90/5.09  thf(redefinition_k2_relset_1, axiom,
% 4.90/5.09    (![A:$i,B:$i,C:$i]:
% 4.90/5.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.90/5.09       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.90/5.09  thf('94', plain,
% 4.90/5.09      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.90/5.09         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 4.90/5.09          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 4.90/5.09      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.90/5.09  thf('95', plain,
% 4.90/5.09      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 4.90/5.09         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 4.90/5.09      inference('sup-', [status(thm)], ['93', '94'])).
% 4.90/5.09  thf('96', plain,
% 4.90/5.09      (((k2_relset_1 @ sk_A @ sk_C @ 
% 4.90/5.09         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('97', plain,
% 4.90/5.09      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 4.90/5.09         = (k5_relat_1 @ sk_D @ sk_E))),
% 4.90/5.09      inference('demod', [status(thm)], ['90', '91'])).
% 4.90/5.09  thf('98', plain,
% 4.90/5.09      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 4.90/5.09      inference('demod', [status(thm)], ['96', '97'])).
% 4.90/5.09  thf('99', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 4.90/5.09      inference('sup+', [status(thm)], ['95', '98'])).
% 4.90/5.09  thf('100', plain,
% 4.90/5.09      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('101', plain,
% 4.90/5.09      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.90/5.09         ((v5_relat_1 @ X21 @ X23)
% 4.90/5.09          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.90/5.09      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.90/5.09  thf('102', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 4.90/5.09      inference('sup-', [status(thm)], ['100', '101'])).
% 4.90/5.09  thf(d19_relat_1, axiom,
% 4.90/5.09    (![A:$i,B:$i]:
% 4.90/5.09     ( ( v1_relat_1 @ B ) =>
% 4.90/5.09       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.90/5.09  thf('103', plain,
% 4.90/5.09      (![X3 : $i, X4 : $i]:
% 4.90/5.09         (~ (v5_relat_1 @ X3 @ X4)
% 4.90/5.09          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 4.90/5.09          | ~ (v1_relat_1 @ X3))),
% 4.90/5.09      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.90/5.09  thf('104', plain,
% 4.90/5.09      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 4.90/5.09      inference('sup-', [status(thm)], ['102', '103'])).
% 4.90/5.09  thf('105', plain, ((v1_relat_1 @ sk_E)),
% 4.90/5.09      inference('sup-', [status(thm)], ['5', '6'])).
% 4.90/5.09  thf('106', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 4.90/5.09      inference('demod', [status(thm)], ['104', '105'])).
% 4.90/5.09  thf('107', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 4.90/5.09      inference('sup+', [status(thm)], ['95', '98'])).
% 4.90/5.09  thf('108', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 4.90/5.09      inference('demod', [status(thm)], ['75', '99', '106', '107'])).
% 4.90/5.09  thf('109', plain, (((k10_relat_1 @ sk_E @ sk_C) = (sk_B))),
% 4.90/5.09      inference('demod', [status(thm)], ['38', '108'])).
% 4.90/5.09  thf('110', plain,
% 4.90/5.09      (![X9 : $i, X10 : $i]:
% 4.90/5.09         (~ (v1_relat_1 @ X9)
% 4.90/5.09          | ((k2_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 4.90/5.09              = (k9_relat_1 @ X9 @ (k2_relat_1 @ X10)))
% 4.90/5.09          | ~ (v1_relat_1 @ X10))),
% 4.90/5.09      inference('cnf', [status(esa)], [t160_relat_1])).
% 4.90/5.09  thf(t155_funct_1, axiom,
% 4.90/5.09    (![A:$i,B:$i]:
% 4.90/5.09     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.90/5.09       ( ( v2_funct_1 @ B ) =>
% 4.90/5.09         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 4.90/5.09  thf('111', plain,
% 4.90/5.09      (![X14 : $i, X15 : $i]:
% 4.90/5.09         (~ (v2_funct_1 @ X14)
% 4.90/5.09          | ((k10_relat_1 @ X14 @ X15)
% 4.90/5.09              = (k9_relat_1 @ (k2_funct_1 @ X14) @ X15))
% 4.90/5.09          | ~ (v1_funct_1 @ X14)
% 4.90/5.09          | ~ (v1_relat_1 @ X14))),
% 4.90/5.09      inference('cnf', [status(esa)], [t155_funct_1])).
% 4.90/5.09  thf('112', plain,
% 4.90/5.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('113', plain,
% 4.90/5.09      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.90/5.09         ((v5_relat_1 @ X21 @ X23)
% 4.90/5.09          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.90/5.09      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.90/5.09  thf('114', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 4.90/5.09      inference('sup-', [status(thm)], ['112', '113'])).
% 4.90/5.09  thf('115', plain,
% 4.90/5.09      (![X3 : $i, X4 : $i]:
% 4.90/5.09         (~ (v5_relat_1 @ X3 @ X4)
% 4.90/5.09          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 4.90/5.09          | ~ (v1_relat_1 @ X3))),
% 4.90/5.09      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.90/5.09  thf('116', plain,
% 4.90/5.09      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 4.90/5.09      inference('sup-', [status(thm)], ['114', '115'])).
% 4.90/5.09  thf('117', plain, ((v1_relat_1 @ sk_D)),
% 4.90/5.09      inference('sup-', [status(thm)], ['44', '45'])).
% 4.90/5.09  thf('118', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 4.90/5.09      inference('demod', [status(thm)], ['116', '117'])).
% 4.90/5.09  thf('119', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 4.90/5.09      inference('demod', [status(thm)], ['26', '33', '36'])).
% 4.90/5.09  thf(t177_funct_1, axiom,
% 4.90/5.09    (![A:$i]:
% 4.90/5.09     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.90/5.09       ( ![B:$i]:
% 4.90/5.09         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 4.90/5.09           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 4.90/5.09             ( B ) ) ) ) ))).
% 4.90/5.09  thf('120', plain,
% 4.90/5.09      (![X16 : $i, X17 : $i]:
% 4.90/5.09         (~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 4.90/5.09          | ((k9_relat_1 @ (k2_funct_1 @ X17) @ (k9_relat_1 @ X17 @ X16))
% 4.90/5.09              = (X16))
% 4.90/5.09          | ~ (v2_funct_1 @ X17)
% 4.90/5.09          | ~ (v1_funct_1 @ X17)
% 4.90/5.09          | ~ (v1_relat_1 @ X17))),
% 4.90/5.09      inference('cnf', [status(esa)], [t177_funct_1])).
% 4.90/5.09  thf('121', plain,
% 4.90/5.09      (![X0 : $i]:
% 4.90/5.09         (~ (r1_tarski @ X0 @ sk_B)
% 4.90/5.09          | ~ (v1_relat_1 @ sk_E)
% 4.90/5.09          | ~ (v1_funct_1 @ sk_E)
% 4.90/5.09          | ~ (v2_funct_1 @ sk_E)
% 4.90/5.09          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k9_relat_1 @ sk_E @ X0))
% 4.90/5.09              = (X0)))),
% 4.90/5.09      inference('sup-', [status(thm)], ['119', '120'])).
% 4.90/5.09  thf('122', plain, ((v1_relat_1 @ sk_E)),
% 4.90/5.09      inference('sup-', [status(thm)], ['5', '6'])).
% 4.90/5.09  thf('123', plain, ((v1_funct_1 @ sk_E)),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('124', plain, ((v2_funct_1 @ sk_E)),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('125', plain,
% 4.90/5.09      (![X0 : $i]:
% 4.90/5.09         (~ (r1_tarski @ X0 @ sk_B)
% 4.90/5.09          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k9_relat_1 @ sk_E @ X0))
% 4.90/5.09              = (X0)))),
% 4.90/5.09      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 4.90/5.09  thf('126', plain,
% 4.90/5.09      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 4.90/5.09         (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D))) = (k2_relat_1 @ sk_D))),
% 4.90/5.09      inference('sup-', [status(thm)], ['118', '125'])).
% 4.90/5.09  thf('127', plain,
% 4.90/5.09      ((((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 4.90/5.09          = (k2_relat_1 @ sk_D))
% 4.90/5.09        | ~ (v1_relat_1 @ sk_E)
% 4.90/5.09        | ~ (v1_funct_1 @ sk_E)
% 4.90/5.09        | ~ (v2_funct_1 @ sk_E))),
% 4.90/5.09      inference('sup+', [status(thm)], ['111', '126'])).
% 4.90/5.09  thf('128', plain, ((v1_relat_1 @ sk_E)),
% 4.90/5.09      inference('sup-', [status(thm)], ['5', '6'])).
% 4.90/5.09  thf('129', plain, ((v1_funct_1 @ sk_E)),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('130', plain, ((v2_funct_1 @ sk_E)),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('131', plain,
% 4.90/5.09      (((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 4.90/5.09         = (k2_relat_1 @ sk_D))),
% 4.90/5.09      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 4.90/5.09  thf('132', plain,
% 4.90/5.09      ((((k10_relat_1 @ sk_E @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 4.90/5.09          = (k2_relat_1 @ sk_D))
% 4.90/5.09        | ~ (v1_relat_1 @ sk_D)
% 4.90/5.09        | ~ (v1_relat_1 @ sk_E))),
% 4.90/5.09      inference('sup+', [status(thm)], ['110', '131'])).
% 4.90/5.09  thf('133', plain, ((v1_relat_1 @ sk_D)),
% 4.90/5.09      inference('sup-', [status(thm)], ['44', '45'])).
% 4.90/5.09  thf('134', plain, ((v1_relat_1 @ sk_E)),
% 4.90/5.09      inference('sup-', [status(thm)], ['5', '6'])).
% 4.90/5.09  thf('135', plain,
% 4.90/5.09      (((k10_relat_1 @ sk_E @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 4.90/5.09         = (k2_relat_1 @ sk_D))),
% 4.90/5.09      inference('demod', [status(thm)], ['132', '133', '134'])).
% 4.90/5.09  thf('136', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 4.90/5.09      inference('sup+', [status(thm)], ['95', '98'])).
% 4.90/5.09  thf('137', plain, (((k10_relat_1 @ sk_E @ sk_C) = (k2_relat_1 @ sk_D))),
% 4.90/5.09      inference('demod', [status(thm)], ['135', '136'])).
% 4.90/5.09  thf('138', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 4.90/5.09      inference('sup+', [status(thm)], ['109', '137'])).
% 4.90/5.09  thf('139', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('140', plain,
% 4.90/5.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.90/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.90/5.09  thf('141', plain,
% 4.90/5.09      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.90/5.09         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 4.90/5.09          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 4.90/5.09      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.90/5.09  thf('142', plain,
% 4.90/5.09      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 4.90/5.09      inference('sup-', [status(thm)], ['140', '141'])).
% 4.90/5.09  thf('143', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 4.90/5.09      inference('demod', [status(thm)], ['139', '142'])).
% 4.90/5.09  thf('144', plain, ($false),
% 4.90/5.09      inference('simplify_reflect-', [status(thm)], ['138', '143'])).
% 4.90/5.09  
% 4.90/5.09  % SZS output end Refutation
% 4.90/5.09  
% 4.90/5.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
