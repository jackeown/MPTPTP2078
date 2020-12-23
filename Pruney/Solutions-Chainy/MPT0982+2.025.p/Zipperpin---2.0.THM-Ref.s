%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gnOqKMPgHV

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:58 EST 2020

% Result     : Theorem 2.26s
% Output     : Refutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 227 expanded)
%              Number of leaves         :   46 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          : 1042 (4432 expanded)
%              Number of equality atoms :   66 ( 280 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k8_relset_1 @ X22 @ X23 @ X24 @ X23 )
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('2',plain,
    ( ( k8_relset_1 @ sk_B @ sk_C @ sk_E @ sk_C )
    = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k8_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k10_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_C @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('8',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('20',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['11','18','19'])).

thf('21',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = sk_B ),
    inference(demod,[status(thm)],['8','20'])).

thf('22',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['2','5','21'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k9_relat_1 @ X2 @ ( k2_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['11','18','19'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X4 @ ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ( ( k10_relat_1 @ X5 @ ( k9_relat_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['35','38','39','40'])).

thf('42',plain,
    ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,
    ( ( ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
      = ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['23','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['29','30'])).

thf('45',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['36','37'])).

thf('46',plain,
    ( ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
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

thf('49',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','63'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('65',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('69',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['46','70'])).

thf('72',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['22','71'])).

thf('73',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('76',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gnOqKMPgHV
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.26/2.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.26/2.43  % Solved by: fo/fo7.sh
% 2.26/2.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.26/2.43  % done 666 iterations in 1.972s
% 2.26/2.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.26/2.43  % SZS output start Refutation
% 2.26/2.43  thf(sk_A_type, type, sk_A: $i).
% 2.26/2.43  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.26/2.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.26/2.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.26/2.43  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.26/2.43  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.26/2.43  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.26/2.43  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.26/2.43  thf(sk_C_type, type, sk_C: $i).
% 2.26/2.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.26/2.43  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.26/2.43  thf(sk_B_type, type, sk_B: $i).
% 2.26/2.43  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.26/2.43  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.26/2.43  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.26/2.43  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.26/2.43  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.26/2.43  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.26/2.43  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 2.26/2.43  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.26/2.43  thf(sk_E_type, type, sk_E: $i).
% 2.26/2.43  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.26/2.43  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.26/2.43  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 2.26/2.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.26/2.43  thf(sk_D_type, type, sk_D: $i).
% 2.26/2.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.26/2.43  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.26/2.43  thf(t28_funct_2, conjecture,
% 2.26/2.43    (![A:$i,B:$i,C:$i,D:$i]:
% 2.26/2.43     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.26/2.43         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.26/2.43       ( ![E:$i]:
% 2.26/2.43         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.26/2.43             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.26/2.43           ( ( ( ( k2_relset_1 @
% 2.26/2.43                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.26/2.43                 ( C ) ) & 
% 2.26/2.43               ( v2_funct_1 @ E ) ) =>
% 2.26/2.43             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.26/2.43               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 2.26/2.43  thf(zf_stmt_0, negated_conjecture,
% 2.26/2.43    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.26/2.43        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.26/2.43            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.26/2.43          ( ![E:$i]:
% 2.26/2.43            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.26/2.43                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.26/2.43              ( ( ( ( k2_relset_1 @
% 2.26/2.43                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.26/2.43                    ( C ) ) & 
% 2.26/2.43                  ( v2_funct_1 @ E ) ) =>
% 2.26/2.43                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.26/2.43                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 2.26/2.43    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 2.26/2.43  thf('0', plain,
% 2.26/2.43      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf(t38_relset_1, axiom,
% 2.26/2.43    (![A:$i,B:$i,C:$i]:
% 2.26/2.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.26/2.43       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 2.26/2.43         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.26/2.43  thf('1', plain,
% 2.26/2.43      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.26/2.43         (((k8_relset_1 @ X22 @ X23 @ X24 @ X23)
% 2.26/2.43            = (k1_relset_1 @ X22 @ X23 @ X24))
% 2.26/2.43          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.26/2.43      inference('cnf', [status(esa)], [t38_relset_1])).
% 2.26/2.43  thf('2', plain,
% 2.26/2.43      (((k8_relset_1 @ sk_B @ sk_C @ sk_E @ sk_C)
% 2.26/2.43         = (k1_relset_1 @ sk_B @ sk_C @ sk_E))),
% 2.26/2.43      inference('sup-', [status(thm)], ['0', '1'])).
% 2.26/2.43  thf('3', plain,
% 2.26/2.43      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf(redefinition_k8_relset_1, axiom,
% 2.26/2.43    (![A:$i,B:$i,C:$i,D:$i]:
% 2.26/2.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.26/2.43       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 2.26/2.43  thf('4', plain,
% 2.26/2.43      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.26/2.43         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.26/2.43          | ((k8_relset_1 @ X19 @ X20 @ X18 @ X21) = (k10_relat_1 @ X18 @ X21)))),
% 2.26/2.43      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.26/2.43  thf('5', plain,
% 2.26/2.43      (![X0 : $i]:
% 2.26/2.43         ((k8_relset_1 @ sk_B @ sk_C @ sk_E @ X0) = (k10_relat_1 @ sk_E @ X0))),
% 2.26/2.43      inference('sup-', [status(thm)], ['3', '4'])).
% 2.26/2.43  thf('6', plain,
% 2.26/2.43      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf(redefinition_k1_relset_1, axiom,
% 2.26/2.43    (![A:$i,B:$i,C:$i]:
% 2.26/2.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.26/2.43       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.26/2.43  thf('7', plain,
% 2.26/2.43      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.26/2.43         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 2.26/2.43          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.26/2.43      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.26/2.43  thf('8', plain, (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 2.26/2.43      inference('sup-', [status(thm)], ['6', '7'])).
% 2.26/2.43  thf('9', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf(d1_funct_2, axiom,
% 2.26/2.43    (![A:$i,B:$i,C:$i]:
% 2.26/2.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.26/2.43       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.26/2.43           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.26/2.43             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.26/2.43         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.26/2.43           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.26/2.43             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.26/2.43  thf(zf_stmt_1, axiom,
% 2.26/2.43    (![C:$i,B:$i,A:$i]:
% 2.26/2.43     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.26/2.43       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.26/2.43  thf('10', plain,
% 2.26/2.43      (![X27 : $i, X28 : $i, X29 : $i]:
% 2.26/2.43         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 2.26/2.43          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 2.26/2.43          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.26/2.43  thf('11', plain,
% 2.26/2.43      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 2.26/2.43        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 2.26/2.43      inference('sup-', [status(thm)], ['9', '10'])).
% 2.26/2.43  thf(zf_stmt_2, axiom,
% 2.26/2.43    (![B:$i,A:$i]:
% 2.26/2.43     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.26/2.43       ( zip_tseitin_0 @ B @ A ) ))).
% 2.26/2.43  thf('12', plain,
% 2.26/2.43      (![X25 : $i, X26 : $i]:
% 2.26/2.43         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.26/2.43  thf('13', plain,
% 2.26/2.43      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.26/2.43  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.26/2.43  thf(zf_stmt_5, axiom,
% 2.26/2.43    (![A:$i,B:$i,C:$i]:
% 2.26/2.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.26/2.43       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.26/2.43         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.26/2.43           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.26/2.43             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.26/2.43  thf('14', plain,
% 2.26/2.43      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.26/2.43         (~ (zip_tseitin_0 @ X30 @ X31)
% 2.26/2.43          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 2.26/2.43          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.26/2.43  thf('15', plain,
% 2.26/2.43      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 2.26/2.43      inference('sup-', [status(thm)], ['13', '14'])).
% 2.26/2.43  thf('16', plain,
% 2.26/2.43      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 2.26/2.43      inference('sup-', [status(thm)], ['12', '15'])).
% 2.26/2.43  thf('17', plain, (((sk_C) != (k1_xboole_0))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf('18', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 2.26/2.43      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 2.26/2.43  thf('19', plain,
% 2.26/2.43      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 2.26/2.43      inference('sup-', [status(thm)], ['6', '7'])).
% 2.26/2.43  thf('20', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.26/2.43      inference('demod', [status(thm)], ['11', '18', '19'])).
% 2.26/2.43  thf('21', plain, (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_B))),
% 2.26/2.43      inference('demod', [status(thm)], ['8', '20'])).
% 2.26/2.43  thf('22', plain, (((k10_relat_1 @ sk_E @ sk_C) = (sk_B))),
% 2.26/2.43      inference('demod', [status(thm)], ['2', '5', '21'])).
% 2.26/2.43  thf(t160_relat_1, axiom,
% 2.26/2.43    (![A:$i]:
% 2.26/2.43     ( ( v1_relat_1 @ A ) =>
% 2.26/2.43       ( ![B:$i]:
% 2.26/2.43         ( ( v1_relat_1 @ B ) =>
% 2.26/2.43           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.26/2.43             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.26/2.43  thf('23', plain,
% 2.26/2.43      (![X2 : $i, X3 : $i]:
% 2.26/2.43         (~ (v1_relat_1 @ X2)
% 2.26/2.43          | ((k2_relat_1 @ (k5_relat_1 @ X3 @ X2))
% 2.26/2.43              = (k9_relat_1 @ X2 @ (k2_relat_1 @ X3)))
% 2.26/2.43          | ~ (v1_relat_1 @ X3))),
% 2.26/2.43      inference('cnf', [status(esa)], [t160_relat_1])).
% 2.26/2.43  thf('24', plain,
% 2.26/2.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf(cc2_relset_1, axiom,
% 2.26/2.43    (![A:$i,B:$i,C:$i]:
% 2.26/2.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.26/2.43       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.26/2.43  thf('25', plain,
% 2.26/2.43      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.26/2.43         ((v5_relat_1 @ X9 @ X11)
% 2.26/2.43          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.26/2.43      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.26/2.43  thf('26', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 2.26/2.43      inference('sup-', [status(thm)], ['24', '25'])).
% 2.26/2.43  thf(d19_relat_1, axiom,
% 2.26/2.43    (![A:$i,B:$i]:
% 2.26/2.43     ( ( v1_relat_1 @ B ) =>
% 2.26/2.43       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.26/2.43  thf('27', plain,
% 2.26/2.43      (![X0 : $i, X1 : $i]:
% 2.26/2.43         (~ (v5_relat_1 @ X0 @ X1)
% 2.26/2.43          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 2.26/2.43          | ~ (v1_relat_1 @ X0))),
% 2.26/2.43      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.26/2.43  thf('28', plain,
% 2.26/2.43      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 2.26/2.43      inference('sup-', [status(thm)], ['26', '27'])).
% 2.26/2.43  thf('29', plain,
% 2.26/2.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf(cc1_relset_1, axiom,
% 2.26/2.43    (![A:$i,B:$i,C:$i]:
% 2.26/2.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.26/2.43       ( v1_relat_1 @ C ) ))).
% 2.26/2.43  thf('30', plain,
% 2.26/2.43      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.26/2.43         ((v1_relat_1 @ X6)
% 2.26/2.43          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.26/2.43      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.26/2.43  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 2.26/2.43      inference('sup-', [status(thm)], ['29', '30'])).
% 2.26/2.43  thf('32', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 2.26/2.43      inference('demod', [status(thm)], ['28', '31'])).
% 2.26/2.43  thf('33', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.26/2.43      inference('demod', [status(thm)], ['11', '18', '19'])).
% 2.26/2.43  thf(t164_funct_1, axiom,
% 2.26/2.43    (![A:$i,B:$i]:
% 2.26/2.43     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.26/2.43       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 2.26/2.43         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 2.26/2.43  thf('34', plain,
% 2.26/2.43      (![X4 : $i, X5 : $i]:
% 2.26/2.43         (~ (r1_tarski @ X4 @ (k1_relat_1 @ X5))
% 2.26/2.43          | ~ (v2_funct_1 @ X5)
% 2.26/2.43          | ((k10_relat_1 @ X5 @ (k9_relat_1 @ X5 @ X4)) = (X4))
% 2.26/2.43          | ~ (v1_funct_1 @ X5)
% 2.26/2.43          | ~ (v1_relat_1 @ X5))),
% 2.26/2.43      inference('cnf', [status(esa)], [t164_funct_1])).
% 2.26/2.43  thf('35', plain,
% 2.26/2.43      (![X0 : $i]:
% 2.26/2.43         (~ (r1_tarski @ X0 @ sk_B)
% 2.26/2.43          | ~ (v1_relat_1 @ sk_E)
% 2.26/2.43          | ~ (v1_funct_1 @ sk_E)
% 2.26/2.43          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0))
% 2.26/2.43          | ~ (v2_funct_1 @ sk_E))),
% 2.26/2.43      inference('sup-', [status(thm)], ['33', '34'])).
% 2.26/2.43  thf('36', plain,
% 2.26/2.43      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf('37', plain,
% 2.26/2.43      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.26/2.43         ((v1_relat_1 @ X6)
% 2.26/2.43          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.26/2.43      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.26/2.43  thf('38', plain, ((v1_relat_1 @ sk_E)),
% 2.26/2.43      inference('sup-', [status(thm)], ['36', '37'])).
% 2.26/2.43  thf('39', plain, ((v1_funct_1 @ sk_E)),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf('40', plain, ((v2_funct_1 @ sk_E)),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf('41', plain,
% 2.26/2.43      (![X0 : $i]:
% 2.26/2.43         (~ (r1_tarski @ X0 @ sk_B)
% 2.26/2.43          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0)))),
% 2.26/2.43      inference('demod', [status(thm)], ['35', '38', '39', '40'])).
% 2.26/2.43  thf('42', plain,
% 2.26/2.43      (((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 2.26/2.43         = (k2_relat_1 @ sk_D))),
% 2.26/2.43      inference('sup-', [status(thm)], ['32', '41'])).
% 2.26/2.43  thf('43', plain,
% 2.26/2.43      ((((k10_relat_1 @ sk_E @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 2.26/2.43          = (k2_relat_1 @ sk_D))
% 2.26/2.43        | ~ (v1_relat_1 @ sk_D)
% 2.26/2.43        | ~ (v1_relat_1 @ sk_E))),
% 2.26/2.43      inference('sup+', [status(thm)], ['23', '42'])).
% 2.26/2.43  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 2.26/2.43      inference('sup-', [status(thm)], ['29', '30'])).
% 2.26/2.43  thf('45', plain, ((v1_relat_1 @ sk_E)),
% 2.26/2.43      inference('sup-', [status(thm)], ['36', '37'])).
% 2.26/2.43  thf('46', plain,
% 2.26/2.43      (((k10_relat_1 @ sk_E @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 2.26/2.43         = (k2_relat_1 @ sk_D))),
% 2.26/2.43      inference('demod', [status(thm)], ['43', '44', '45'])).
% 2.26/2.43  thf('47', plain,
% 2.26/2.43      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf('48', plain,
% 2.26/2.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf(dt_k1_partfun1, axiom,
% 2.26/2.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.26/2.43     ( ( ( v1_funct_1 @ E ) & 
% 2.26/2.43         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.26/2.43         ( v1_funct_1 @ F ) & 
% 2.26/2.43         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.26/2.43       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.26/2.43         ( m1_subset_1 @
% 2.26/2.43           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.26/2.43           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.26/2.43  thf('49', plain,
% 2.26/2.43      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 2.26/2.43         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.26/2.43          | ~ (v1_funct_1 @ X33)
% 2.26/2.43          | ~ (v1_funct_1 @ X36)
% 2.26/2.43          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 2.26/2.43          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 2.26/2.43             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 2.26/2.43      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.26/2.43  thf('50', plain,
% 2.26/2.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.26/2.43         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.26/2.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.26/2.43          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.26/2.43          | ~ (v1_funct_1 @ X1)
% 2.26/2.43          | ~ (v1_funct_1 @ sk_D))),
% 2.26/2.43      inference('sup-', [status(thm)], ['48', '49'])).
% 2.26/2.43  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf('52', plain,
% 2.26/2.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.26/2.43         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.26/2.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.26/2.43          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.26/2.43          | ~ (v1_funct_1 @ X1))),
% 2.26/2.43      inference('demod', [status(thm)], ['50', '51'])).
% 2.26/2.43  thf('53', plain,
% 2.26/2.43      ((~ (v1_funct_1 @ sk_E)
% 2.26/2.43        | (m1_subset_1 @ 
% 2.26/2.43           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 2.26/2.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 2.26/2.43      inference('sup-', [status(thm)], ['47', '52'])).
% 2.26/2.43  thf('54', plain, ((v1_funct_1 @ sk_E)),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf('55', plain,
% 2.26/2.43      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf('56', plain,
% 2.26/2.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf(redefinition_k1_partfun1, axiom,
% 2.26/2.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.26/2.43     ( ( ( v1_funct_1 @ E ) & 
% 2.26/2.43         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.26/2.43         ( v1_funct_1 @ F ) & 
% 2.26/2.43         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.26/2.43       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.26/2.43  thf('57', plain,
% 2.26/2.43      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 2.26/2.43         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 2.26/2.43          | ~ (v1_funct_1 @ X39)
% 2.26/2.43          | ~ (v1_funct_1 @ X42)
% 2.26/2.43          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 2.26/2.43          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 2.26/2.43              = (k5_relat_1 @ X39 @ X42)))),
% 2.26/2.43      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.26/2.43  thf('58', plain,
% 2.26/2.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.26/2.43         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.26/2.43            = (k5_relat_1 @ sk_D @ X0))
% 2.26/2.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.26/2.43          | ~ (v1_funct_1 @ X0)
% 2.26/2.43          | ~ (v1_funct_1 @ sk_D))),
% 2.26/2.43      inference('sup-', [status(thm)], ['56', '57'])).
% 2.26/2.43  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf('60', plain,
% 2.26/2.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.26/2.43         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.26/2.43            = (k5_relat_1 @ sk_D @ X0))
% 2.26/2.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.26/2.43          | ~ (v1_funct_1 @ X0))),
% 2.26/2.43      inference('demod', [status(thm)], ['58', '59'])).
% 2.26/2.43  thf('61', plain,
% 2.26/2.43      ((~ (v1_funct_1 @ sk_E)
% 2.26/2.43        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.26/2.43            = (k5_relat_1 @ sk_D @ sk_E)))),
% 2.26/2.43      inference('sup-', [status(thm)], ['55', '60'])).
% 2.26/2.43  thf('62', plain, ((v1_funct_1 @ sk_E)),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf('63', plain,
% 2.26/2.43      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.26/2.43         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.26/2.43      inference('demod', [status(thm)], ['61', '62'])).
% 2.26/2.43  thf('64', plain,
% 2.26/2.43      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 2.26/2.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.26/2.43      inference('demod', [status(thm)], ['53', '54', '63'])).
% 2.26/2.43  thf(redefinition_k2_relset_1, axiom,
% 2.26/2.43    (![A:$i,B:$i,C:$i]:
% 2.26/2.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.26/2.43       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.26/2.43  thf('65', plain,
% 2.26/2.43      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.26/2.43         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 2.26/2.43          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.26/2.43      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.26/2.43  thf('66', plain,
% 2.26/2.43      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 2.26/2.43         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 2.26/2.43      inference('sup-', [status(thm)], ['64', '65'])).
% 2.26/2.43  thf('67', plain,
% 2.26/2.43      (((k2_relset_1 @ sk_A @ sk_C @ 
% 2.26/2.43         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf('68', plain,
% 2.26/2.43      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.26/2.43         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.26/2.43      inference('demod', [status(thm)], ['61', '62'])).
% 2.26/2.43  thf('69', plain,
% 2.26/2.43      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.26/2.43      inference('demod', [status(thm)], ['67', '68'])).
% 2.26/2.43  thf('70', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.26/2.43      inference('sup+', [status(thm)], ['66', '69'])).
% 2.26/2.43  thf('71', plain, (((k10_relat_1 @ sk_E @ sk_C) = (k2_relat_1 @ sk_D))),
% 2.26/2.43      inference('demod', [status(thm)], ['46', '70'])).
% 2.26/2.43  thf('72', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 2.26/2.43      inference('sup+', [status(thm)], ['22', '71'])).
% 2.26/2.43  thf('73', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf('74', plain,
% 2.26/2.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.26/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.43  thf('75', plain,
% 2.26/2.43      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.26/2.43         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 2.26/2.43          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.26/2.43      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.26/2.43  thf('76', plain,
% 2.26/2.43      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.26/2.43      inference('sup-', [status(thm)], ['74', '75'])).
% 2.26/2.43  thf('77', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 2.26/2.43      inference('demod', [status(thm)], ['73', '76'])).
% 2.26/2.43  thf('78', plain, ($false),
% 2.26/2.43      inference('simplify_reflect-', [status(thm)], ['72', '77'])).
% 2.26/2.43  
% 2.26/2.43  % SZS output end Refutation
% 2.26/2.43  
% 2.26/2.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
