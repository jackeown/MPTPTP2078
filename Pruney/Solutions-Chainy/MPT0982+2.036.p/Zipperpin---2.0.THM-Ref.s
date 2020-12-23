%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L2CIaWgv2Z

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:00 EST 2020

% Result     : Theorem 2.32s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 239 expanded)
%              Number of leaves         :   47 (  92 expanded)
%              Depth                    :   14
%              Number of atoms          : 1066 (4488 expanded)
%              Number of equality atoms :   66 ( 280 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k8_relset_1 @ X23 @ X24 @ X25 @ X24 )
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k8_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k10_relat_1 @ X19 @ X22 ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k9_relat_1 @ X6 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,
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

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X8 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ( ( k10_relat_1 @ X9 @ ( k9_relat_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('42',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['37','42','43','44'])).

thf('46',plain,
    ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,
    ( ( ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
      = ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['23','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('49',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['40','41'])).

thf('50',plain,
    ( ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( ( k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43 )
        = ( k5_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','67'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('69',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('70',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('73',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['50','74'])).

thf('76',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['22','75'])).

thf('77',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('80',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L2CIaWgv2Z
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:22:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.32/2.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.32/2.55  % Solved by: fo/fo7.sh
% 2.32/2.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.32/2.55  % done 647 iterations in 2.067s
% 2.32/2.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.32/2.55  % SZS output start Refutation
% 2.32/2.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.32/2.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 2.32/2.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.32/2.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.32/2.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.32/2.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.32/2.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.32/2.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.32/2.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.32/2.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.32/2.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.32/2.55  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 2.32/2.55  thf(sk_E_type, type, sk_E: $i).
% 2.32/2.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.32/2.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.32/2.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.32/2.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.32/2.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.32/2.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.32/2.55  thf(sk_C_type, type, sk_C: $i).
% 2.32/2.55  thf(sk_D_type, type, sk_D: $i).
% 2.32/2.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.32/2.55  thf(sk_B_type, type, sk_B: $i).
% 2.32/2.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.32/2.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.32/2.55  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.32/2.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.32/2.55  thf(sk_A_type, type, sk_A: $i).
% 2.32/2.55  thf(t28_funct_2, conjecture,
% 2.32/2.55    (![A:$i,B:$i,C:$i,D:$i]:
% 2.32/2.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.32/2.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.55       ( ![E:$i]:
% 2.32/2.55         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.32/2.55             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.32/2.55           ( ( ( ( k2_relset_1 @
% 2.32/2.55                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.32/2.55                 ( C ) ) & 
% 2.32/2.55               ( v2_funct_1 @ E ) ) =>
% 2.32/2.55             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.32/2.55               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 2.32/2.55  thf(zf_stmt_0, negated_conjecture,
% 2.32/2.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.32/2.55        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.32/2.55            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.55          ( ![E:$i]:
% 2.32/2.55            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.32/2.55                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.32/2.55              ( ( ( ( k2_relset_1 @
% 2.32/2.55                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.32/2.55                    ( C ) ) & 
% 2.32/2.55                  ( v2_funct_1 @ E ) ) =>
% 2.32/2.55                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.32/2.55                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 2.32/2.55    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 2.32/2.55  thf('0', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf(t38_relset_1, axiom,
% 2.32/2.55    (![A:$i,B:$i,C:$i]:
% 2.32/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.32/2.55       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 2.32/2.55         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.32/2.55  thf('1', plain,
% 2.32/2.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.32/2.55         (((k8_relset_1 @ X23 @ X24 @ X25 @ X24)
% 2.32/2.55            = (k1_relset_1 @ X23 @ X24 @ X25))
% 2.32/2.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 2.32/2.55      inference('cnf', [status(esa)], [t38_relset_1])).
% 2.32/2.55  thf('2', plain,
% 2.32/2.55      (((k8_relset_1 @ sk_B @ sk_C @ sk_E @ sk_C)
% 2.32/2.55         = (k1_relset_1 @ sk_B @ sk_C @ sk_E))),
% 2.32/2.55      inference('sup-', [status(thm)], ['0', '1'])).
% 2.32/2.55  thf('3', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf(redefinition_k8_relset_1, axiom,
% 2.32/2.55    (![A:$i,B:$i,C:$i,D:$i]:
% 2.32/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.32/2.55       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 2.32/2.55  thf('4', plain,
% 2.32/2.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 2.32/2.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 2.32/2.55          | ((k8_relset_1 @ X20 @ X21 @ X19 @ X22) = (k10_relat_1 @ X19 @ X22)))),
% 2.32/2.55      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.32/2.55  thf('5', plain,
% 2.32/2.55      (![X0 : $i]:
% 2.32/2.55         ((k8_relset_1 @ sk_B @ sk_C @ sk_E @ X0) = (k10_relat_1 @ sk_E @ X0))),
% 2.32/2.55      inference('sup-', [status(thm)], ['3', '4'])).
% 2.32/2.55  thf('6', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf(redefinition_k1_relset_1, axiom,
% 2.32/2.55    (![A:$i,B:$i,C:$i]:
% 2.32/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.32/2.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.32/2.55  thf('7', plain,
% 2.32/2.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.32/2.55         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 2.32/2.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.32/2.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.32/2.55  thf('8', plain, (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 2.32/2.55      inference('sup-', [status(thm)], ['6', '7'])).
% 2.32/2.55  thf('9', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf(d1_funct_2, axiom,
% 2.32/2.55    (![A:$i,B:$i,C:$i]:
% 2.32/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.32/2.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.32/2.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.32/2.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.32/2.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.32/2.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.32/2.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.32/2.55  thf(zf_stmt_1, axiom,
% 2.32/2.55    (![C:$i,B:$i,A:$i]:
% 2.32/2.55     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.32/2.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.32/2.55  thf('10', plain,
% 2.32/2.55      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.32/2.55         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 2.32/2.55          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 2.32/2.55          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.32/2.55  thf('11', plain,
% 2.32/2.55      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 2.32/2.55        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 2.32/2.55      inference('sup-', [status(thm)], ['9', '10'])).
% 2.32/2.55  thf(zf_stmt_2, axiom,
% 2.32/2.55    (![B:$i,A:$i]:
% 2.32/2.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.32/2.55       ( zip_tseitin_0 @ B @ A ) ))).
% 2.32/2.55  thf('12', plain,
% 2.32/2.55      (![X26 : $i, X27 : $i]:
% 2.32/2.55         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.32/2.55  thf('13', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.32/2.55  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.32/2.55  thf(zf_stmt_5, axiom,
% 2.32/2.55    (![A:$i,B:$i,C:$i]:
% 2.32/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.32/2.55       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.32/2.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.32/2.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.32/2.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.32/2.55  thf('14', plain,
% 2.32/2.55      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.32/2.55         (~ (zip_tseitin_0 @ X31 @ X32)
% 2.32/2.55          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 2.32/2.55          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.32/2.55  thf('15', plain,
% 2.32/2.55      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 2.32/2.55      inference('sup-', [status(thm)], ['13', '14'])).
% 2.32/2.55  thf('16', plain,
% 2.32/2.55      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 2.32/2.55      inference('sup-', [status(thm)], ['12', '15'])).
% 2.32/2.55  thf('17', plain, (((sk_C) != (k1_xboole_0))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('18', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 2.32/2.55      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 2.32/2.55  thf('19', plain,
% 2.32/2.55      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 2.32/2.55      inference('sup-', [status(thm)], ['6', '7'])).
% 2.32/2.55  thf('20', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.32/2.55      inference('demod', [status(thm)], ['11', '18', '19'])).
% 2.32/2.55  thf('21', plain, (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_B))),
% 2.32/2.55      inference('demod', [status(thm)], ['8', '20'])).
% 2.32/2.55  thf('22', plain, (((k10_relat_1 @ sk_E @ sk_C) = (sk_B))),
% 2.32/2.55      inference('demod', [status(thm)], ['2', '5', '21'])).
% 2.32/2.55  thf(t160_relat_1, axiom,
% 2.32/2.55    (![A:$i]:
% 2.32/2.55     ( ( v1_relat_1 @ A ) =>
% 2.32/2.55       ( ![B:$i]:
% 2.32/2.55         ( ( v1_relat_1 @ B ) =>
% 2.32/2.55           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.32/2.55             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.32/2.55  thf('23', plain,
% 2.32/2.55      (![X6 : $i, X7 : $i]:
% 2.32/2.55         (~ (v1_relat_1 @ X6)
% 2.32/2.55          | ((k2_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 2.32/2.55              = (k9_relat_1 @ X6 @ (k2_relat_1 @ X7)))
% 2.32/2.55          | ~ (v1_relat_1 @ X7))),
% 2.32/2.55      inference('cnf', [status(esa)], [t160_relat_1])).
% 2.32/2.55  thf('24', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf(cc2_relset_1, axiom,
% 2.32/2.55    (![A:$i,B:$i,C:$i]:
% 2.32/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.32/2.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.32/2.55  thf('25', plain,
% 2.32/2.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.32/2.55         ((v5_relat_1 @ X10 @ X12)
% 2.32/2.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 2.32/2.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.32/2.55  thf('26', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 2.32/2.55      inference('sup-', [status(thm)], ['24', '25'])).
% 2.32/2.55  thf(d19_relat_1, axiom,
% 2.32/2.55    (![A:$i,B:$i]:
% 2.32/2.55     ( ( v1_relat_1 @ B ) =>
% 2.32/2.55       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.32/2.55  thf('27', plain,
% 2.32/2.55      (![X2 : $i, X3 : $i]:
% 2.32/2.55         (~ (v5_relat_1 @ X2 @ X3)
% 2.32/2.55          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 2.32/2.55          | ~ (v1_relat_1 @ X2))),
% 2.32/2.55      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.32/2.55  thf('28', plain,
% 2.32/2.55      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 2.32/2.55      inference('sup-', [status(thm)], ['26', '27'])).
% 2.32/2.55  thf('29', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf(cc2_relat_1, axiom,
% 2.32/2.55    (![A:$i]:
% 2.32/2.55     ( ( v1_relat_1 @ A ) =>
% 2.32/2.55       ( ![B:$i]:
% 2.32/2.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.32/2.55  thf('30', plain,
% 2.32/2.55      (![X0 : $i, X1 : $i]:
% 2.32/2.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.32/2.55          | (v1_relat_1 @ X0)
% 2.32/2.55          | ~ (v1_relat_1 @ X1))),
% 2.32/2.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.32/2.55  thf('31', plain,
% 2.32/2.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 2.32/2.55      inference('sup-', [status(thm)], ['29', '30'])).
% 2.32/2.55  thf(fc6_relat_1, axiom,
% 2.32/2.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.32/2.55  thf('32', plain,
% 2.32/2.55      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 2.32/2.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.32/2.55  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 2.32/2.55      inference('demod', [status(thm)], ['31', '32'])).
% 2.32/2.55  thf('34', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 2.32/2.55      inference('demod', [status(thm)], ['28', '33'])).
% 2.32/2.55  thf('35', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.32/2.55      inference('demod', [status(thm)], ['11', '18', '19'])).
% 2.32/2.55  thf(t164_funct_1, axiom,
% 2.32/2.55    (![A:$i,B:$i]:
% 2.32/2.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.32/2.55       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 2.32/2.55         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 2.32/2.55  thf('36', plain,
% 2.32/2.55      (![X8 : $i, X9 : $i]:
% 2.32/2.55         (~ (r1_tarski @ X8 @ (k1_relat_1 @ X9))
% 2.32/2.55          | ~ (v2_funct_1 @ X9)
% 2.32/2.55          | ((k10_relat_1 @ X9 @ (k9_relat_1 @ X9 @ X8)) = (X8))
% 2.32/2.55          | ~ (v1_funct_1 @ X9)
% 2.32/2.55          | ~ (v1_relat_1 @ X9))),
% 2.32/2.55      inference('cnf', [status(esa)], [t164_funct_1])).
% 2.32/2.55  thf('37', plain,
% 2.32/2.55      (![X0 : $i]:
% 2.32/2.55         (~ (r1_tarski @ X0 @ sk_B)
% 2.32/2.55          | ~ (v1_relat_1 @ sk_E)
% 2.32/2.55          | ~ (v1_funct_1 @ sk_E)
% 2.32/2.55          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0))
% 2.32/2.55          | ~ (v2_funct_1 @ sk_E))),
% 2.32/2.55      inference('sup-', [status(thm)], ['35', '36'])).
% 2.32/2.55  thf('38', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('39', plain,
% 2.32/2.55      (![X0 : $i, X1 : $i]:
% 2.32/2.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.32/2.55          | (v1_relat_1 @ X0)
% 2.32/2.55          | ~ (v1_relat_1 @ X1))),
% 2.32/2.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.32/2.55  thf('40', plain,
% 2.32/2.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 2.32/2.55      inference('sup-', [status(thm)], ['38', '39'])).
% 2.32/2.55  thf('41', plain,
% 2.32/2.55      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 2.32/2.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.32/2.55  thf('42', plain, ((v1_relat_1 @ sk_E)),
% 2.32/2.55      inference('demod', [status(thm)], ['40', '41'])).
% 2.32/2.55  thf('43', plain, ((v1_funct_1 @ sk_E)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('44', plain, ((v2_funct_1 @ sk_E)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('45', plain,
% 2.32/2.55      (![X0 : $i]:
% 2.32/2.55         (~ (r1_tarski @ X0 @ sk_B)
% 2.32/2.55          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0)))),
% 2.32/2.55      inference('demod', [status(thm)], ['37', '42', '43', '44'])).
% 2.32/2.55  thf('46', plain,
% 2.32/2.55      (((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 2.32/2.55         = (k2_relat_1 @ sk_D))),
% 2.32/2.55      inference('sup-', [status(thm)], ['34', '45'])).
% 2.32/2.55  thf('47', plain,
% 2.32/2.55      ((((k10_relat_1 @ sk_E @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 2.32/2.55          = (k2_relat_1 @ sk_D))
% 2.32/2.55        | ~ (v1_relat_1 @ sk_D)
% 2.32/2.55        | ~ (v1_relat_1 @ sk_E))),
% 2.32/2.55      inference('sup+', [status(thm)], ['23', '46'])).
% 2.32/2.55  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 2.32/2.55      inference('demod', [status(thm)], ['31', '32'])).
% 2.32/2.55  thf('49', plain, ((v1_relat_1 @ sk_E)),
% 2.32/2.55      inference('demod', [status(thm)], ['40', '41'])).
% 2.32/2.55  thf('50', plain,
% 2.32/2.55      (((k10_relat_1 @ sk_E @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 2.32/2.55         = (k2_relat_1 @ sk_D))),
% 2.32/2.55      inference('demod', [status(thm)], ['47', '48', '49'])).
% 2.32/2.55  thf('51', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('52', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf(dt_k1_partfun1, axiom,
% 2.32/2.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.32/2.55     ( ( ( v1_funct_1 @ E ) & 
% 2.32/2.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.32/2.55         ( v1_funct_1 @ F ) & 
% 2.32/2.55         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.32/2.55       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.32/2.55         ( m1_subset_1 @
% 2.32/2.55           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.32/2.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.32/2.55  thf('53', plain,
% 2.32/2.55      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 2.32/2.55         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 2.32/2.55          | ~ (v1_funct_1 @ X34)
% 2.32/2.55          | ~ (v1_funct_1 @ X37)
% 2.32/2.55          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.32/2.55          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 2.32/2.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 2.32/2.55      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.32/2.55  thf('54', plain,
% 2.32/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.55         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.32/2.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.32/2.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.32/2.55          | ~ (v1_funct_1 @ X1)
% 2.32/2.55          | ~ (v1_funct_1 @ sk_D))),
% 2.32/2.55      inference('sup-', [status(thm)], ['52', '53'])).
% 2.32/2.55  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('56', plain,
% 2.32/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.55         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.32/2.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.32/2.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.32/2.55          | ~ (v1_funct_1 @ X1))),
% 2.32/2.55      inference('demod', [status(thm)], ['54', '55'])).
% 2.32/2.55  thf('57', plain,
% 2.32/2.55      ((~ (v1_funct_1 @ sk_E)
% 2.32/2.55        | (m1_subset_1 @ 
% 2.32/2.55           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 2.32/2.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 2.32/2.55      inference('sup-', [status(thm)], ['51', '56'])).
% 2.32/2.55  thf('58', plain, ((v1_funct_1 @ sk_E)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('59', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('60', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf(redefinition_k1_partfun1, axiom,
% 2.32/2.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.32/2.55     ( ( ( v1_funct_1 @ E ) & 
% 2.32/2.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.32/2.55         ( v1_funct_1 @ F ) & 
% 2.32/2.55         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.32/2.55       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.32/2.55  thf('61', plain,
% 2.32/2.55      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 2.32/2.55         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 2.32/2.55          | ~ (v1_funct_1 @ X40)
% 2.32/2.55          | ~ (v1_funct_1 @ X43)
% 2.32/2.55          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.32/2.55          | ((k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43)
% 2.32/2.55              = (k5_relat_1 @ X40 @ X43)))),
% 2.32/2.55      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.32/2.55  thf('62', plain,
% 2.32/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.55         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.32/2.55            = (k5_relat_1 @ sk_D @ X0))
% 2.32/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.32/2.55          | ~ (v1_funct_1 @ X0)
% 2.32/2.55          | ~ (v1_funct_1 @ sk_D))),
% 2.32/2.55      inference('sup-', [status(thm)], ['60', '61'])).
% 2.32/2.55  thf('63', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('64', plain,
% 2.32/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.55         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.32/2.55            = (k5_relat_1 @ sk_D @ X0))
% 2.32/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.32/2.55          | ~ (v1_funct_1 @ X0))),
% 2.32/2.55      inference('demod', [status(thm)], ['62', '63'])).
% 2.32/2.55  thf('65', plain,
% 2.32/2.55      ((~ (v1_funct_1 @ sk_E)
% 2.32/2.55        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.32/2.55            = (k5_relat_1 @ sk_D @ sk_E)))),
% 2.32/2.55      inference('sup-', [status(thm)], ['59', '64'])).
% 2.32/2.55  thf('66', plain, ((v1_funct_1 @ sk_E)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('67', plain,
% 2.32/2.55      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.32/2.55         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.32/2.55      inference('demod', [status(thm)], ['65', '66'])).
% 2.32/2.55  thf('68', plain,
% 2.32/2.55      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 2.32/2.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.32/2.55      inference('demod', [status(thm)], ['57', '58', '67'])).
% 2.32/2.55  thf(redefinition_k2_relset_1, axiom,
% 2.32/2.55    (![A:$i,B:$i,C:$i]:
% 2.32/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.32/2.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.32/2.55  thf('69', plain,
% 2.32/2.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.32/2.55         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 2.32/2.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 2.32/2.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.32/2.55  thf('70', plain,
% 2.32/2.55      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 2.32/2.55         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 2.32/2.55      inference('sup-', [status(thm)], ['68', '69'])).
% 2.32/2.55  thf('71', plain,
% 2.32/2.55      (((k2_relset_1 @ sk_A @ sk_C @ 
% 2.32/2.55         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('72', plain,
% 2.32/2.55      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.32/2.55         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.32/2.55      inference('demod', [status(thm)], ['65', '66'])).
% 2.32/2.55  thf('73', plain,
% 2.32/2.55      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.32/2.55      inference('demod', [status(thm)], ['71', '72'])).
% 2.32/2.55  thf('74', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.32/2.55      inference('sup+', [status(thm)], ['70', '73'])).
% 2.32/2.55  thf('75', plain, (((k10_relat_1 @ sk_E @ sk_C) = (k2_relat_1 @ sk_D))),
% 2.32/2.55      inference('demod', [status(thm)], ['50', '74'])).
% 2.32/2.55  thf('76', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 2.32/2.55      inference('sup+', [status(thm)], ['22', '75'])).
% 2.32/2.55  thf('77', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('78', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('79', plain,
% 2.32/2.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.32/2.55         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 2.32/2.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 2.32/2.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.32/2.55  thf('80', plain,
% 2.32/2.55      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.32/2.55      inference('sup-', [status(thm)], ['78', '79'])).
% 2.32/2.55  thf('81', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 2.32/2.55      inference('demod', [status(thm)], ['77', '80'])).
% 2.32/2.55  thf('82', plain, ($false),
% 2.32/2.55      inference('simplify_reflect-', [status(thm)], ['76', '81'])).
% 2.32/2.55  
% 2.32/2.55  % SZS output end Refutation
% 2.32/2.55  
% 2.32/2.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
