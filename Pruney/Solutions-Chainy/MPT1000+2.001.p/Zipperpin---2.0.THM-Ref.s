%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oOMPMLtu5H

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:57 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 218 expanded)
%              Number of leaves         :   38 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  780 (2465 expanded)
%              Number of equality atoms :   88 ( 276 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( k8_relset_1 @ A @ B @ C @ B )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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

thf('2',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('3',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k8_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k10_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['20','23'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('28',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['26','27'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('29',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k10_relat_1 @ X4 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('32',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('36',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(demod,[status(thm)],['12','15','36'])).

thf('38',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','37'])).

thf('39',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('51',plain,
    ( ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X22: $i] :
      ( zip_tseitin_0 @ X22 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','53'])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('56',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','54','57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('60',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('61',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B )
     != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('63',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('65',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k8_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k10_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ X0 )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('68',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','66','67'])).

thf('69',plain,(
    sk_A != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['58','68'])).

thf('70',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('71',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['41','71'])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oOMPMLtu5H
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 115 iterations in 0.148s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.42/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.60  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.42/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.42/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.42/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.60  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.42/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.42/0.60  thf(d1_funct_2, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, axiom,
% 0.42/0.60    (![B:$i,A:$i]:
% 0.42/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      (![X22 : $i, X23 : $i]:
% 0.42/0.60         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(t48_funct_2, conjecture,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.60         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_1, negated_conjecture,
% 0.42/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.60        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.60            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.60          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.60            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t48_funct_2])).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.60  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.42/0.60  thf(zf_stmt_3, axiom,
% 0.42/0.60    (![C:$i,B:$i,A:$i]:
% 0.42/0.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.42/0.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.42/0.60  thf(zf_stmt_5, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.42/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.60         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.42/0.60          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.42/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['0', '3'])).
% 0.42/0.60  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.60         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.42/0.60          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.42/0.60          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.42/0.60        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.60         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.42/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.42/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.42/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.42/0.60      inference('demod', [status(thm)], ['7', '10'])).
% 0.42/0.60  thf('12', plain, (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.60  thf(redefinition_k8_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.42/0.60          | ((k8_relset_1 @ X19 @ X20 @ X18 @ X21) = (k10_relat_1 @ X18 @ X21)))),
% 0.42/0.60      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.60  thf(cc2_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.60         ((v5_relat_1 @ X12 @ X14)
% 0.42/0.60          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.42/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.60  thf('18', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.42/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.60  thf(d19_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ B ) =>
% 0.42/0.60       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (v5_relat_1 @ X0 @ X1)
% 0.42/0.60          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.42/0.60  thf('20', plain,
% 0.42/0.60      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.60  thf(cc1_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( v1_relat_1 @ C ) ))).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.60         ((v1_relat_1 @ X9)
% 0.42/0.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.42/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.60  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.42/0.60  thf('24', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.42/0.60      inference('demod', [status(thm)], ['20', '23'])).
% 0.42/0.60  thf(t79_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ B ) =>
% 0.42/0.60       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.42/0.60         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.42/0.60  thf('25', plain,
% 0.42/0.60      (![X7 : $i, X8 : $i]:
% 0.42/0.60         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.42/0.60          | ((k5_relat_1 @ X7 @ (k6_relat_1 @ X8)) = (X7))
% 0.42/0.60          | ~ (v1_relat_1 @ X7))),
% 0.42/0.60      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.42/0.60  thf('26', plain,
% 0.42/0.60      ((~ (v1_relat_1 @ sk_C)
% 0.42/0.60        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.42/0.60  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.42/0.60  thf('28', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 0.42/0.60      inference('demod', [status(thm)], ['26', '27'])).
% 0.42/0.60  thf(t71_relat_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.42/0.60       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.42/0.60  thf('29', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.42/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.42/0.60  thf(t182_relat_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ A ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( v1_relat_1 @ B ) =>
% 0.42/0.60           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.42/0.60             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      (![X3 : $i, X4 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X3)
% 0.42/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.42/0.60              = (k10_relat_1 @ X4 @ (k1_relat_1 @ X3)))
% 0.42/0.60          | ~ (v1_relat_1 @ X4))),
% 0.42/0.60      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.42/0.60  thf('31', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.42/0.60            = (k10_relat_1 @ X1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X1)
% 0.42/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.42/0.60      inference('sup+', [status(thm)], ['29', '30'])).
% 0.42/0.60  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.42/0.60  thf('32', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.42/0.60            = (k10_relat_1 @ X1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X1))),
% 0.42/0.60      inference('demod', [status(thm)], ['31', '32'])).
% 0.42/0.60  thf('34', plain,
% 0.42/0.60      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))
% 0.42/0.60        | ~ (v1_relat_1 @ sk_C))),
% 0.42/0.60      inference('sup+', [status(thm)], ['28', '33'])).
% 0.42/0.60  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.42/0.60  thf('36', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.42/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.42/0.60  thf('37', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['12', '15', '36'])).
% 0.42/0.60  thf('38', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.42/0.60      inference('simplify_reflect-', [status(thm)], ['11', '37'])).
% 0.42/0.60  thf('39', plain, (((sk_B) = (k1_xboole_0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['4', '38'])).
% 0.42/0.60  thf('40', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.60  thf('41', plain,
% 0.42/0.60      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.42/0.60      inference('split', [status(esa)], ['40'])).
% 0.42/0.60  thf('42', plain,
% 0.42/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('split', [status(esa)], ['40'])).
% 0.42/0.60  thf('43', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.60  thf('44', plain,
% 0.42/0.60      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.60  thf('45', plain,
% 0.42/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.60         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.42/0.60          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.42/0.60          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.60  thf('46', plain,
% 0.42/0.60      (((~ (zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.42/0.60         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C))))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.42/0.60  thf('47', plain,
% 0.42/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('split', [status(esa)], ['40'])).
% 0.42/0.60  thf('48', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.60  thf('49', plain,
% 0.42/0.60      (((m1_subset_1 @ sk_C @ 
% 0.42/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup+', [status(thm)], ['47', '48'])).
% 0.42/0.60  thf('50', plain,
% 0.42/0.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.60         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.42/0.60          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.42/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.60  thf('51', plain,
% 0.42/0.60      ((((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.42/0.60         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['49', '50'])).
% 0.42/0.60  thf('52', plain,
% 0.42/0.60      (![X22 : $i, X23 : $i]:
% 0.42/0.60         ((zip_tseitin_0 @ X22 @ X23) | ((X23) != (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('53', plain, (![X22 : $i]: (zip_tseitin_0 @ X22 @ k1_xboole_0)),
% 0.42/0.60      inference('simplify', [status(thm)], ['52'])).
% 0.42/0.60  thf('54', plain,
% 0.42/0.60      (((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('demod', [status(thm)], ['51', '53'])).
% 0.42/0.60  thf('55', plain,
% 0.42/0.60      (((m1_subset_1 @ sk_C @ 
% 0.42/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup+', [status(thm)], ['47', '48'])).
% 0.42/0.60  thf('56', plain,
% 0.42/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.60         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.42/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.42/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.60  thf('57', plain,
% 0.42/0.60      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C) = (k1_relat_1 @ sk_C)))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['55', '56'])).
% 0.42/0.60  thf('58', plain,
% 0.42/0.60      ((((k1_xboole_0) = (k1_relat_1 @ sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('demod', [status(thm)], ['46', '54', '57'])).
% 0.42/0.60  thf('59', plain,
% 0.42/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('split', [status(esa)], ['40'])).
% 0.42/0.60  thf('60', plain, (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.60  thf('61', plain,
% 0.42/0.60      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B) != (sk_A)))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['59', '60'])).
% 0.42/0.60  thf('62', plain,
% 0.42/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('split', [status(esa)], ['40'])).
% 0.42/0.60  thf('63', plain,
% 0.42/0.60      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B) != (k1_xboole_0)))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('demod', [status(thm)], ['61', '62'])).
% 0.42/0.60  thf('64', plain,
% 0.42/0.60      (((m1_subset_1 @ sk_C @ 
% 0.42/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup+', [status(thm)], ['47', '48'])).
% 0.42/0.60  thf('65', plain,
% 0.42/0.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.42/0.60          | ((k8_relset_1 @ X19 @ X20 @ X18 @ X21) = (k10_relat_1 @ X18 @ X21)))),
% 0.42/0.60      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.42/0.60  thf('66', plain,
% 0.42/0.60      ((![X0 : $i]:
% 0.42/0.60          ((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ X0)
% 0.42/0.60            = (k10_relat_1 @ sk_C @ X0)))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['64', '65'])).
% 0.42/0.60  thf('67', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.42/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.42/0.60  thf('68', plain,
% 0.42/0.60      ((((k1_relat_1 @ sk_C) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('demod', [status(thm)], ['63', '66', '67'])).
% 0.42/0.60  thf('69', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.42/0.60      inference('simplify_reflect-', [status(thm)], ['58', '68'])).
% 0.42/0.60  thf('70', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.42/0.60      inference('split', [status(esa)], ['40'])).
% 0.42/0.60  thf('71', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.42/0.60      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.42/0.60  thf('72', plain, (((sk_B) != (k1_xboole_0))),
% 0.42/0.60      inference('simpl_trail', [status(thm)], ['41', '71'])).
% 0.42/0.60  thf('73', plain, ($false),
% 0.42/0.60      inference('simplify_reflect-', [status(thm)], ['39', '72'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.46/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
