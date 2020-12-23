%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RANtixzvvj

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:02 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 458 expanded)
%              Number of leaves         :   38 ( 153 expanded)
%              Depth                    :   14
%              Number of atoms          : 1008 (5477 expanded)
%              Number of equality atoms :  117 ( 508 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) )
          = A ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_funct_2])).

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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( ( k7_relset_1 @ X16 @ X17 @ X15 @ X18 )
        = ( k9_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k2_relat_1 @ sk_C ) )
 != sk_A ),
    inference(demod,[status(thm)],['12','15','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k8_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k10_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('42',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('44',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('45',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['39','40','41','42','43','44'])).

thf('46',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(demod,[status(thm)],['31','34','45'])).

thf('47',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','46'])).

thf('48',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','47'])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('50',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('53',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,
    ( ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','62'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('65',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('66',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','63','66'])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('69',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('70',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
     != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('74',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0 ) )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('76',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( ( k7_relset_1 @ X16 @ X17 @ X15 @ X18 )
        = ( k9_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ X0 )
        = ( k9_relat_1 @ sk_C @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('79',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('80',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('82',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( sk_C
        = ( k7_relat_1 @ sk_C @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('84',plain,
    ( ( sk_C
      = ( k7_relat_1 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('86',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','77','86'])).

thf('88',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('89',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k8_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k10_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ X0 )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['39','40','41','42','43','44'])).

thf('92',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','90','91'])).

thf('93',plain,(
    sk_A != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['67','92'])).

thf('94',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('95',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['93','94'])).

thf('96',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','95'])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RANtixzvvj
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 153 iterations in 0.147s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.41/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.41/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.41/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.41/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.41/0.61  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.41/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.61  thf(d1_funct_2, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.41/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.41/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.41/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, axiom,
% 0.41/0.61    (![B:$i,A:$i]:
% 0.41/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.61       ( zip_tseitin_0 @ B @ A ) ))).
% 0.41/0.61  thf('0', plain,
% 0.41/0.61      (![X23 : $i, X24 : $i]:
% 0.41/0.61         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t51_funct_2, conjecture,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.61         ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 0.41/0.61           ( A ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_1, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.61        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.61            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.61          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.61            ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 0.41/0.61              ( A ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t51_funct_2])).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.41/0.61  thf(zf_stmt_3, axiom,
% 0.41/0.61    (![C:$i,B:$i,A:$i]:
% 0.41/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.41/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.41/0.61  thf(zf_stmt_5, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.41/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.41/0.61         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.41/0.61          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.41/0.61          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['0', '3'])).
% 0.41/0.61  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.61         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.41/0.61          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.41/0.61          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.41/0.61        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.61         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.41/0.61          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.41/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.61  thf('11', plain,
% 0.41/0.61      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.41/0.61      inference('demod', [status(thm)], ['7', '10'])).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ 
% 0.41/0.61         (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)) != (sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf(redefinition_k7_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.41/0.61          | ((k7_relset_1 @ X16 @ X17 @ X15 @ X18) = (k9_relat_1 @ X15 @ X18)))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.41/0.61  thf('15', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf(cc2_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.61         ((v4_relat_1 @ X9 @ X10)
% 0.41/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.61  thf('18', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.41/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.61  thf(t209_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.41/0.61       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i]:
% 0.41/0.61         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.41/0.61          | ~ (v4_relat_1 @ X7 @ X8)
% 0.41/0.61          | ~ (v1_relat_1 @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf(cc2_relat_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.41/0.61          | (v1_relat_1 @ X0)
% 0.41/0.61          | ~ (v1_relat_1 @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.41/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.61  thf(fc6_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.41/0.61  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.61  thf('26', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['20', '25'])).
% 0.41/0.61  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.61  thf(t148_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ B ) =>
% 0.41/0.61       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i]:
% 0.41/0.61         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.41/0.61          | ~ (v1_relat_1 @ X4))),
% 0.41/0.61      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.41/0.61  thf('29', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)) = (k9_relat_1 @ sk_C @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.61  thf('30', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('sup+', [status(thm)], ['26', '29'])).
% 0.41/0.61  thf('31', plain,
% 0.41/0.61      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ (k2_relat_1 @ sk_C)) != (sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['12', '15', '30'])).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf(redefinition_k8_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.41/0.61  thf('33', plain,
% 0.41/0.61      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.41/0.61          | ((k8_relset_1 @ X20 @ X21 @ X19 @ X22) = (k10_relat_1 @ X19 @ X22)))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.41/0.61  thf('34', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.61  thf('35', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['20', '25'])).
% 0.41/0.61  thf('36', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i]:
% 0.41/0.61         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.41/0.61          | ~ (v1_relat_1 @ X4))),
% 0.41/0.61      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.41/0.61  thf(t169_relat_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ A ) =>
% 0.41/0.61       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      (![X6 : $i]:
% 0.41/0.61         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.41/0.61          | ~ (v1_relat_1 @ X6))),
% 0.41/0.61      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.41/0.61  thf('38', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.41/0.61            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.41/0.61          | ~ (v1_relat_1 @ X1)
% 0.41/0.61          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['36', '37'])).
% 0.41/0.61  thf('39', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.41/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.61        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.41/0.61            (k9_relat_1 @ sk_C @ sk_A))
% 0.41/0.61            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['35', '38'])).
% 0.41/0.61  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.61  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.61  thf('42', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['20', '25'])).
% 0.41/0.61  thf('43', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('sup+', [status(thm)], ['26', '29'])).
% 0.41/0.61  thf('44', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['20', '25'])).
% 0.41/0.61  thf('45', plain,
% 0.41/0.61      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.41/0.61      inference('demod', [status(thm)], ['39', '40', '41', '42', '43', '44'])).
% 0.41/0.61  thf('46', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['31', '34', '45'])).
% 0.41/0.61  thf('47', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['11', '46'])).
% 0.41/0.61  thf('48', plain, (((sk_B) = (k1_xboole_0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['4', '47'])).
% 0.41/0.61  thf('49', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf('50', plain,
% 0.41/0.61      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['49'])).
% 0.41/0.61  thf('51', plain,
% 0.41/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['49'])).
% 0.41/0.61  thf('52', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf('53', plain,
% 0.41/0.61      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['51', '52'])).
% 0.41/0.61  thf('54', plain,
% 0.41/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.61         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.41/0.61          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.41/0.61          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.41/0.61  thf('55', plain,
% 0.41/0.61      (((~ (zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.41/0.61         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C))))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.61  thf('56', plain,
% 0.41/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['49'])).
% 0.41/0.61  thf('57', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf('58', plain,
% 0.41/0.61      (((m1_subset_1 @ sk_C @ 
% 0.41/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['56', '57'])).
% 0.41/0.61  thf('59', plain,
% 0.41/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.41/0.61         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.41/0.61          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.41/0.61          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.61  thf('60', plain,
% 0.41/0.61      ((((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.41/0.61         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['58', '59'])).
% 0.41/0.61  thf('61', plain,
% 0.41/0.61      (![X23 : $i, X24 : $i]:
% 0.41/0.61         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('62', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 0.41/0.61      inference('simplify', [status(thm)], ['61'])).
% 0.41/0.61  thf('63', plain,
% 0.41/0.61      (((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['60', '62'])).
% 0.41/0.61  thf('64', plain,
% 0.41/0.61      (((m1_subset_1 @ sk_C @ 
% 0.41/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['56', '57'])).
% 0.41/0.61  thf('65', plain,
% 0.41/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.61         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.41/0.61          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.61  thf('66', plain,
% 0.41/0.61      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C) = (k1_relat_1 @ sk_C)))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['64', '65'])).
% 0.41/0.61  thf('67', plain,
% 0.41/0.61      ((((k1_xboole_0) = (k1_relat_1 @ sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['55', '63', '66'])).
% 0.41/0.61  thf('68', plain,
% 0.41/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['49'])).
% 0.41/0.61  thf('69', plain,
% 0.41/0.61      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ 
% 0.41/0.61         (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)) != (sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf('70', plain,
% 0.41/0.61      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ 
% 0.41/0.61          (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)) != (sk_A)))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['68', '69'])).
% 0.41/0.61  thf('71', plain,
% 0.41/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['49'])).
% 0.41/0.61  thf('72', plain,
% 0.41/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['49'])).
% 0.41/0.61  thf('73', plain,
% 0.41/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['49'])).
% 0.41/0.61  thf('74', plain,
% 0.41/0.61      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ 
% 0.41/0.61          (k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0))
% 0.41/0.61          != (k1_xboole_0)))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.41/0.61  thf('75', plain,
% 0.41/0.61      (((m1_subset_1 @ sk_C @ 
% 0.41/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['56', '57'])).
% 0.41/0.61  thf('76', plain,
% 0.41/0.61      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.41/0.61          | ((k7_relset_1 @ X16 @ X17 @ X15 @ X18) = (k9_relat_1 @ X15 @ X18)))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.41/0.61  thf('77', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          ((k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ X0)
% 0.41/0.61            = (k9_relat_1 @ sk_C @ X0)))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['75', '76'])).
% 0.41/0.61  thf('78', plain,
% 0.41/0.61      (((m1_subset_1 @ sk_C @ 
% 0.41/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['56', '57'])).
% 0.41/0.61  thf('79', plain,
% 0.41/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.61         ((v4_relat_1 @ X9 @ X10)
% 0.41/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.61  thf('80', plain,
% 0.41/0.61      (((v4_relat_1 @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['78', '79'])).
% 0.41/0.61  thf('81', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i]:
% 0.41/0.61         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.41/0.61          | ~ (v4_relat_1 @ X7 @ X8)
% 0.41/0.61          | ~ (v1_relat_1 @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.41/0.61  thf('82', plain,
% 0.41/0.61      (((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ k1_xboole_0))))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['80', '81'])).
% 0.41/0.61  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.61  thf('84', plain,
% 0.41/0.61      ((((sk_C) = (k7_relat_1 @ sk_C @ k1_xboole_0)))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['82', '83'])).
% 0.41/0.61  thf('85', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)) = (k9_relat_1 @ sk_C @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.61  thf('86', plain,
% 0.41/0.61      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ k1_xboole_0)))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['84', '85'])).
% 0.41/0.61  thf('87', plain,
% 0.41/0.61      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ (k2_relat_1 @ sk_C))
% 0.41/0.61          != (k1_xboole_0)))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['74', '77', '86'])).
% 0.41/0.61  thf('88', plain,
% 0.41/0.61      (((m1_subset_1 @ sk_C @ 
% 0.41/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['56', '57'])).
% 0.41/0.61  thf('89', plain,
% 0.41/0.61      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.41/0.61          | ((k8_relset_1 @ X20 @ X21 @ X19 @ X22) = (k10_relat_1 @ X19 @ X22)))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.41/0.61  thf('90', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          ((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ X0)
% 0.41/0.61            = (k10_relat_1 @ sk_C @ X0)))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['88', '89'])).
% 0.41/0.61  thf('91', plain,
% 0.41/0.61      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.41/0.61      inference('demod', [status(thm)], ['39', '40', '41', '42', '43', '44'])).
% 0.41/0.61  thf('92', plain,
% 0.41/0.61      ((((k1_relat_1 @ sk_C) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['87', '90', '91'])).
% 0.41/0.61  thf('93', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['67', '92'])).
% 0.41/0.61  thf('94', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.41/0.61      inference('split', [status(esa)], ['49'])).
% 0.41/0.61  thf('95', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['93', '94'])).
% 0.41/0.61  thf('96', plain, (((sk_B) != (k1_xboole_0))),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['50', '95'])).
% 0.41/0.61  thf('97', plain, ($false),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['48', '96'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
