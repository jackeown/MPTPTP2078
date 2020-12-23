%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9fykU3rNFT

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:02 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 197 expanded)
%              Number of leaves         :   32 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  890 (2717 expanded)
%              Number of equality atoms :  108 ( 312 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
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

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('13',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( ( k8_relset_1 @ X11 @ X12 @ X10 @ X13 )
        = ( k10_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k10_relat_1 @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relset_1 @ X14 @ X15 @ X16 @ X14 )
        = ( k2_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('20',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
 != sk_A ),
    inference(demod,[status(thm)],['17','24'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('28',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','30'])).

thf('32',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','31'])).

thf('33',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('44',plain,
    ( ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X17: $i] :
      ( zip_tseitin_0 @ X17 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('49',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('50',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('53',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('54',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('55',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
     != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('58',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('59',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0 ) )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('61',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( ( k8_relset_1 @ X11 @ X12 @ X10 @ X13 )
        = ( k10_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ X0 )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0 ) )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('65',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relset_1 @ X14 @ X15 @ X16 @ X14 )
        = ( k2_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('66',plain,
    ( ( ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0 )
      = ( k2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('68',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('69',plain,
    ( ( ( k2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0 )
      = ( k2_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','70'])).

thf('72',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('74',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    sk_A != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['51','74'])).

thf('76',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('77',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['75','76'])).

thf('78',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['34','77'])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9fykU3rNFT
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.57  % Solved by: fo/fo7.sh
% 0.35/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.57  % done 134 iterations in 0.116s
% 0.35/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.57  % SZS output start Refutation
% 0.35/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.35/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.35/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.57  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.35/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.35/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.57  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.35/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.57  thf(d1_funct_2, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.35/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.35/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.35/0.57  thf(zf_stmt_0, axiom,
% 0.35/0.57    (![B:$i,A:$i]:
% 0.35/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.35/0.57  thf('0', plain,
% 0.35/0.57      (![X17 : $i, X18 : $i]:
% 0.35/0.57         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(t51_funct_2, conjecture,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.57         ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 0.35/0.57           ( A ) ) ) ))).
% 0.35/0.57  thf(zf_stmt_1, negated_conjecture,
% 0.35/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.57          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.57            ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 0.35/0.57              ( A ) ) ) ) )),
% 0.35/0.57    inference('cnf.neg', [status(esa)], [t51_funct_2])).
% 0.35/0.57  thf('1', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.35/0.57  thf(zf_stmt_3, axiom,
% 0.35/0.57    (![C:$i,B:$i,A:$i]:
% 0.35/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.35/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.35/0.57  thf(zf_stmt_5, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.35/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.35/0.57  thf('2', plain,
% 0.35/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.57         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.35/0.57          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.35/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.57  thf('3', plain,
% 0.35/0.57      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.57  thf('4', plain,
% 0.35/0.57      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['0', '3'])).
% 0.35/0.57  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf('6', plain,
% 0.35/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.57         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.35/0.57          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.35/0.57          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.57  thf('7', plain,
% 0.35/0.57      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.35/0.57        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.57  thf('8', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.57  thf('9', plain,
% 0.35/0.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.57         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 0.35/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.35/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.57  thf('10', plain,
% 0.35/0.57      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.35/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.35/0.57  thf('11', plain,
% 0.35/0.57      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.35/0.57      inference('demod', [status(thm)], ['7', '10'])).
% 0.35/0.57  thf(t169_relat_1, axiom,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( v1_relat_1 @ A ) =>
% 0.35/0.57       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.35/0.57  thf('12', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.35/0.57          | ~ (v1_relat_1 @ X0))),
% 0.35/0.57      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.35/0.57  thf('13', plain,
% 0.35/0.57      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ 
% 0.35/0.57         (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)) != (sk_A))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf('14', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf(redefinition_k8_relset_1, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.35/0.57  thf('15', plain,
% 0.35/0.57      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.35/0.57          | ((k8_relset_1 @ X11 @ X12 @ X10 @ X13) = (k10_relat_1 @ X10 @ X13)))),
% 0.35/0.57      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.35/0.57  thf('16', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.35/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.57  thf('17', plain,
% 0.35/0.57      (((k10_relat_1 @ sk_C @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.35/0.57         != (sk_A))),
% 0.35/0.57      inference('demod', [status(thm)], ['13', '16'])).
% 0.35/0.57  thf('18', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf(t38_relset_1, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.35/0.57         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.57  thf('19', plain,
% 0.35/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.57         (((k7_relset_1 @ X14 @ X15 @ X16 @ X14)
% 0.35/0.57            = (k2_relset_1 @ X14 @ X15 @ X16))
% 0.35/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.35/0.57      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.35/0.57  thf('20', plain,
% 0.35/0.57      (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.35/0.57         = (k2_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.35/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.35/0.57  thf('21', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.35/0.57  thf('22', plain,
% 0.35/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.57         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 0.35/0.57          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.35/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.35/0.57  thf('23', plain,
% 0.35/0.57      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.35/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.57  thf('24', plain,
% 0.35/0.57      (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.35/0.57      inference('demod', [status(thm)], ['20', '23'])).
% 0.35/0.57  thf('25', plain, (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (sk_A))),
% 0.35/0.57      inference('demod', [status(thm)], ['17', '24'])).
% 0.35/0.57  thf('26', plain, ((((k1_relat_1 @ sk_C) != (sk_A)) | ~ (v1_relat_1 @ sk_C))),
% 0.35/0.57      inference('sup-', [status(thm)], ['12', '25'])).
% 0.35/0.57  thf('27', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf(cc1_relset_1, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( v1_relat_1 @ C ) ))).
% 0.35/0.57  thf('28', plain,
% 0.35/0.57      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.57         ((v1_relat_1 @ X1)
% 0.35/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.35/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.57  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.57  thf('30', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.35/0.57      inference('demod', [status(thm)], ['26', '29'])).
% 0.35/0.57  thf('31', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.35/0.57      inference('simplify_reflect-', [status(thm)], ['11', '30'])).
% 0.35/0.57  thf('32', plain, (((sk_B) = (k1_xboole_0))),
% 0.35/0.57      inference('sup-', [status(thm)], ['4', '31'])).
% 0.35/0.57  thf('33', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf('34', plain,
% 0.35/0.57      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.35/0.57      inference('split', [status(esa)], ['33'])).
% 0.35/0.57  thf('35', plain,
% 0.35/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('split', [status(esa)], ['33'])).
% 0.35/0.57  thf('36', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf('37', plain,
% 0.35/0.57      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup+', [status(thm)], ['35', '36'])).
% 0.35/0.57  thf('38', plain,
% 0.35/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.57         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.35/0.57          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.35/0.57          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.57  thf('39', plain,
% 0.35/0.57      (((~ (zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.35/0.57         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C))))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.35/0.57  thf('40', plain,
% 0.35/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('split', [status(esa)], ['33'])).
% 0.35/0.57  thf('41', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf('42', plain,
% 0.35/0.57      (((m1_subset_1 @ sk_C @ 
% 0.35/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup+', [status(thm)], ['40', '41'])).
% 0.35/0.57  thf('43', plain,
% 0.35/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.57         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.35/0.57          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.35/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.57  thf('44', plain,
% 0.35/0.57      ((((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.35/0.57         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.57  thf('45', plain,
% 0.35/0.57      (![X17 : $i, X18 : $i]:
% 0.35/0.57         ((zip_tseitin_0 @ X17 @ X18) | ((X18) != (k1_xboole_0)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('46', plain, (![X17 : $i]: (zip_tseitin_0 @ X17 @ k1_xboole_0)),
% 0.35/0.57      inference('simplify', [status(thm)], ['45'])).
% 0.35/0.57  thf('47', plain,
% 0.35/0.57      (((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('demod', [status(thm)], ['44', '46'])).
% 0.35/0.57  thf('48', plain,
% 0.35/0.57      (((m1_subset_1 @ sk_C @ 
% 0.35/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup+', [status(thm)], ['40', '41'])).
% 0.35/0.57  thf('49', plain,
% 0.35/0.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.57         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 0.35/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.35/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.57  thf('50', plain,
% 0.35/0.57      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C) = (k1_relat_1 @ sk_C)))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.35/0.57  thf('51', plain,
% 0.35/0.57      ((((k1_xboole_0) = (k1_relat_1 @ sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('demod', [status(thm)], ['39', '47', '50'])).
% 0.35/0.57  thf('52', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.35/0.57          | ~ (v1_relat_1 @ X0))),
% 0.35/0.57      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.35/0.57  thf('53', plain,
% 0.35/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('split', [status(esa)], ['33'])).
% 0.35/0.57  thf('54', plain,
% 0.35/0.57      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ 
% 0.35/0.57         (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)) != (sk_A))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf('55', plain,
% 0.35/0.57      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ 
% 0.35/0.57          (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)) != (sk_A)))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.35/0.57  thf('56', plain,
% 0.35/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('split', [status(esa)], ['33'])).
% 0.35/0.57  thf('57', plain,
% 0.35/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('split', [status(esa)], ['33'])).
% 0.35/0.57  thf('58', plain,
% 0.35/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('split', [status(esa)], ['33'])).
% 0.35/0.57  thf('59', plain,
% 0.35/0.57      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ 
% 0.35/0.57          (k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0))
% 0.35/0.57          != (k1_xboole_0)))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.35/0.57  thf('60', plain,
% 0.35/0.57      (((m1_subset_1 @ sk_C @ 
% 0.35/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup+', [status(thm)], ['40', '41'])).
% 0.35/0.57  thf('61', plain,
% 0.35/0.57      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.35/0.57          | ((k8_relset_1 @ X11 @ X12 @ X10 @ X13) = (k10_relat_1 @ X10 @ X13)))),
% 0.35/0.57      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.35/0.57  thf('62', plain,
% 0.35/0.57      ((![X0 : $i]:
% 0.35/0.57          ((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ X0)
% 0.35/0.57            = (k10_relat_1 @ sk_C @ X0)))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.35/0.57  thf('63', plain,
% 0.35/0.57      ((((k10_relat_1 @ sk_C @ 
% 0.35/0.57          (k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0))
% 0.35/0.57          != (k1_xboole_0)))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('demod', [status(thm)], ['59', '62'])).
% 0.35/0.57  thf('64', plain,
% 0.35/0.57      (((m1_subset_1 @ sk_C @ 
% 0.35/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup+', [status(thm)], ['40', '41'])).
% 0.35/0.57  thf('65', plain,
% 0.35/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.57         (((k7_relset_1 @ X14 @ X15 @ X16 @ X14)
% 0.35/0.57            = (k2_relset_1 @ X14 @ X15 @ X16))
% 0.35/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.35/0.57      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.35/0.57  thf('66', plain,
% 0.35/0.57      ((((k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0)
% 0.35/0.57          = (k2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C)))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['64', '65'])).
% 0.35/0.57  thf('67', plain,
% 0.35/0.57      (((m1_subset_1 @ sk_C @ 
% 0.35/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup+', [status(thm)], ['40', '41'])).
% 0.35/0.57  thf('68', plain,
% 0.35/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.57         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 0.35/0.57          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.35/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.35/0.57  thf('69', plain,
% 0.35/0.57      ((((k2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C) = (k2_relat_1 @ sk_C)))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['67', '68'])).
% 0.35/0.57  thf('70', plain,
% 0.35/0.57      ((((k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0)
% 0.35/0.57          = (k2_relat_1 @ sk_C)))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('demod', [status(thm)], ['66', '69'])).
% 0.35/0.57  thf('71', plain,
% 0.35/0.57      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_xboole_0)))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('demod', [status(thm)], ['63', '70'])).
% 0.35/0.57  thf('72', plain,
% 0.35/0.57      (((((k1_relat_1 @ sk_C) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C)))
% 0.35/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['52', '71'])).
% 0.35/0.57  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.57  thf('74', plain,
% 0.35/0.57      ((((k1_relat_1 @ sk_C) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.35/0.57      inference('demod', [status(thm)], ['72', '73'])).
% 0.35/0.57  thf('75', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.35/0.57      inference('simplify_reflect-', [status(thm)], ['51', '74'])).
% 0.35/0.57  thf('76', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.35/0.57      inference('split', [status(esa)], ['33'])).
% 0.35/0.57  thf('77', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.35/0.57      inference('sat_resolution*', [status(thm)], ['75', '76'])).
% 0.35/0.57  thf('78', plain, (((sk_B) != (k1_xboole_0))),
% 0.35/0.57      inference('simpl_trail', [status(thm)], ['34', '77'])).
% 0.35/0.57  thf('79', plain, ($false),
% 0.35/0.57      inference('simplify_reflect-', [status(thm)], ['32', '78'])).
% 0.35/0.57  
% 0.35/0.57  % SZS output end Refutation
% 0.35/0.57  
% 0.35/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
