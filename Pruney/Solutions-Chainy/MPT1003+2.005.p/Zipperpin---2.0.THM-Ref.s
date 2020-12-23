%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GvxQqhNbDW

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:02 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 211 expanded)
%              Number of leaves         :   34 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  871 (2718 expanded)
%              Number of equality atoms :  108 ( 314 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('3',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X7: $i] :
      ( ( ( k10_relat_1 @ X7 @ ( k2_relat_1 @ X7 ) )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('12',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k8_relset_1 @ X15 @ X16 @ X14 @ X17 )
        = ( k10_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ( k10_relat_1 @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relset_1 @ X18 @ X19 @ X20 @ X18 )
        = ( k2_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('19',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('22',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
 != sk_A ),
    inference(demod,[status(thm)],['16','23'])).

thf('25',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','31'])).

thf('33',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['3','32'])).

thf('34',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('36',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('39',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('45',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('46',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('49',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_C )
        = ( k1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','51'])).

thf('53',plain,(
    ! [X7: $i] :
      ( ( ( k10_relat_1 @ X7 @ ( k2_relat_1 @ X7 ) )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('54',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('55',plain,(
    ( k10_relat_1 @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['12','15'])).

thf('56',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_A ) )
     != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('58',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('59',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0 ) )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('61',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('62',plain,
    ( ( ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_A )
      = ( k2_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('64',plain,
    ( ( ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0 )
      = ( k2_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('68',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['52','68'])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','46'])).

thf('71',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('72',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X21: $i] :
      ( zip_tseitin_0 @ X21 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_C @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['69','77'])).

thf('79',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('80',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['36','80'])).

thf('82',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GvxQqhNbDW
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:19:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.44/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.61  % Solved by: fo/fo7.sh
% 0.44/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.61  % done 194 iterations in 0.152s
% 0.44/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.61  % SZS output start Refutation
% 0.44/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.44/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.44/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.61  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.44/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.61  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.44/0.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.44/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.44/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.61  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.44/0.61  thf(d1_funct_2, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.44/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.44/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_0, axiom,
% 0.44/0.61    (![B:$i,A:$i]:
% 0.44/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.61       ( zip_tseitin_0 @ B @ A ) ))).
% 0.44/0.61  thf('0', plain,
% 0.44/0.61      (![X21 : $i, X22 : $i]:
% 0.44/0.61         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(t51_funct_2, conjecture,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.61         ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 0.44/0.61           ( A ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_1, negated_conjecture,
% 0.44/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.61        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.61            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.61          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.61            ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 0.44/0.61              ( A ) ) ) ) )),
% 0.44/0.61    inference('cnf.neg', [status(esa)], [t51_funct_2])).
% 0.44/0.61  thf('1', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.44/0.61  thf(zf_stmt_3, axiom,
% 0.44/0.61    (![C:$i,B:$i,A:$i]:
% 0.44/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.44/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.44/0.61  thf(zf_stmt_5, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.44/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.44/0.61  thf('2', plain,
% 0.44/0.61      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.61         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.44/0.61          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.44/0.61          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.61  thf('3', plain,
% 0.44/0.61      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.44/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.61  thf('4', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf('5', plain,
% 0.44/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.44/0.61         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.44/0.61          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.44/0.61          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.61  thf('6', plain,
% 0.44/0.61      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.44/0.61        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.61  thf('7', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.44/0.61  thf('8', plain,
% 0.44/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.61         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.44/0.61          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.61  thf('9', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.44/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.44/0.61  thf('10', plain,
% 0.44/0.61      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.44/0.61      inference('demod', [status(thm)], ['6', '9'])).
% 0.44/0.61  thf(t169_relat_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( v1_relat_1 @ A ) =>
% 0.44/0.61       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.44/0.61  thf('11', plain,
% 0.44/0.61      (![X7 : $i]:
% 0.44/0.61         (((k10_relat_1 @ X7 @ (k2_relat_1 @ X7)) = (k1_relat_1 @ X7))
% 0.44/0.61          | ~ (v1_relat_1 @ X7))),
% 0.44/0.61      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.44/0.61  thf('12', plain,
% 0.44/0.61      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ 
% 0.44/0.61         (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)) != (sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf('13', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf(redefinition_k8_relset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.44/0.61  thf('14', plain,
% 0.44/0.61      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.44/0.61          | ((k8_relset_1 @ X15 @ X16 @ X14 @ X17) = (k10_relat_1 @ X14 @ X17)))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.44/0.61  thf('15', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.61  thf('16', plain,
% 0.44/0.61      (((k10_relat_1 @ sk_C @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.44/0.61         != (sk_A))),
% 0.44/0.61      inference('demod', [status(thm)], ['12', '15'])).
% 0.44/0.61  thf('17', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf(t38_relset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.44/0.61         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.61  thf('18', plain,
% 0.44/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.61         (((k7_relset_1 @ X18 @ X19 @ X20 @ X18)
% 0.44/0.61            = (k2_relset_1 @ X18 @ X19 @ X20))
% 0.44/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.44/0.61      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.44/0.61  thf('19', plain,
% 0.44/0.61      (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.44/0.61         = (k2_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.44/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.44/0.61  thf('20', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf(redefinition_k2_relset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.44/0.61  thf('21', plain,
% 0.44/0.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.61         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.44/0.61          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.44/0.61  thf('22', plain,
% 0.44/0.61      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.44/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.44/0.61  thf('23', plain,
% 0.44/0.61      (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.44/0.61      inference('demod', [status(thm)], ['19', '22'])).
% 0.44/0.61  thf('24', plain, (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (sk_A))),
% 0.44/0.61      inference('demod', [status(thm)], ['16', '23'])).
% 0.44/0.61  thf('25', plain, ((((k1_relat_1 @ sk_C) != (sk_A)) | ~ (v1_relat_1 @ sk_C))),
% 0.44/0.61      inference('sup-', [status(thm)], ['11', '24'])).
% 0.44/0.61  thf('26', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf(cc2_relat_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( v1_relat_1 @ A ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.44/0.61  thf('27', plain,
% 0.44/0.61      (![X3 : $i, X4 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.44/0.61          | (v1_relat_1 @ X3)
% 0.44/0.61          | ~ (v1_relat_1 @ X4))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.44/0.61  thf('28', plain,
% 0.44/0.61      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.44/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.61  thf(fc6_relat_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.44/0.61  thf('29', plain,
% 0.44/0.61      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.44/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.44/0.61  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.44/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.61  thf('31', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.44/0.61      inference('demod', [status(thm)], ['25', '30'])).
% 0.44/0.61  thf('32', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.44/0.61      inference('simplify_reflect-', [status(thm)], ['10', '31'])).
% 0.44/0.61  thf('33', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.44/0.61      inference('clc', [status(thm)], ['3', '32'])).
% 0.44/0.61  thf('34', plain, (((sk_B) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['0', '33'])).
% 0.44/0.61  thf('35', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf('36', plain,
% 0.44/0.61      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.61      inference('split', [status(esa)], ['35'])).
% 0.44/0.61  thf('37', plain,
% 0.44/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('split', [status(esa)], ['35'])).
% 0.44/0.61  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf('39', plain,
% 0.44/0.61      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B))
% 0.44/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['37', '38'])).
% 0.44/0.61  thf('40', plain,
% 0.44/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.44/0.61         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.44/0.61          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.44/0.61          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.61  thf('41', plain,
% 0.44/0.61      (((~ (zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.44/0.61         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C))))
% 0.44/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.44/0.61  thf('42', plain,
% 0.44/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('split', [status(esa)], ['35'])).
% 0.44/0.61  thf('43', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf('44', plain,
% 0.44/0.61      (((m1_subset_1 @ sk_C @ 
% 0.44/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.44/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.44/0.61  thf(t113_zfmisc_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.44/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.44/0.61  thf('45', plain,
% 0.44/0.61      (![X1 : $i, X2 : $i]:
% 0.44/0.61         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.44/0.61  thf('46', plain,
% 0.44/0.61      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.44/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.44/0.61  thf('47', plain,
% 0.44/0.61      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.44/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('demod', [status(thm)], ['44', '46'])).
% 0.44/0.61  thf('48', plain,
% 0.44/0.61      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.44/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.44/0.61  thf('49', plain,
% 0.44/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.61         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.44/0.61          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.61  thf('50', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.61          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.44/0.61  thf('51', plain,
% 0.44/0.61      ((![X0 : $i]:
% 0.44/0.61          ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_C) = (k1_relat_1 @ sk_C)))
% 0.44/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['47', '50'])).
% 0.44/0.61  thf('52', plain,
% 0.44/0.61      (((~ (zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.44/0.61         | ((k1_xboole_0) = (k1_relat_1 @ sk_C))))
% 0.44/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('demod', [status(thm)], ['41', '51'])).
% 0.44/0.61  thf('53', plain,
% 0.44/0.61      (![X7 : $i]:
% 0.44/0.61         (((k10_relat_1 @ X7 @ (k2_relat_1 @ X7)) = (k1_relat_1 @ X7))
% 0.44/0.61          | ~ (v1_relat_1 @ X7))),
% 0.44/0.61      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.44/0.61  thf('54', plain,
% 0.44/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('split', [status(esa)], ['35'])).
% 0.44/0.61  thf('55', plain,
% 0.44/0.61      (((k10_relat_1 @ sk_C @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.44/0.61         != (sk_A))),
% 0.44/0.61      inference('demod', [status(thm)], ['12', '15'])).
% 0.44/0.61  thf('56', plain,
% 0.44/0.61      ((((k10_relat_1 @ sk_C @ (k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_A))
% 0.44/0.61          != (sk_A)))
% 0.44/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.44/0.61  thf('57', plain,
% 0.44/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('split', [status(esa)], ['35'])).
% 0.44/0.61  thf('58', plain,
% 0.44/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('split', [status(esa)], ['35'])).
% 0.44/0.61  thf('59', plain,
% 0.44/0.61      ((((k10_relat_1 @ sk_C @ 
% 0.44/0.61          (k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0))
% 0.44/0.61          != (k1_xboole_0)))
% 0.44/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.44/0.61  thf('60', plain,
% 0.44/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('split', [status(esa)], ['35'])).
% 0.44/0.61  thf('61', plain,
% 0.44/0.61      (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.44/0.61      inference('demod', [status(thm)], ['19', '22'])).
% 0.44/0.61  thf('62', plain,
% 0.44/0.61      ((((k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_A) = (k2_relat_1 @ sk_C)))
% 0.44/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['60', '61'])).
% 0.44/0.61  thf('63', plain,
% 0.44/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('split', [status(esa)], ['35'])).
% 0.44/0.61  thf('64', plain,
% 0.44/0.61      ((((k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0)
% 0.44/0.61          = (k2_relat_1 @ sk_C)))
% 0.44/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('demod', [status(thm)], ['62', '63'])).
% 0.44/0.61  thf('65', plain,
% 0.44/0.61      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_xboole_0)))
% 0.44/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('demod', [status(thm)], ['59', '64'])).
% 0.44/0.61  thf('66', plain,
% 0.44/0.61      (((((k1_relat_1 @ sk_C) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C)))
% 0.44/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['53', '65'])).
% 0.44/0.61  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.44/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.61  thf('68', plain,
% 0.44/0.61      ((((k1_relat_1 @ sk_C) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('demod', [status(thm)], ['66', '67'])).
% 0.44/0.61  thf('69', plain,
% 0.44/0.61      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0))
% 0.44/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('simplify_reflect-', [status(thm)], ['52', '68'])).
% 0.44/0.61  thf('70', plain,
% 0.44/0.61      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.44/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('demod', [status(thm)], ['44', '46'])).
% 0.44/0.61  thf('71', plain,
% 0.44/0.61      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.44/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.44/0.61  thf('72', plain,
% 0.44/0.61      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.61         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.44/0.61          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.44/0.61          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.61  thf('73', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.61          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.44/0.61          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['71', '72'])).
% 0.44/0.61  thf('74', plain,
% 0.44/0.61      (![X21 : $i, X22 : $i]:
% 0.44/0.61         ((zip_tseitin_0 @ X21 @ X22) | ((X22) != (k1_xboole_0)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('75', plain, (![X21 : $i]: (zip_tseitin_0 @ X21 @ k1_xboole_0)),
% 0.44/0.61      inference('simplify', [status(thm)], ['74'])).
% 0.44/0.61  thf('76', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.61          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['73', '75'])).
% 0.44/0.61  thf('77', plain,
% 0.44/0.61      ((![X0 : $i]: (zip_tseitin_1 @ sk_C @ X0 @ k1_xboole_0))
% 0.44/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['70', '76'])).
% 0.44/0.61  thf('78', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.44/0.61      inference('demod', [status(thm)], ['69', '77'])).
% 0.44/0.61  thf('79', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.44/0.61      inference('split', [status(esa)], ['35'])).
% 0.44/0.61  thf('80', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.44/0.61      inference('sat_resolution*', [status(thm)], ['78', '79'])).
% 0.44/0.61  thf('81', plain, (((sk_B) != (k1_xboole_0))),
% 0.44/0.61      inference('simpl_trail', [status(thm)], ['36', '80'])).
% 0.44/0.61  thf('82', plain, ($false),
% 0.44/0.61      inference('simplify_reflect-', [status(thm)], ['34', '81'])).
% 0.44/0.61  
% 0.44/0.61  % SZS output end Refutation
% 0.44/0.61  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
