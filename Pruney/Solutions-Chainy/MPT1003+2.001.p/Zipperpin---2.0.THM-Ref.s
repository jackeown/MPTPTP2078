%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9S5BDllthM

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:02 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 406 expanded)
%              Number of leaves         :   37 ( 135 expanded)
%              Depth                    :   14
%              Number of atoms          : 1002 (5241 expanded)
%              Number of equality atoms :  118 ( 510 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k7_relset_1 @ X15 @ X16 @ X14 @ X17 )
        = ( k9_relat_1 @ X14 @ X17 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( X3
        = ( k7_relat_1 @ X3 @ X4 ) )
      | ~ ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k2_relat_1 @ sk_C ) )
 != sk_A ),
    inference(demod,[status(thm)],['12','15','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k8_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k10_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k2_relat_1 @ X2 ) )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('40',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('41',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('42',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('44',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(demod,[status(thm)],['29','32','44'])).

thf('46',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','45'])).

thf('47',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','46'])).

thf('48',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('51',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('59',plain,
    ( ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X22: $i] :
      ( zip_tseitin_0 @ X22 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('64',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('65',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','62','65'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('68',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('69',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
     != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('71',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('73',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0 ) )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('75',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k7_relset_1 @ X15 @ X16 @ X14 @ X17 )
        = ( k9_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ X0 )
        = ( k9_relat_1 @ sk_C @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('78',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('79',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3
        = ( k7_relat_1 @ X3 @ X4 ) )
      | ~ ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('81',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( sk_C
        = ( k7_relat_1 @ sk_C @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('83',plain,
    ( ( sk_C
      = ( k7_relat_1 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('85',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76','85'])).

thf('87',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('88',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k8_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k10_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ X0 )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('91',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','89','90'])).

thf('92',plain,(
    sk_A != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['66','91'])).

thf('93',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('94',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['49','94'])).

thf('96',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9S5BDllthM
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.39/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.60  % Solved by: fo/fo7.sh
% 0.39/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.60  % done 153 iterations in 0.151s
% 0.39/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.60  % SZS output start Refutation
% 0.39/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.60  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.60  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.39/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.60  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.60  thf(d1_funct_2, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.60  thf(zf_stmt_0, axiom,
% 0.39/0.60    (![B:$i,A:$i]:
% 0.39/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.60  thf('0', plain,
% 0.39/0.60      (![X22 : $i, X23 : $i]:
% 0.39/0.60         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(t51_funct_2, conjecture,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.60         ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 0.39/0.60           ( A ) ) ) ))).
% 0.39/0.60  thf(zf_stmt_1, negated_conjecture,
% 0.39/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.60        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.60            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.60          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.60            ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 0.39/0.60              ( A ) ) ) ) )),
% 0.39/0.60    inference('cnf.neg', [status(esa)], [t51_funct_2])).
% 0.39/0.60  thf('1', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.60  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.60  thf(zf_stmt_3, axiom,
% 0.39/0.60    (![C:$i,B:$i,A:$i]:
% 0.39/0.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.60  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.60  thf(zf_stmt_5, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.60  thf('2', plain,
% 0.39/0.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.39/0.60         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.39/0.60          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.39/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.60  thf('3', plain,
% 0.39/0.60      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.39/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.60  thf('4', plain,
% 0.39/0.60      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.39/0.60      inference('sup-', [status(thm)], ['0', '3'])).
% 0.39/0.60  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.60  thf('6', plain,
% 0.39/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.39/0.60         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.39/0.60          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.39/0.60          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.60  thf('7', plain,
% 0.39/0.60      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.39/0.60        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.60  thf('8', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.60  thf('9', plain,
% 0.39/0.60      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.60         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.39/0.60          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.60  thf('10', plain,
% 0.39/0.60      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.39/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.60  thf('11', plain,
% 0.39/0.60      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.39/0.60      inference('demod', [status(thm)], ['7', '10'])).
% 0.39/0.60  thf('12', plain,
% 0.39/0.60      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ 
% 0.39/0.60         (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)) != (sk_A))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.60  thf('13', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.60  thf(redefinition_k7_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.39/0.60  thf('14', plain,
% 0.39/0.60      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.39/0.60          | ((k7_relset_1 @ X15 @ X16 @ X14 @ X17) = (k9_relat_1 @ X14 @ X17)))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.39/0.60  thf('15', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.60  thf('16', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.60  thf(cc2_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.60  thf('17', plain,
% 0.39/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.60         ((v4_relat_1 @ X8 @ X9)
% 0.39/0.60          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.60  thf('18', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.39/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.60  thf(t209_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.39/0.60       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.39/0.60  thf('19', plain,
% 0.39/0.60      (![X3 : $i, X4 : $i]:
% 0.39/0.60         (((X3) = (k7_relat_1 @ X3 @ X4))
% 0.39/0.60          | ~ (v4_relat_1 @ X3 @ X4)
% 0.39/0.60          | ~ (v1_relat_1 @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.39/0.60  thf('20', plain,
% 0.39/0.60      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.60  thf('21', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.60  thf(cc1_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( v1_relat_1 @ C ) ))).
% 0.39/0.60  thf('22', plain,
% 0.39/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.60         ((v1_relat_1 @ X5)
% 0.39/0.60          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.60  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.60  thf('24', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.39/0.60      inference('demod', [status(thm)], ['20', '23'])).
% 0.39/0.60  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.60  thf(t148_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ B ) =>
% 0.39/0.60       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.39/0.60  thf('26', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (((k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) = (k9_relat_1 @ X0 @ X1))
% 0.39/0.60          | ~ (v1_relat_1 @ X0))),
% 0.39/0.60      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.39/0.60  thf('27', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)) = (k9_relat_1 @ sk_C @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.60  thf('28', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.39/0.60      inference('sup+', [status(thm)], ['24', '27'])).
% 0.39/0.60  thf('29', plain,
% 0.39/0.60      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ (k2_relat_1 @ sk_C)) != (sk_A))),
% 0.39/0.60      inference('demod', [status(thm)], ['12', '15', '28'])).
% 0.39/0.60  thf('30', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.60  thf(redefinition_k8_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.39/0.60  thf('31', plain,
% 0.39/0.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.39/0.60          | ((k8_relset_1 @ X19 @ X20 @ X18 @ X21) = (k10_relat_1 @ X18 @ X21)))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.39/0.60  thf('32', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.60  thf('33', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.39/0.60      inference('demod', [status(thm)], ['20', '23'])).
% 0.39/0.60  thf('34', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (((k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) = (k9_relat_1 @ X0 @ X1))
% 0.39/0.60          | ~ (v1_relat_1 @ X0))),
% 0.39/0.60      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.39/0.60  thf(t169_relat_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ A ) =>
% 0.39/0.60       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.39/0.60  thf('35', plain,
% 0.39/0.60      (![X2 : $i]:
% 0.39/0.60         (((k10_relat_1 @ X2 @ (k2_relat_1 @ X2)) = (k1_relat_1 @ X2))
% 0.39/0.60          | ~ (v1_relat_1 @ X2))),
% 0.39/0.60      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.39/0.60  thf('36', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.39/0.60            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.39/0.60          | ~ (v1_relat_1 @ X1)
% 0.39/0.60          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['34', '35'])).
% 0.39/0.60  thf('37', plain,
% 0.39/0.60      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.60        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.39/0.60            (k9_relat_1 @ sk_C @ sk_A))
% 0.39/0.60            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['33', '36'])).
% 0.39/0.60  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.60  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.60  thf('40', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.39/0.60      inference('demod', [status(thm)], ['20', '23'])).
% 0.39/0.60  thf('41', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.39/0.60      inference('demod', [status(thm)], ['20', '23'])).
% 0.39/0.60  thf('42', plain,
% 0.39/0.60      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.39/0.60      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.39/0.60  thf('43', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.39/0.60      inference('sup+', [status(thm)], ['24', '27'])).
% 0.39/0.60  thf('44', plain,
% 0.39/0.60      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.39/0.60      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.60  thf('45', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.39/0.60      inference('demod', [status(thm)], ['29', '32', '44'])).
% 0.39/0.60  thf('46', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['11', '45'])).
% 0.39/0.60  thf('47', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['4', '46'])).
% 0.39/0.60  thf('48', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.60  thf('49', plain,
% 0.39/0.60      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.39/0.60      inference('split', [status(esa)], ['48'])).
% 0.39/0.60  thf('50', plain,
% 0.39/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('split', [status(esa)], ['48'])).
% 0.39/0.60  thf('51', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.60  thf('52', plain,
% 0.39/0.60      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['50', '51'])).
% 0.39/0.60  thf('53', plain,
% 0.39/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.39/0.60         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.39/0.60          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.39/0.60          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.60  thf('54', plain,
% 0.39/0.60      (((~ (zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.39/0.60         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C))))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['52', '53'])).
% 0.39/0.60  thf('55', plain,
% 0.39/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('split', [status(esa)], ['48'])).
% 0.39/0.60  thf('56', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.60  thf('57', plain,
% 0.39/0.60      (((m1_subset_1 @ sk_C @ 
% 0.39/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['55', '56'])).
% 0.39/0.60  thf('58', plain,
% 0.39/0.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.39/0.60         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.39/0.60          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.39/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.60  thf('59', plain,
% 0.39/0.60      ((((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.39/0.60         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['57', '58'])).
% 0.39/0.60  thf('60', plain,
% 0.39/0.60      (![X22 : $i, X23 : $i]:
% 0.39/0.60         ((zip_tseitin_0 @ X22 @ X23) | ((X23) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('61', plain, (![X22 : $i]: (zip_tseitin_0 @ X22 @ k1_xboole_0)),
% 0.39/0.60      inference('simplify', [status(thm)], ['60'])).
% 0.39/0.60  thf('62', plain,
% 0.39/0.60      (((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('demod', [status(thm)], ['59', '61'])).
% 0.39/0.60  thf('63', plain,
% 0.39/0.60      (((m1_subset_1 @ sk_C @ 
% 0.39/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['55', '56'])).
% 0.39/0.60  thf('64', plain,
% 0.39/0.60      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.60         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.39/0.60          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.60  thf('65', plain,
% 0.39/0.60      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C) = (k1_relat_1 @ sk_C)))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['63', '64'])).
% 0.39/0.60  thf('66', plain,
% 0.39/0.60      ((((k1_xboole_0) = (k1_relat_1 @ sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('demod', [status(thm)], ['54', '62', '65'])).
% 0.39/0.60  thf('67', plain,
% 0.39/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('split', [status(esa)], ['48'])).
% 0.39/0.60  thf('68', plain,
% 0.39/0.60      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ 
% 0.39/0.60         (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)) != (sk_A))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.60  thf('69', plain,
% 0.39/0.60      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ 
% 0.39/0.60          (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)) != (sk_A)))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['67', '68'])).
% 0.39/0.60  thf('70', plain,
% 0.39/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('split', [status(esa)], ['48'])).
% 0.39/0.60  thf('71', plain,
% 0.39/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('split', [status(esa)], ['48'])).
% 0.39/0.60  thf('72', plain,
% 0.39/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('split', [status(esa)], ['48'])).
% 0.39/0.60  thf('73', plain,
% 0.39/0.60      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ 
% 0.39/0.60          (k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0))
% 0.39/0.60          != (k1_xboole_0)))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.39/0.60  thf('74', plain,
% 0.39/0.60      (((m1_subset_1 @ sk_C @ 
% 0.39/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['55', '56'])).
% 0.39/0.60  thf('75', plain,
% 0.39/0.60      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.39/0.60          | ((k7_relset_1 @ X15 @ X16 @ X14 @ X17) = (k9_relat_1 @ X14 @ X17)))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.39/0.60  thf('76', plain,
% 0.39/0.60      ((![X0 : $i]:
% 0.39/0.60          ((k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ X0)
% 0.39/0.60            = (k9_relat_1 @ sk_C @ X0)))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['74', '75'])).
% 0.39/0.60  thf('77', plain,
% 0.39/0.60      (((m1_subset_1 @ sk_C @ 
% 0.39/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['55', '56'])).
% 0.39/0.60  thf('78', plain,
% 0.39/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.60         ((v4_relat_1 @ X8 @ X9)
% 0.39/0.60          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.60  thf('79', plain,
% 0.39/0.60      (((v4_relat_1 @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['77', '78'])).
% 0.39/0.60  thf('80', plain,
% 0.39/0.60      (![X3 : $i, X4 : $i]:
% 0.39/0.60         (((X3) = (k7_relat_1 @ X3 @ X4))
% 0.39/0.60          | ~ (v4_relat_1 @ X3 @ X4)
% 0.39/0.60          | ~ (v1_relat_1 @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.39/0.60  thf('81', plain,
% 0.39/0.60      (((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ k1_xboole_0))))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['79', '80'])).
% 0.39/0.60  thf('82', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.60  thf('83', plain,
% 0.39/0.60      ((((sk_C) = (k7_relat_1 @ sk_C @ k1_xboole_0)))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('demod', [status(thm)], ['81', '82'])).
% 0.39/0.60  thf('84', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)) = (k9_relat_1 @ sk_C @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.60  thf('85', plain,
% 0.39/0.60      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ k1_xboole_0)))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['83', '84'])).
% 0.39/0.60  thf('86', plain,
% 0.39/0.60      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ (k2_relat_1 @ sk_C))
% 0.39/0.60          != (k1_xboole_0)))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('demod', [status(thm)], ['73', '76', '85'])).
% 0.39/0.60  thf('87', plain,
% 0.39/0.60      (((m1_subset_1 @ sk_C @ 
% 0.39/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['55', '56'])).
% 0.39/0.60  thf('88', plain,
% 0.39/0.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.39/0.60          | ((k8_relset_1 @ X19 @ X20 @ X18 @ X21) = (k10_relat_1 @ X18 @ X21)))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.39/0.60  thf('89', plain,
% 0.39/0.60      ((![X0 : $i]:
% 0.39/0.60          ((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ X0)
% 0.39/0.60            = (k10_relat_1 @ sk_C @ X0)))
% 0.39/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['87', '88'])).
% 0.39/0.60  thf('90', plain,
% 0.39/0.60      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.39/0.60      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.60  thf('91', plain,
% 0.39/0.60      ((((k1_relat_1 @ sk_C) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.60      inference('demod', [status(thm)], ['86', '89', '90'])).
% 0.39/0.60  thf('92', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['66', '91'])).
% 0.39/0.60  thf('93', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.39/0.60      inference('split', [status(esa)], ['48'])).
% 0.39/0.60  thf('94', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.39/0.60      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 0.39/0.60  thf('95', plain, (((sk_B) != (k1_xboole_0))),
% 0.39/0.60      inference('simpl_trail', [status(thm)], ['49', '94'])).
% 0.39/0.60  thf('96', plain, ($false),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['47', '95'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
